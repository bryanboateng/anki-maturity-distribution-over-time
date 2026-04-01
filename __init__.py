import json
import math  # Adicionado para math.floor
import re
import time
import traceback

from anki import stats
from anki.hooks import wrap
from anki.utils import ids2str, pointVersion
from aqt import mw
from aqt.deckbrowser import DeckBrowser, DeckBrowserContent
from aqt.gui_hooks import deck_browser_will_render_content, overview_will_render_content
from aqt.overview import Overview, OverviewContent

from .translations import tr  # Adicionado para tradução

# Card State Categories & Colors
CAT_LEARNING = 0
CAT_YOUNG = 1
CAT_MATURE = 2
CAT_RETAINED = 3

COLOR_LEARNING = stats.colLearn
COLOR_YOUNG = stats.colYoung
COLOR_MATURE = stats.colMature
COLOR_RETAINED = "#004080"  # Dark blue, adjust as needed

# Interval thresholds (in days)
INTERVAL_LEARNING_MAX = 7
INTERVAL_YOUNG_MAX = 21
INTERVAL_MATURE_MAX = 84

TARGET_METHOD_NAME = "cardGraph"
BACKUP_ATTR_NAME = (
    "_cardGraph_original_by_evolution_addon"  # Manter nome do backup para consistência
)


def get_card_category(revlog_type, last_interval_days):
    if revlog_type in (0, 2, 3):  # Learn, Relearn, Cram
        return CAT_LEARNING
    if revlog_type == 1:  # Review
        if last_interval_days <= INTERVAL_LEARNING_MAX:
            return CAT_LEARNING
        elif last_interval_days <= INTERVAL_YOUNG_MAX:
            return CAT_YOUNG
        elif last_interval_days <= INTERVAL_MATURE_MAX:
            return CAT_MATURE
        else:
            return CAT_RETAINED
    return CAT_LEARNING  # Default


def fsrs_retrievability(elapsed_days, stability):
    """
    Calcula a retrievability.
    Para este gráfico, usamos a fórmula do FSRS-4.5 que é mais robusta
    quando a estabilidade (S) é apenas uma aproximação (usando o ivl).
    A fórmula do FSRS-6 é muito sensível e produz valores irrealistas sem a S real.
    """
    if stability <= 0:
        return 0.0

    # Fórmula FSRS-4.5: R(t) = (1 + t / (9 * S)) ^ -1
    return math.pow(1.0 + elapsed_days / (9.0 * stability), -1.0)


def get_card_evolution_data(self_instance, graph_id="evolutionGraph"):
    period_days = self_instance._periodDays()

    try:
        day_cutoff_s = self_instance.col.sched.day_cutoff
    except AttributeError:
        day_cutoff_s = self_instance.col.sched.dayCutoff

    # Verificar se é tela principal (CompleteCollectionStats) e aplicar configuração
    is_main_screen = hasattr(
        self_instance, "_deck_id"
    )  # Nossa classe customizada tem este atributo

    # Para tela de estatísticas, usar o chunk sugerido pelo Anki
    # Para tela principal, usar configuração do addon
    if is_main_screen:
        # Lógica para tela principal (mantém a configuração do addon)
        config = mw.addonManager.getConfig(__name__)
        aggregation_config = config.get("main_screen_aggregation")

        if aggregation_config == "d":
            aggregation_chunk_days = 1
        else:  # 'w' ou default
            aggregation_chunk_days = 7
    else:
        # Para tela de estatísticas, usar o chunk sugerido pelo Anki
        try:
            raw_chunk_from_anki = self_instance.get_start_end_chunk()
            if raw_chunk_from_anki and len(raw_chunk_from_anki) > 2:
                aggregation_chunk_days = raw_chunk_from_anki[2]
            else:
                # Fallback baseado no tipo se get_start_end_chunk falhar
                stats_type_from_instance = getattr(self_instance, "type", 3)
                if stats_type_from_instance == 0:  # 1 Mês
                    aggregation_chunk_days = 1
                elif stats_type_from_instance == 1:  # 3 Meses
                    aggregation_chunk_days = 7
                elif stats_type_from_instance == 2:  # 1 Ano
                    aggregation_chunk_days = 30
                else:  # Deck Life (All)
                    aggregation_chunk_days = 30
        except (IndexError, AttributeError, TypeError):
            # Fallback se qualquer erro ocorrer
            stats_type_from_instance = getattr(self_instance, "type", 3)
            if stats_type_from_instance == 0:
                aggregation_chunk_days = 1
            elif stats_type_from_instance == 1:
                aggregation_chunk_days = 7
            else:
                aggregation_chunk_days = 30

    unit_suffix = "d"
    if aggregation_chunk_days == 7:
        unit_suffix = "w"
    elif aggregation_chunk_days >= 28:  # Inclui 30 e outros próximos para "mês"
        unit_suffix = "m"

    end_date_timestamp_ms = day_cutoff_s * 1000
    graph_start_day_idx = 0

    revlog_deck_tag_filter_sql = self_instance._revlogLimit()

    if period_days is not None and period_days > 0:
        graph_start_day_idx = -(period_days - 1)
    else:  # Deck life ou period_days é 0 ou None
        first_rev_query_conditions = []
        if revlog_deck_tag_filter_sql:
            first_rev_query_conditions.append(revlog_deck_tag_filter_sql)
        first_rev_query = "SELECT MIN(id) FROM revlog"
        if first_rev_query_conditions:
            first_rev_query += " WHERE " + " AND ".join(first_rev_query_conditions)
        min_revlog_id_ms = self_instance.col.db.scalar(first_rev_query)
        if not min_revlog_id_ms:  # Se não há revisões, retorna dados vazios
            return [], {}, "", aggregation_chunk_days
        days_ago = (day_cutoff_s - (min_revlog_id_ms / 1000)) // 86400
        graph_start_day_idx = -int(days_ago)

    main_revlog_query_conditions = ["id < " + str(end_date_timestamp_ms)]
    if revlog_deck_tag_filter_sql:
        main_revlog_query_conditions.append(revlog_deck_tag_filter_sql)

    config = mw.addonManager.getConfig(__name__)
    exclude_deleted = config.get(
        "exclude_deleted_cards"
    )  # Padrão True se não encontrado
    exclude_suspended = config.get(
        "exclude_suspended_cards"
    )  # Padrão False se não encontrado

    if exclude_deleted:
        main_revlog_query_conditions.append("cid IN (SELECT id FROM cards)")

    if exclude_suspended:
        main_revlog_query_conditions.append(
            "cid IN (SELECT id FROM cards WHERE queue != -1)"
        )

    main_revlog_query_conditions.append("type != 5")

    query = (
        """
        SELECT id, cid, type, ivl
        FROM revlog
        WHERE """
        + " AND ".join(main_revlog_query_conditions)
        + """
        ORDER BY id ASC
    """
    )
    all_reviews = self_instance.col.db.all(query)

    if not all_reviews:
        return [], {}, "", aggregation_chunk_days

    card_current_states = {}
    daily_graph_data_points = {}
    daily_etk_points = {}
    daily_etk_percent_points = {}

    current_rev_idx = 0
    for day_offset in range(graph_start_day_idx, 1):  # Itera dia a dia
        current_day_end_ts_ms = (day_cutoff_s + (day_offset * 86400)) * 1000
        if day_offset == 0:  # Hoje
            current_day_end_ts_ms = end_date_timestamp_ms

        processed_reviews_on_this_day_iteration = False
        while current_rev_idx < len(all_reviews):
            rev_id_ms, cid, rev_type, rev_ivl = all_reviews[current_rev_idx]
            if rev_id_ms < current_day_end_ts_ms:
                cat = get_card_category(rev_type, rev_ivl)
                card_current_states[cid] = {
                    "category": cat,
                    "ivl": rev_ivl,
                    "last_rev_time": rev_id_ms,
                }
                current_rev_idx += 1
                processed_reviews_on_this_day_iteration = True
            else:
                break

        daily_graph_data_points[day_offset] = {
            CAT_LEARNING: 0,
            CAT_YOUNG: 0,
            CAT_MATURE: 0,
            CAT_RETAINED: 0,
        }

        # Laço unificado para cálculo
        total_retrievability_for_day = 0
        active_cards_for_etk = 0
        day_counts_recalc = {
            CAT_LEARNING: 0,
            CAT_YOUNG: 0,
            CAT_MATURE: 0,
            CAT_RETAINED: 0,
        }

        for cid, state in card_current_states.items():
            if state["last_rev_time"] < current_day_end_ts_ms:
                active_cards_for_etk += 1
                day_counts_recalc[state["category"]] += 1

                last_rev_day_s = state["last_rev_time"] / 1000
                last_rev_day_idx = int((last_rev_day_s - day_cutoff_s) / 86400)

                days_since_review = day_offset - last_rev_day_idx
                if days_since_review < 0:
                    continue

                stability = max(
                    state["ivl"], 0.1
                )  # Usar ivl como aproximação de estabilidade, evitar divisão por zero

                # Fórmula de Retrievability FSRS
                retrievability = fsrs_retrievability(days_since_review, stability)
                total_retrievability_for_day += retrievability

        day_counts = day_counts_recalc

        daily_etk_points[day_offset] = total_retrievability_for_day
        if active_cards_for_etk > 0:
            daily_etk_percent_points[day_offset] = (
                total_retrievability_for_day / active_cards_for_etk
            ) * 100
        else:
            daily_etk_percent_points[day_offset] = 0

        if (
            day_offset > graph_start_day_idx
            and not processed_reviews_on_this_day_iteration
        ):
            if (day_offset - 1) in daily_graph_data_points:
                daily_graph_data_points[day_offset] = daily_graph_data_points[
                    day_offset - 1
                ].copy()
        else:
            daily_graph_data_points[day_offset] = day_counts

    # Certificar que o dia 0 (hoje) tem os dados corretos finais
    final_day_counts = {CAT_LEARNING: 0, CAT_YOUNG: 0, CAT_MATURE: 0, CAT_RETAINED: 0}
    for card_id, state in card_current_states.items():
        if state["last_rev_time"] < end_date_timestamp_ms:
            final_day_counts[state["category"]] += 1
    daily_graph_data_points[0] = final_day_counts

    # Agregar dados diários em chunks (semanas, meses)
    aggregated_flot_data = {
        CAT_LEARNING: {},
        CAT_YOUNG: {},
        CAT_MATURE: {},
        CAT_RETAINED: {},
    }
    aggregated_etk_data = {}
    aggregated_etk_percent_data = {}
    etk_percent_temp_accumulator = {}

    for day_idx in sorted(daily_graph_data_points.keys()):
        x_flot_chunk_idx = -math.floor(-day_idx / aggregation_chunk_days)

        aggregated_flot_data[CAT_LEARNING][x_flot_chunk_idx] = daily_graph_data_points[
            day_idx
        ][CAT_LEARNING]
        aggregated_flot_data[CAT_YOUNG][x_flot_chunk_idx] = daily_graph_data_points[
            day_idx
        ][CAT_YOUNG]
        aggregated_flot_data[CAT_MATURE][x_flot_chunk_idx] = daily_graph_data_points[
            day_idx
        ][CAT_MATURE]
        aggregated_flot_data[CAT_RETAINED][x_flot_chunk_idx] = daily_graph_data_points[
            day_idx
        ][CAT_RETAINED]

        aggregated_etk_data[x_flot_chunk_idx] = daily_etk_points.get(day_idx, 0)

        if x_flot_chunk_idx not in etk_percent_temp_accumulator:
            etk_percent_temp_accumulator[x_flot_chunk_idx] = []
        etk_percent_temp_accumulator[x_flot_chunk_idx].append(
            daily_etk_percent_points.get(day_idx, 0)
        )

    for chunk_idx, values in etk_percent_temp_accumulator.items():
        if values:
            aggregated_etk_percent_data[chunk_idx] = sum(values) / len(values)
        else:
            aggregated_etk_percent_data[chunk_idx] = 0

    series = []
    data_learning, data_young, data_mature, data_retained, data_etk_percent = (
        [],
        [],
        [],
        [],
        [],
    )

    all_x_flot_chunk_indices = sorted(list(set(aggregated_etk_data.keys())))

    if not all_x_flot_chunk_indices and graph_start_day_idx == 0:
        all_x_flot_chunk_indices.append(0)

    for x_chunk_idx in all_x_flot_chunk_indices:
        data_learning.append(
            [x_chunk_idx, aggregated_flot_data[CAT_LEARNING].get(x_chunk_idx, 0)]
        )
        data_young.append(
            [x_chunk_idx, aggregated_flot_data[CAT_YOUNG].get(x_chunk_idx, 0)]
        )
        data_mature.append(
            [x_chunk_idx, aggregated_flot_data[CAT_MATURE].get(x_chunk_idx, 0)]
        )
        data_retained.append(
            [x_chunk_idx, aggregated_flot_data[CAT_RETAINED].get(x_chunk_idx, 0)]
        )
        data_etk_percent.append(
            [x_chunk_idx, aggregated_etk_percent_data.get(x_chunk_idx, 0)]
        )

    config = mw.addonManager.getConfig(__name__)

    if not config.get("hide_retained"):
        series.append(
            {
                "data": data_retained,
                "label": tr("label_retained"),
                "color": COLOR_RETAINED,
                "bars": {"order": 1},
            }
        )
    if not config.get("hide_mature"):
        series.append(
            {
                "data": data_mature,
                "label": tr("label_mature"),
                "color": COLOR_MATURE,
                "bars": {"order": 2},
            }
        )
    if not config.get("hide_young"):
        series.append(
            {
                "data": data_young,
                "label": tr("label_young"),
                "color": COLOR_YOUNG,
                "bars": {"order": 3},
            }
        )
    if not config.get("hide_learning"):
        series.append(
            {
                "data": data_learning,
                "label": tr("label_learning"),
                "color": COLOR_LEARNING,
                "bars": {"order": 4},
            }
        )

    series.append(
        {
            "data": data_etk_percent,
            "label": tr("label_avg_retention_percent"),
            "color": "#FF6B35",
            "lines": {"show": True, "lineWidth": 2, "fill": False},
            "bars": {"show": False},
            "stack": False,
            "yaxis": 2,
        }
    )

    min_x_val_for_axis = 0
    max_x_val_for_axis = 0
    if all_x_flot_chunk_indices:
        min_x_val_for_axis = all_x_flot_chunk_indices[0]
        max_x_val_for_axis = all_x_flot_chunk_indices[-1]
        if max_x_val_for_axis < 0:
            max_x_val_for_axis = 0
        elif not (0 in all_x_flot_chunk_indices):
            max_x_val_for_axis = 0

    xaxis_min = min_x_val_for_axis - 0.5
    xaxis_max = max_x_val_for_axis + 0.5

    tr_today = tr("label_today")
    use_absolute_dates = config.get("use_absolute_dates")

    month_translations = []
    for i in range(1, 13):
        month_key = [
            "month_jan",
            "month_feb",
            "month_mar",
            "month_apr",
            "month_may",
            "month_jun",
            "month_jul",
            "month_aug",
            "month_sep",
            "month_oct",
            "month_nov",
            "month_dec",
        ][i - 1]
        month_translations.append(tr(month_key))

    months_js_array = '["' + '", "'.join(month_translations) + '"]'

    if use_absolute_dates:
        tick_formatter_js = f"""
function(val, axis) {{
    if (Math.abs(val - 0) < 0.0001) {{ return '{tr_today}'; }}
    var date = new Date(({day_cutoff_s} + (val * {aggregation_chunk_days} * 86400)) * 1000);
    var months = {months_js_array};
    return months[date.getMonth()] + ' ' + date.getDate();
}}
"""
    else:
        tick_formatter_js = f"""
function(val, axis) {{
    var suffix = '{unit_suffix}';
    if (Math.abs(val - 0) < 0.0001) {{ return '{tr_today}'; }}
    return val.toFixed(axis.options.tickDecimals === undefined ? 0 : axis.options.tickDecimals) + suffix;
}}
"""

    etk_percent_data_json = json.dumps(aggregated_etk_percent_data)
    etk_abs_data_json = json.dumps(aggregated_etk_data)

    tooltip_html = f"""
<script>
$(function() {{
    var etkAbsData = {etk_abs_data_json};
    var tooltip = $("#evolutionGraphTooltip");
    if (!tooltip.length) {{
        tooltip = $('<div id="evolutionGraphTooltip" style="position:absolute;display:none;padding:8px;background-color:#fff;border:1px solid #ddd;color:#333;border-radius:4px;box-shadow:0 2px 5px rgba(0,0,0,0.1);pointer-events:none;font-size:0.9em;z-index:100;"></div>').appendTo("body");
    }}
    $("#{graph_id}").bind("plothover", function (event, pos, item) {{
        if (item) {{
            var x_val_on_axis = item.datapoint[0];
            var totalForDay = 0;
            var etkAbsValue = "N/A";
            var etkPercentValue = "N/A";

            var plot = $(this).data("plot");
            var allSeries = plot.getData();
            var pointData = {{}};

            for(var i=0; i < allSeries.length; ++i){{
                 var currentSeries = allSeries[i];
                 if (!currentSeries.label) continue;
                for(var j=0; j < currentSeries.data.length; ++j){{
                    var d = currentSeries.data[j];
                    if(Math.abs(d[0] - x_val_on_axis) < 0.0001){{
                         if(!pointData[x_val_on_axis]) pointData[x_val_on_axis] = {{}};
                         pointData[x_val_on_axis][currentSeries.label] = d[1];
                     }}
                }}
            }}

            var today_str = '{tr_today}';
            var titleX = item.series.xaxis.tickFormatter(x_val_on_axis, item.series.xaxis);

            var content = "<b>{tr("tooltip_period")}" + titleX + "</b><br/>";
            var labelLearning = "{tr("label_learning")}";
            var labelYoung = "{tr("label_young")}";
            var labelMature = "{tr("label_mature")}";
            var labelRetained = "{tr("label_retained")}";
            var labelRetentionPercent = "{tr("label_avg_retention_percent")}";

            if(pointData[x_val_on_axis]){{
                if(pointData[x_val_on_axis][labelLearning] !== undefined) totalForDay += pointData[x_val_on_axis][labelLearning];
                if(pointData[x_val_on_axis][labelYoung] !== undefined) totalForDay += pointData[x_val_on_axis][labelYoung];
                if(pointData[x_val_on_axis][labelMature] !== undefined) totalForDay += pointData[x_val_on_axis][labelMature];
                if(pointData[x_val_on_axis][labelRetained] !== undefined) totalForDay += pointData[x_val_on_axis][labelRetained];
                
                if(pointData[x_val_on_axis][labelRetentionPercent] !== undefined) {{
                    etkPercentValue = pointData[x_val_on_axis][labelRetentionPercent].toFixed(1) + "%";
                }}
                if(etkAbsData[x_val_on_axis] !== undefined) {{
                    etkAbsValue = etkAbsData[x_val_on_axis].toFixed(0);
                }}
            }}
            
            content += labelLearning + ": " + (pointData[x_val_on_axis]?.[labelLearning]?.toFixed(0) || 0) + "<br/>";
            content += labelYoung + ": " + (pointData[x_val_on_axis]?.[labelYoung]?.toFixed(0) || 0) + "<br/>";
            content += labelMature + ": " + (pointData[x_val_on_axis]?.[labelMature]?.toFixed(0) || 0) + "<br/>";
            content += labelRetained + ": " + (pointData[x_val_on_axis]?.[labelRetained]?.toFixed(0) || 0) + "<br/>";
            content += "<i>{tr("tooltip_total")}" + totalForDay.toFixed(0) + "</i><br/><hr style='margin: 4px 0; border-top: 1px solid #ccc;'/>";
            content += "<b>" + labelRetentionPercent + ": " + etkPercentValue + "</b><br/>";
            content += "<b>{tr("label_total_knowledge")}: " + etkAbsValue + "</b>";

            tooltip.html(content).css({{top: item.pageY+5, left: item.pageX+5}}).fadeIn(200);
        }} else {{
            tooltip.hide();
        }}
    }});
}});
</script>
"""
    graph_options = {
        "xaxis": {
            "min": xaxis_min,
            "max": xaxis_max,
            "tickFormatter": tick_formatter_js,
        },
        "yaxes": [
            {"min": 0, "position": "left"},
            {
                "min": 0,
                "max": 100,
                "position": "right",
                "alignTicksWithAxis": 1,
                "show": False,
            },
        ],
        "series": {
            "stack": True,
            "bars": {
                "show": True,
                "align": "center",
                "barWidth": 0.9,
                "lineWidth": 1,
                "fill": 0.8,
            },
        },
        "grid": {"hoverable": True, "clickable": True, "borderColor": "#C0C0C0"},
        "legend": {
            "show": True,
            "position": "nw",
            "backgroundColor": "#ffffff",
            "backgroundOpacity": 0,
        },
    }
    return series, graph_options, tooltip_html, aggregation_chunk_days


def render_card_evolution_graph(self_instance):
    graph_id = "evolutionGraph" + str(time.time()).replace(".", "")
    title = tr("graph_title")
    subtitle = tr("graph_subtitle")
    series_data, options, tooltip_html, aggregation_chunk_days = (
        get_card_evolution_data(self_instance, graph_id)
    )

    # Remover prints de depuração
    if not series_data or not any(s["data"] for s in series_data):
        return (
            "<div style='text-align:center;margin-top:1em;'>"
            + tr("graph_no_data")
            + "</div>"
        )

    # Usar o método _title da instância para um estilo de título padrão do Anki.
    # O método _title geralmente lida com a tradução se as strings forem chaves de tradução.
    # Nossas strings title e subtitle são literais em português.
    html = self_instance._title(title, subtitle)

    # A lógica de renderização agora depende do tipo de instância de estatísticas
    if isinstance(self_instance, CompleteCollectionStats):
        # Para a tela principal, passamos o tooltip_html para ser integrado pelo método _graph customizado
        html += self_instance._graph(
            id=graph_id,
            data=series_data,
            conf=options,
            ylabel=tr("graph_y_label"),
            y2label=tr("graph_y_label_percent"),
            tooltip_html=tooltip_html,
        )
    else:
        # Para a tela de estatísticas padrão, usamos o método original do Anki (sem y2label)
        html += self_instance._graph(
            id=graph_id,
            data=series_data,
            conf=options,
            xunit=aggregation_chunk_days,
            ylabel=tr("graph_y_label"),
        )
        html += tooltip_html

    return html


def add_evolution_graph_to_card_stats(self_instance, *original_args, **original_kwargs):
    """
    Wraps the original cardGraph method to append the evolution graph.
    This version assumes the wrapper is called with only (self, *args, **kwargs) by the hook system,
    and the original method is retrieved from our backup.

    `self_instance` is the CollectionStats instance.
    `original_args` and `original_kwargs` are arguments for the original method (likely none for cardGraph).
    """
    original_card_graph_html = ""

    original_method_ref = getattr(stats.CollectionStats, BACKUP_ATTR_NAME, None)

    if original_method_ref:
        # Clean up kwargs for the original cardGraph call
        # cardGraph() typically only takes self.
        # Another addon seems to be injecting '_old' into the kwargs.
        cleaned_kwargs = original_kwargs.copy()
        if "_old" in cleaned_kwargs:
            del cleaned_kwargs["_old"]

        # The original cardGraph() method does not accept *args or **kwargs beyond self.
        # So, we should call it with only self_instance if original_args and cleaned_kwargs are empty.
        # However, to be safe and pass through what was given (minus _old):
        try:
            original_card_graph_html = original_method_ref(
                self_instance, *original_args, **cleaned_kwargs
            )
        except TypeError as e:
            # This might happen if original_args is not empty or cleaned_kwargs still has unexpected items.
            try:
                original_card_graph_html = original_method_ref(self_instance)
            except Exception as e2:
                original_card_graph_html = "<!-- Original graph failed to load -->"

    else:
        original_card_graph_html = "<!-- Original graph could not be determined -->"

    evolution_graph_html = render_card_evolution_graph(self_instance)

    config = mw.addonManager.getConfig(__name__)
    show_at_beginning = config.get(
        "show_at_beginning"
    )  # False por padrão (mostrar ao final)

    if show_at_beginning:
        # Mostrar o gráfico de evolução ANTES do gráfico original
        return evolution_graph_html + original_card_graph_html
    else:
        # Mostrar o gráfico de evolução DEPOIS do gráfico original (comportamento padrão)
        return original_card_graph_html + evolution_graph_html


# ===== INÍCIO DA INTEGRAÇÃO COM TELA PRINCIPAL =====

# Imports adicionais


# Classe Helper para gerar estatísticas da tela principal.
# Movida para fora das funções de hook para evitar re-declaração.
class CompleteCollectionStats:
    def __init__(self, col, deck_id=None, period="3m"):
        self.col = col
        self._deck_id = deck_id
        self._period = period

        if period == "1m":
            self.type = 0
        elif period == "3m":
            self.type = 1
        elif period == "1y":
            self.type = 2
        else:
            # Para períodos customizados, escolhe tipo baseado na duração
            period_days = self._periodDays()
            if period_days is None:  # deck_life
                self.type = 3
            elif period_days <= 30:  # até 1 mês
                self.type = 0
            elif period_days <= 90:  # até 3 meses
                self.type = 1
            elif period_days <= 365:  # até 1 ano
                self.type = 2
            else:  # mais de 1 ano
                self.type = 3

    def _periodDays(self):
        if self._period == "1m":
            return 30
        elif self._period == "3m":
            return 90
        elif self._period == "1y":
            return 365
        elif self._period == "deck_life":
            return None
        else:
            # Tenta interpretar como Xm (X meses) ou Xy (X anos)
            match = re.match(r"^(\d+)([my])$", self._period)
            if match:
                number, unit = int(match.group(1)), match.group(2)
                if unit == "m":  # meses
                    return number * 30
                elif unit == "y":  # anos
                    return number * 365
            return None

    def _revlogLimit(self):
        if not self._deck_id:
            return ""

        try:
            child_decks = [self._deck_id]
            for name, did in self.col.decks.children(self._deck_id):
                child_decks.append(did)
            deck_ids_str = ids2str(child_decks)
            return "cid IN (SELECT id FROM cards WHERE did IN " + deck_ids_str + ")"
        except Exception as e:
            return ""

    def get_start_end_chunk(self):
        config = mw.addonManager.getConfig(__name__)
        try:
            day_cutoff_s = self.col.sched.day_cutoff
        except AttributeError:
            day_cutoff_s = int(time.time())

        aggregation_config = config.get("main_screen_aggregation")

        if aggregation_config == "d":
            chunk_days = 1
        else:
            chunk_days = 7

        # Usa _periodDays() para calcular o período em dias
        period_days = self._periodDays()

        if period_days is not None:
            return (day_cutoff_s - (period_days * 86400), day_cutoff_s, chunk_days)
        else:  # deck_life
            first_rev_query = "SELECT MIN(id) FROM revlog"
            if self._deck_id:
                try:
                    child_decks = [self._deck_id]
                    for name, did in self.col.decks.children(self._deck_id):
                        child_decks.append(did)
                    deck_ids_str = ids2str(child_decks)
                    first_rev_query += (
                        " WHERE cid IN (SELECT id FROM cards WHERE did IN "
                        + deck_ids_str
                        + ")"
                    )
                except:
                    pass

            min_revlog_id_ms = self.col.db.scalar(first_rev_query)
            if min_revlog_id_ms:
                start = min_revlog_id_ms // 1000
            else:
                start = day_cutoff_s - (365 * 86400)

            return (start, day_cutoff_s, chunk_days)

    def _title(self, title, subtitle=""):
        safe_title = title.replace("%", "%%")
        safe_subtitle = subtitle.replace("%", "%%")

        html_parts = []
        html_parts.append(
            '<h3 style="text-align: center; margin-bottom: 0; color: #333;">'
        )
        html_parts.append(safe_title)
        html_parts.append("</h3>")
        if safe_subtitle:
            html_parts.append(
                '<p style="text-align: center; color: #666; margin-top: 0.2em; margin-bottom: 0.5em; font-size: 0.9em;">'
            )
            html_parts.append(safe_subtitle)
            html_parts.append("</p>")
        return "".join(html_parts)

    def _graph(self, id, data, conf, ylabel="", y2label="", tooltip_html=""):
        config = mw.addonManager.getConfig(__name__)
        height = config.get("main_screen_height")
        safe_ylabel = ylabel.replace("%", "%%")
        safe_y2label = y2label.replace("%", "%%")

        # Extrai o conteúdo JS puro do tooltip_html
        tooltip_js_content = ""
        if tooltip_html:
            match = re.search(r"<script[^>]*>(.*?)</script>", tooltip_html, re.DOTALL)
            if match:
                tooltip_js_content = match.group(1).strip()
                # Remove a função de auto-execução $(function() { ... }); para que possamos chamá-la diretamente
                tooltip_js_content = re.sub(
                    r"^\s*\$\(function\(\)\s*\{", "", tooltip_js_content
                )
                tooltip_js_content = re.sub(r"\}\s*\)\;\s*$", "", tooltip_js_content)

        try:
            if not data or not any(s.get("data") for s in data):
                return (
                    '<div style="color:#888;text-align:center;margin:1em 0;">'
                    + tr("graph_no_data")
                    + "</div>"
                )

            data_json_for_js = json.dumps(data)
            options_json_for_js = json.dumps(conf)

            py_unit_suffix = conf.get("xaxis", {}).get("unit_suffix", "d")
            py_agg_days = conf.get("xaxis", {}).get("aggregation_chunk_days", 1)
            py_today_label = tr("label_today").replace("%", "%%")

            # Get day_cutoff_s to pass to JS for absolute dates
            try:
                py_day_cutoff_s = self.col.sched.day_cutoff
            except AttributeError:
                py_day_cutoff_s = self.col.sched.dayCutoff  # For older Anki versions

            html_parts = []
            html_parts.append(
                '<div id="'
                + id
                + '" style="height:'
                + str(height)
                + 'px; width:95%; margin: 0 auto;"></div>'
            )
            html_parts.append(
                '<p style="text-align: center; font-size: 0.8em; color: #666; margin-top: 0.5em;">'
                + safe_ylabel
                + "</p>"
            )

            js_parts = []
            js_parts.append('<script type="text/javascript">')
            js_parts.append("(function() {")
            js_parts.append("  var attempts = 0;")
            js_parts.append("  var maxAttempts = 20;")
            js_parts.append("  var retryInterval = 200;")
            js_parts.append("  ")
            js_parts.append("  function checkDependencies() {")
            js_parts.append(
                '    return (typeof $ !== "undefined" && typeof $.plot !== "undefined");'
            )
            js_parts.append("  }")
            js_parts.append("  ")
            js_parts.append("  function loadFlotLibraries(callback) {")
            js_parts.append('    if (typeof $ === "undefined") {')
            js_parts.append(
                '      console.error("Card Evolution JS: jQuery not available");'
            )
            js_parts.append("      return false;")
            js_parts.append("    }")
            js_parts.append("    ")
            js_parts.append('    if (typeof $.plot === "undefined") {')
            js_parts.append('      var flotScript = document.createElement("script");')
            js_parts.append(
                '      flotScript.src = "https://cdnjs.cloudflare.com/ajax/libs/flot/0.8.3/jquery.flot.min.js";'
            )
            js_parts.append("      flotScript.onload = function() {")
            js_parts.append(
                '        var stackScript = document.createElement("script");'
            )
            js_parts.append(
                '        stackScript.src = "https://cdnjs.cloudflare.com/ajax/libs/flot/0.8.3/jquery.flot.stack.min.js";'
            )
            js_parts.append("        stackScript.onload = function() {")
            js_parts.append("          setTimeout(callback, 100);")
            js_parts.append("        };")
            js_parts.append("        stackScript.onerror = function() {")
            js_parts.append(
                '          console.error("Card Evolution JS: Failed to load Flot stack plugin");'
            )
            js_parts.append("          setTimeout(callback, 100);")
            js_parts.append("        };")
            js_parts.append("        document.head.appendChild(stackScript);")
            js_parts.append("      };")
            js_parts.append("      flotScript.onerror = function() {")
            js_parts.append(
                '        console.error("Card Evolution JS: Failed to load Flot from CDN");'
            )
            js_parts.append("        callback();")
            js_parts.append("      };")
            js_parts.append("      document.head.appendChild(flotScript);")
            js_parts.append("      return false;")
            js_parts.append("    }")
            js_parts.append("    ")
            js_parts.append("    callback();")
            js_parts.append("    return true;")
            js_parts.append("  }")
            js_parts.append("  ")
            js_parts.append("  function renderGraph() {")
            js_parts.append("    try {")
            js_parts.append('      var graphDiv = $("#' + id + '");')
            js_parts.append("      if (graphDiv.length === 0) {")
            js_parts.append("")
            js_parts.append("        return false;")
            js_parts.append("      }")
            js_parts.append("      ")
            js_parts.append("      var data = " + data_json_for_js + ";")
            js_parts.append("      var options = " + options_json_for_js + ";")
            js_parts.append("      ")
            js_parts.append(
                '      if (options.xaxis && typeof options.xaxis.tickFormatter === "string") {'
            )
            js_parts.append("        delete options.xaxis.tickFormatter;")
            js_parts.append("      }")
            js_parts.append("      ")
            js_parts.append("      if (options.series) {")
            js_parts.append("        options.series.stack = true;")
            js_parts.append("        if (options.series.bars) {")
            js_parts.append("          options.series.bars.show = true;")
            js_parts.append("        } else {")
            js_parts.append("          options.series.bars = { show: true };")
            js_parts.append("        }")
            js_parts.append("      } else {")
            js_parts.append(
                "        options.series = { stack: true, bars: { show: true } };"
            )
            js_parts.append("      }")
            js_parts.append("      ")

            use_absolute_dates = config.get("use_absolute_dates")

            # Criar array de meses traduzidos para JavaScript
            month_translations_main = []
            for i in range(1, 13):
                month_key = [
                    "month_jan",
                    "month_feb",
                    "month_mar",
                    "month_apr",
                    "month_may",
                    "month_jun",
                    "month_jul",
                    "month_aug",
                    "month_sep",
                    "month_oct",
                    "month_nov",
                    "month_dec",
                ][i - 1]
                month_translations_main.append(tr(month_key))
            months_js_array_main = '["' + '", "'.join(month_translations_main) + '"]'

            if use_absolute_dates:
                formatter_func_str = (
                    "function(val, axis) { var todayLabel = '"
                    + py_today_label
                    + "'; if (Math.abs(val - 0) < 0.001) { return todayLabel; } var aggDays = "
                    + str(py_agg_days)
                    + "; var dayCutoffS = "
                    + str(py_day_cutoff_s)
                    + "; var dayOffset = val * aggDays; var date = new Date((dayCutoffS + (dayOffset * 86400)) * 1000); var months = "
                    + months_js_array_main
                    + "; return months[date.getMonth()] + ' ' + date.getDate(); }"
                )
            else:
                formatter_func_str = (
                    "function(val, axis) { var unitSuffix = '"
                    + py_unit_suffix
                    + "'; var todayLabel = '"
                    + py_today_label
                    + "'; if (Math.abs(val - 0) < 0.001) { return todayLabel; } var decimals = axis.options.tickDecimals === undefined ? 0 : axis.options.tickDecimals; return val.toFixed(decimals) + unitSuffix; }"
                )

            js_parts.append(
                "      options.xaxis.tickFormatter = " + formatter_func_str + ";"
            )
            js_parts.append("      ")
            js_parts.append("      $.plot(graphDiv, data, options);")
            js_parts.append("      ")
            js_parts.append("      " + tooltip_js_content)
            js_parts.append("      ")
            js_parts.append("")
            js_parts.append("      return true;")
            js_parts.append("    } catch (e) {")
            js_parts.append(
                '      console.error("Card Evolution JS: Error rendering graph on attempt " + attempts + ":", e);'
            )
            js_parts.append("      return false;")
            js_parts.append("    }")
            js_parts.append("  }")
            js_parts.append("  ")
            js_parts.append("  function attemptRender() {")
            js_parts.append("    attempts++;")
            js_parts.append("    ")
            js_parts.append("    if (attempts > maxAttempts) {")
            js_parts.append(
                '      console.error("Card Evolution JS: Failed to render graph after " + maxAttempts + " attempts. Dependencies or DOM may not be ready.");'
            )
            js_parts.append("      return;")
            js_parts.append("    }")
            js_parts.append("    ")
            js_parts.append("    if (!checkDependencies()) {")
            js_parts.append("      loadFlotLibraries(function() {")
            js_parts.append("        setTimeout(attemptRender, retryInterval);")
            js_parts.append("      });")
            js_parts.append("      return;")
            js_parts.append("    }")
            js_parts.append("    ")
            js_parts.append("    if (renderGraph()) {")
            js_parts.append("      return;")
            js_parts.append("    }")
            js_parts.append("    ")
            js_parts.append("    setTimeout(attemptRender, retryInterval);")
            js_parts.append("  }")
            js_parts.append("  ")
            js_parts.append("  function initWhenReady() {")
            js_parts.append('    if (document.readyState === "loading") {')
            js_parts.append(
                '      document.addEventListener("DOMContentLoaded", function() {'
            )
            js_parts.append("        setTimeout(attemptRender, 50);")
            js_parts.append("      });")
            js_parts.append("    } else {")
            js_parts.append("      setTimeout(attemptRender, 50);")
            js_parts.append("    }")
            js_parts.append("  }")
            js_parts.append("  ")
            js_parts.append("  initWhenReady();")
            js_parts.append("})();")
            js_parts.append("</script>")

            return "".join(html_parts) + "".join(js_parts)

        except Exception as e:
            print(
                "Card Evolution Main Screen: Erro ao gerar HTML/JS do gráfico (Python): "
                + str(e)
            )
            print(
                "Card Evolution Main Screen: Traceback (Python): "
                + str(traceback.format_exc())
            )
            return (
                '<div style="color:red;text-align:center;">Erro Py ao gerar gráfico: '
                + str(e)
                + "</div>"
            )


def _render_main_screen_graph_html(deck_id=None):
    """Gera o HTML completo para o gráfico da tela principal."""
    config = mw.addonManager.getConfig(__name__)
    period = config.get("main_screen_period")
    stats_instance = CompleteCollectionStats(mw.col, deck_id=deck_id, period=period)

    graph_html = render_card_evolution_graph(stats_instance)

    # Envolve o gráfico renderizado em um contêiner pai, agora com estilo.
    return f'<div class="evolution-graph-main-wrapper" style="max-width: 900px; margin: 20px auto; padding: 1em; border: 1px solid #ddd; border-radius: 5px; background: #f9f9f9;">{graph_html}</div>'


def on_deck_browser_render(deck_browser: DeckBrowser, content: DeckBrowserContent):
    """Adiciona o gráfico de evolução do status à tela principal do navegador de baralhos."""
    config = mw.addonManager.getConfig(__name__)
    if not config.get("show_in_deck_browser"):
        return

    try:
        # Para o navegador de baralhos, não filtramos por deck_id (None)
        graph_html = _render_main_screen_graph_html(deck_id=None)
        content.stats += graph_html
    except Exception as e:
        print(f"Accumulated Retention: Failed to render graph on deck browser: {e}")


def on_overview_render(overview: Overview, content: OverviewContent):
    """Adiciona o gráfico de evolução do status à tela de visão geral do baralho."""
    config = mw.addonManager.getConfig(__name__)
    if not config.get("show_in_overview"):
        return

    try:
        # Para a visão geral, usamos o ID do baralho atual, obtido via mw.
        current_deck_id = mw.col.decks.get_current_id()
        graph_html = _render_main_screen_graph_html(deck_id=current_deck_id)

        # Injetar o gráfico, envolvendo-o em uma linha de tabela para renderização correta.
        content.table += (
            f'<tr><td colspan="2" style="padding: 10px 0;">{graph_html}</td></tr>'
        )

    except Exception as e:
        print(f"Accumulated Retention: Failed to render graph on overview: {e}")


def init_main_screen_hooks():
    """Inicializa os ganchos para a tela principal (Navegador de Baralhos)."""
    config = mw.addonManager.getConfig(__name__)
    if config.get("enable_main_screen"):
        # A verificação de show_in_overview/deck_browser é feita dentro de cada hook.
        overview_will_render_content.append(on_overview_render)
        deck_browser_will_render_content.append(on_deck_browser_render)


def main():
    # Verificação de versão do Anki
    anki_version = pointVersion()
    print(f"Accumulated Retention Graph: Anki version detected - {anki_version}")

    # Verificar se é uma versão compatível
    if anki_version >= 256000:  # Anki 25.6+
        print("Accumulated Retention Graph: Running on Anki 25.6+ (new versioning)")
    elif anki_version >= 231000:  # Anki 23.10+
        print("Accumulated Retention Graph: Running on Anki 23.10+ (new versioning)")
    elif anki_version >= 45:  # Anki 2.1.45+
        print(
            "Accumulated Retention Graph: Running on Anki 2.1.45+ (legacy versioning)"
        )
    else:
        print(
            f"Accumulated Retention Graph: Warning - Running on older Anki version {anki_version}. This addon may not work properly."
        )

    # --- Nova seção de Hooking ---

    # Tentar usar cardGraph (sem underscore)

    # Guardar uma referência ao método original, se ainda não foi guardada por este addon
    if hasattr(stats.CollectionStats, TARGET_METHOD_NAME) and not hasattr(
        stats.CollectionStats, BACKUP_ATTR_NAME
    ):
        setattr(
            stats.CollectionStats,
            BACKUP_ATTR_NAME,
            getattr(stats.CollectionStats, TARGET_METHOD_NAME),
        )
    elif not hasattr(stats.CollectionStats, TARGET_METHOD_NAME):
        pass
    # Aplicar o wrap apenas se o método original e o backup existirem
    if hasattr(stats.CollectionStats, TARGET_METHOD_NAME) and hasattr(
        stats.CollectionStats, BACKUP_ATTR_NAME
    ):
        current_target_method_func = getattr(stats.CollectionStats, TARGET_METHOD_NAME)
        original_backup_func = getattr(stats.CollectionStats, BACKUP_ATTR_NAME)

        # Desfazer o wrap se o método alvo não for já o original (ou seja, se já foi envolvido por nós)
        if current_target_method_func != original_backup_func:
            setattr(stats.CollectionStats, TARGET_METHOD_NAME, original_backup_func)

        # Aplicar o wrap
        setattr(
            stats.CollectionStats,
            TARGET_METHOD_NAME,
            wrap(
                original_backup_func,  # Envolver o original que guardamos
                add_evolution_graph_to_card_stats,
                "around",
            ),
        )
    # Inicializar hooks da tela principal
    try:
        init_main_screen_hooks()
    except Exception as e:
        print(f"Card Evolution: Erro ao inicializar hooks da tela principal: {e}")


# ===== FIM DA INTEGRAÇÃO COM TELA PRINCIPAL =====

main()
