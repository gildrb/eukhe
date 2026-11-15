//! The lines a budget reads as, shared by every surface that shows one
//! (the CLI's final line and `eukhe budget`, `/budget`, the status line).
//! The amounts a user types are read by `eukhe_types::budget_input`.
//!
//! The report line names, per limited dimension, what is used (spent,
//! held by requests in flight and lent to children) against the limit,
//! and for time what is left until the deadline:
//! `budget: $0.42/$2.00 - 31.0k/200k tok - 6m 50s left - 12/50 calls -
//! 3/30 req`, then the agent's phase when it is not working and the
//! overrun when there is one. The caller passes the separator of its
//! surface and the time now (Unix milliseconds).

use eukhe_types::budget::{
    dollars, BudgetAmounts, BudgetDimension, BudgetPhase, BudgetReport, LimitSource, LimitValue,
};
use eukhe_types::daemon::BudgetAudit;

/// A token count, cut (never rounded up): `999`, `31.0k`, `200k`, `1.5M`.
fn tokens(count: u64) -> String {
    match count {
        0..1_000 => count.to_string(),
        1_000..100_000 => format!("{}.{}k", count / 1_000, count % 1_000 / 100),
        100_000..1_000_000 => format!("{}k", count / 1_000),
        1_000_000..100_000_000 => {
            format!("{}.{}M", count / 1_000_000, count % 1_000_000 / 100_000)
        }
        100_000_000.. => format!("{}M", count / 1_000_000),
    }
}

/// Milliseconds as whole seconds in the two largest units that count:
/// `45s`, `3m 10s`, `10m`, `2h 5m`.
fn duration(ms: u64) -> String {
    let seconds = ms / 1_000;
    match (seconds / 3_600, seconds % 3_600 / 60, seconds % 60) {
        (0, 0, seconds) => format!("{seconds}s"),
        (0, minutes, 0) => format!("{minutes}m"),
        (0, minutes, seconds) => format!("{minutes}m {seconds}s"),
        (hours, 0, _) => format!("{hours}h"),
        (hours, minutes, _) => format!("{hours}h {minutes}m"),
    }
}

/// Unix milliseconds as the UTC time `YYYY-MM-DD HH:MM:SS UTC` (the civil
/// date of the days since 1970-01-01, Howard Hinnant's `civil_from_days`).
fn utc_time(epoch_ms: u64) -> String {
    let seconds = epoch_ms / 1_000;
    let (days, rest) = (seconds / 86_400, seconds % 86_400);
    let shifted = days + 719_468;
    let era = shifted / 146_097;
    let day_of_era = shifted % 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_index = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_index + 2) / 5 + 1;
    let month = if month_index < 10 {
        month_index + 3
    } else {
        month_index - 9
    };
    let year = year_of_era + era * 400 + u64::from(month <= 2);
    format!(
        "{year}-{month:02}-{day:02} {:02}:{:02}:{:02} UTC",
        rest / 3_600,
        rest % 3_600 / 60,
        rest % 60
    )
}

/// `amount` of `dimension` without its unit word.
fn amount_text(dimension: BudgetDimension, amount: u64) -> String {
    match dimension {
        BudgetDimension::Cost => dollars(amount),
        BudgetDimension::Tokens => tokens(amount),
        BudgetDimension::Time => duration(amount),
        BudgetDimension::ToolCalls | BudgetDimension::Requests => count(amount),
    }
}

/// A count with thousands separators: `3,200`.
fn count(value: u64) -> String {
    let digits = value.to_string();
    let mut grouped = String::with_capacity(digits.len() + digits.len() / 3);
    for (place, digit) in digits.chars().enumerate() {
        if place > 0 && (digits.len() - place).is_multiple_of(3) {
            grouped.push(',');
        }
        grouped.push(digit);
    }
    grouped
}

/// `amount` of `dimension` with its unit as the budget line writes it:
/// `$0.42`, `31.0k tok`, `3,200 requests`.
fn long_amount(dimension: BudgetDimension, amount: u64) -> String {
    match dimension {
        BudgetDimension::ToolCalls => format!("{} tool calls", count(amount)),
        BudgetDimension::Requests => format!("{} requests", count(amount)),
        BudgetDimension::Cost | BudgetDimension::Tokens | BudgetDimension::Time => {
            format!("{}{}", amount_text(dimension, amount), unit(dimension))
        }
    }
}

/// What a dimension without a limit is named in `no <name> limit`.
fn limit_name(dimension: BudgetDimension) -> &'static str {
    match dimension {
        BudgetDimension::Cost => "money",
        BudgetDimension::Tokens => "token",
        BudgetDimension::Time => "time",
        BudgetDimension::ToolCalls => "tool call",
        BudgetDimension::Requests => "request",
    }
}

/// The order limited dimensions are written in.
const LIMITED_ORDER: [BudgetDimension; 5] = [
    BudgetDimension::Requests,
    BudgetDimension::ToolCalls,
    BudgetDimension::Time,
    BudgetDimension::Cost,
    BudgetDimension::Tokens,
];

/// The order the spend of dimensions without a limit is written in.
const SPENT_ORDER: [BudgetDimension; 4] = [
    BudgetDimension::Cost,
    BudgetDimension::Tokens,
    BudgetDimension::Requests,
    BudgetDimension::ToolCalls,
];

/// The source a report gives `dimension`'s limit. A ledger written before
/// runs were recorded (no kind) has only the principal's limits.
fn source_of(report: &BudgetReport, dimension: BudgetDimension) -> LimitSource {
    match report.sources.get(dimension) {
        LimitSource::UntilFinished
            if report.kind.is_none() && report.limits.get(dimension).is_some() =>
        {
            LimitSource::Set
        }
        source => source.clone(),
    }
}

/// The short word of who decided a limit, as the budget and status lines
/// write it after a group: `limits on`, `set`, `/b <name>`; `None`: the
/// default (until finished).
fn source_word(source: &LimitSource) -> Option<String> {
    match source {
        LimitSource::UntilFinished => None,
        LimitSource::Set => Some("set".to_owned()),
        LimitSource::LimitsProfile | LimitSource::Profile => Some("limits on".to_owned()),
        LimitSource::Preset(name) => Some(format!("/b {name}")),
    }
}

/// The long name of who decided a limit, as `eukhe budget show --json`
/// and the session record write it.
#[must_use]
pub fn source_name(source: &LimitSource) -> String {
    match source {
        LimitSource::UntilFinished => "until finished (default)".to_owned(),
        LimitSource::Set => "set by the principal".to_owned(),
        LimitSource::LimitsProfile => "limits profile".to_owned(),
        LimitSource::Profile => "profile".to_owned(),
        LimitSource::Preset(name) => format!("/b {name}"),
    }
}

/// Each dimension's limit and the long name of its source, keyed by the
/// dimension's wire name: `{"requests": {"limit": 3200, "source":
/// "limits profile"}, "costMicros": {"limit": "unlimited", "source":
/// "until finished (default)"}}`.
#[must_use]
pub fn limits_json(report: &BudgetReport) -> serde_json::Value {
    let mut map = serde_json::Map::new();
    for dimension in BudgetDimension::ALL {
        let key = match dimension {
            BudgetDimension::Cost => "costMicros",
            BudgetDimension::Tokens => "tokens",
            BudgetDimension::Time => "timeMs",
            BudgetDimension::ToolCalls => "toolCalls",
            BudgetDimension::Requests => "requests",
        };
        let limit = report
            .limits
            .get(dimension)
            .map_or(LimitValue::Unlimited, LimitValue::At);
        map.insert(
            key.to_owned(),
            serde_json::json!({
                "limit": limit,
                "source": source_name(&source_of(report, dimension)),
            }),
        );
    }
    serde_json::Value::Object(map)
}

/// What is used of `dimension`: spent, held by requests in flight and
/// lent to children.
fn used(report: &BudgetReport, dimension: BudgetDimension) -> u64 {
    report
        .spent
        .get(dimension)
        .saturating_add(report.held.get(dimension))
        .saturating_add(report.lent.get(dimension))
}

/// A limited dimension as used against its limit (time: what is left).
fn against(report: &BudgetReport, dimension: BudgetDimension, limit: u64, now_ms: u64) -> String {
    match dimension {
        BudgetDimension::Time => format!("{} left", duration(time_left(report, now_ms))),
        BudgetDimension::Cost
        | BudgetDimension::Tokens
        | BudgetDimension::ToolCalls
        | BudgetDimension::Requests => format!(
            "{}/{}",
            amount_text(dimension, used(report, dimension)),
            long_amount(dimension, limit)
        ),
    }
}

/// `item` added to the group of `source`, a new group in order of first
/// appearance.
fn push_grouped<K: PartialEq>(groups: &mut Vec<(K, Vec<String>)>, source: K, item: String) {
    match groups.iter_mut().find(|(word, _)| *word == source) {
        Some((_, items)) => items.push(item),
        None => groups.push((source, vec![item])),
    }
}

/// The phase and overrun parts after a line's dimensions.
fn phase_parts(report: &BudgetReport, parts: &mut Vec<String>) {
    match (report.phase, report.short) {
        (BudgetPhase::Working, _) => {}
        (BudgetPhase::WrapUp, _) => parts.push("wrap-up".to_string()),
        (BudgetPhase::Exhausted, Some(short)) => {
            parts.push(format!("exhausted ({})", short.label()));
        }
        (BudgetPhase::Exhausted, None) => parts.push("exhausted".to_string()),
    }
    if !report.over.is_zero() {
        parts.push(format!("over {}", amounts_text(&report.over)));
    }
}

/// The unit word after an amount of `dimension`.
fn unit(dimension: BudgetDimension) -> &'static str {
    match dimension {
        BudgetDimension::Cost | BudgetDimension::Time => "",
        BudgetDimension::Tokens => " tok",
        BudgetDimension::ToolCalls => " calls",
        BudgetDimension::Requests => " req",
    }
}

/// The non-zero dimensions of `amounts`, each with its unit:
/// `$0.42, 31.0k tok, 12 calls, 3 req`; `nothing` when all are zero.
fn amounts_text(amounts: &BudgetAmounts) -> String {
    let parts: Vec<String> = BudgetDimension::ALL
        .into_iter()
        .filter(|dimension| amounts.get(*dimension) > 0)
        .map(|dimension| {
            format!(
                "{}{}",
                amount_text(dimension, amounts.get(dimension)),
                unit(dimension)
            )
        })
        .collect();
    if parts.is_empty() {
        "nothing".to_string()
    } else {
        parts.join(", ")
    }
}

/// What is left of the budget's time at `now_ms`: until its deadline, or
/// what the report says was left when it was read.
fn time_left(report: &BudgetReport, now_ms: u64) -> u64 {
    report.deadline_ms.map_or(report.free.time_ms, |deadline| {
        deadline.saturating_sub(now_ms)
    })
}

/// The one line a budget report reads as at `now_ms` (Unix
/// milliseconds): its dimensions grouped by who decided their limit,
/// each group followed by its source word; a limited dimension as used
/// against the limit (time: what is left), one the principal left
/// unlimited as its spend and `no <name> limit`, one without a limit by
/// default as its spend; then the program runs, the agent's phase when it
/// is not working and the overrun when there is one:
/// `budget: 12/3,200 requests, 41/4,000 tool calls, 3h 58m left (limits
/// on); $0.42 spent, no money limit (set); 31.0k tok; 3 program runs
/// (unconfined, a lower bound)`, or for a run without limits `budget:
/// until finished (default); spent $0.42, 31.0k tok, 12 requests, 41 tool
/// calls`.
#[must_use]
pub fn report_line(report: &BudgetReport, now_ms: u64) -> String {
    let mut groups: Vec<(Option<String>, Vec<String>)> = Vec::new();
    for dimension in LIMITED_ORDER {
        if let Some(limit) = report.limits.get(dimension) {
            let word = source_word(&source_of(report, dimension));
            push_grouped(&mut groups, word, against(report, dimension, limit, now_ms));
        }
    }
    for dimension in LIMITED_ORDER {
        let source = source_of(report, dimension);
        if report.limits.get(dimension).is_some() || source == LimitSource::UntilFinished {
            continue;
        }
        let item = match dimension {
            BudgetDimension::Time => "no time limit".to_owned(),
            BudgetDimension::Cost
            | BudgetDimension::Tokens
            | BudgetDimension::ToolCalls
            | BudgetDimension::Requests => format!(
                "{} spent, no {} limit",
                long_amount(dimension, used(report, dimension)),
                limit_name(dimension)
            ),
        };
        push_grouped(&mut groups, source_word(&source), item);
    }
    for dimension in SPENT_ORDER {
        let spent = used(report, dimension);
        if report.limits.get(dimension).is_none()
            && source_of(report, dimension) == LimitSource::UntilFinished
            && spent > 0
        {
            push_grouped(&mut groups, None, long_amount(dimension, spent));
        }
    }
    let limited = groups.iter().any(|(word, _)| word.is_some());
    let mut parts: Vec<String> = Vec::new();
    if !limited {
        parts.push("until finished (default)".to_owned());
    }
    for (word, items) in &groups {
        parts.push(match word {
            Some(word) => format!("{} ({word})", items.join(", ")),
            None if limited => items.join(", "),
            None => format!("spent {}", items.join(", ")),
        });
    }
    if report.program_runs > 0 {
        parts.push(format!(
            "{} program runs (unconfined, a lower bound)",
            count(report.program_runs)
        ));
    }
    phase_parts(report, &mut parts);
    format!("budget: {}", parts.join("; "))
}

/// The status line's budget segment: the limited dimensions as used
/// against their limit (time: left), grouped by source word (`12/3,200
/// req (limits on)`), or `until finished` for a run without limits; then
/// the phase.
#[must_use]
pub fn status_text(report: &BudgetReport, now_ms: u64) -> String {
    let mut groups: Vec<(String, Vec<String>)> = Vec::new();
    for dimension in LIMITED_ORDER {
        let Some(limit) = report.limits.get(dimension) else {
            continue;
        };
        let item = match dimension {
            BudgetDimension::Time => format!("{} left", duration(time_left(report, now_ms))),
            BudgetDimension::Cost
            | BudgetDimension::Tokens
            | BudgetDimension::ToolCalls
            | BudgetDimension::Requests => format!(
                "{}/{}{}",
                amount_text(dimension, used(report, dimension)),
                amount_text(dimension, limit),
                unit(dimension)
            ),
        };
        let word = source_word(&source_of(report, dimension)).unwrap_or_else(|| "set".to_owned());
        push_grouped(&mut groups, word, item);
    }
    let mut parts: Vec<String> = groups
        .iter()
        .map(|(word, items)| format!("{} ({word})", items.join(", ")))
        .collect();
    if parts.is_empty() {
        parts.push("until finished".to_owned());
    }
    phase_parts(report, &mut parts);
    parts.join("; ")
}

/// [`report_line`] with what a full answer about the budget adds: the
/// deadline (UTC) of a budget with a time limit, and the account's owner
/// when the agent draws from another session's budget.
#[must_use]
pub fn report_detail(report: &BudgetReport, now_ms: u64) -> String {
    let mut line = report_line(report, now_ms);
    if let Some(deadline) = report.deadline_ms {
        line.push_str("; deadline ");
        line.push_str(&utc_time(deadline));
    }
    if !report.agent_session_id.is_empty() && report.agent_session_id != report.session_id {
        line.push_str("; from the budget of ");
        line.push_str(&report.session_id);
    }
    line
}

/// The time now in Unix milliseconds, for [`report_line`] and
/// [`report_detail`] (0 before the epoch).
#[must_use]
pub fn now_ms() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |elapsed| {
            u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
        })
}

/// The one line a ledger audit reads as: `ledger exact: 14 records,
/// settled $0.42, 31.0k tok`, or where the ledger stops adding up.
#[must_use]
pub fn audit_line(audit: &BudgetAudit) -> String {
    match audit.first_mismatch {
        Some(record) => format!("ledger MISMATCH at record {record}"),
        None if audit.exact => format!(
            "ledger exact: {} records, settled {}",
            audit.records,
            amounts_text(&audit.settled)
        ),
        None => format!(
            "ledger MISMATCH: {} records, settled {} but reports {} spent",
            audit.records,
            amounts_text(&audit.settled),
            amounts_text(&audit.spent)
        ),
    }
}

#[cfg(test)]
mod tests;
