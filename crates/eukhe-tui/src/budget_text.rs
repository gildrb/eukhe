//! The human syntax of a budget, shared by every surface that reads or
//! shows one (the CLI's `--budget-*` flags, final line and `eukhe budget`,
//! `/budget`, the status line): the amounts a user types and the line a
//! report reads as.
//!
//! Typed amounts: cost in dollars (`1.50`, `$1.50`; stored in
//! micro-dollars, rounded up), tokens (`200000`, `200k`, `1.5m`), time
//! (`90s`, `10m`, `2h`; stored in milliseconds: the wall-clock duration of
//! the budget from when it is set, or by how much `add` moves the
//! deadline), tool calls and model requests (plain integers). Each is more
//! than zero and at most [`BUDGET_AMOUNT_MAX`] in its stored unit.
//!
//! The report line names, per limited dimension, what is used (spent,
//! held by requests in flight and lent to children) against the limit,
//! and for time what is left until the deadline:
//! `budget: $0.42/$2.00 - 31.0k/200k tok - 6m 50s left - 12/50 calls -
//! 3/30 req`, then the agent's phase when it is not working and the
//! overrun when there is one. The caller passes the separator of its
//! surface and the time now (Unix milliseconds).

use eukhe_types::budget::{
    dollars, BudgetAmounts, BudgetDimension, BudgetLimits, BudgetPhase, BudgetReport,
    BUDGET_AMOUNT_MAX,
};
use eukhe_types::daemon::BudgetAudit;

/// The keys of `/budget set` and `/budget add`, as their errors list them.
const KEYS: &str = "cost=<dollars>, tokens=<n>, time=<duration>, calls=<n>, requests=<n>";

/// Why typed text is not a budget amount. `name` is what the user typed
/// the value for: a flag (`--budget-cost`) or a key (`cost`).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum BudgetTextError {
    /// The value does not read as an amount of its dimension.
    #[error("{name} \"{value}\": expected {expected}")]
    Malformed {
        name: String,
        value: String,
        expected: &'static str,
    },
    /// The value reads as zero.
    #[error("{name} \"{value}\": a budget amount is more than zero")]
    Zero { name: String, value: String },
    /// The value is past what a budget holds.
    #[error("{name} \"{value}\": a budget holds at most {max}")]
    TooLarge {
        name: String,
        value: String,
        max: String,
    },
    /// A word of `/budget set` or `/budget add` that is not `key=value`
    /// with a known key.
    #[error("\"{word}\": expected one of {KEYS}")]
    UnknownWord { word: String },
    /// A key given more than once.
    #[error("{name} is given twice")]
    Repeated { name: String },
    /// No `key=value` word at all.
    #[error("name at least one of {KEYS}")]
    NoAmount,
}

/// `number` (`digits` or `digits.digits`) times `scale`, rounded up and
/// saturating; `None` when it is not such a number. A number starts with
/// a digit: `.50` is what an unquoted `$1.50` leaves of itself in a
/// shell, and must not read as half a dollar.
fn scaled(number: &str, scale: u64) -> Option<u128> {
    let (whole, fraction) = match number.split_once('.') {
        Some((whole, fraction)) if !fraction.is_empty() => (whole, fraction),
        Some(_) => return None,
        None => (number, ""),
    };
    let digits = |text: &str| text.bytes().all(|byte| byte.is_ascii_digit());
    if whole.is_empty() || !digits(whole) || !digits(fraction) {
        return None;
    }
    let value = |text: &str| {
        text.bytes().fold(0_u128, |sum, byte| {
            sum.saturating_mul(10)
                .saturating_add(u128::from(byte - b'0'))
        })
    };
    // Twelve fraction digits are past every scale's precision: the rest
    // only decides the rounding.
    let (kept, rest) = fraction.split_at(fraction.len().min(12));
    let numerator = value(kept) * u128::from(scale);
    let denominator = 10_u128.pow(u32::try_from(kept.len()).unwrap_or(0));
    let rounds_up = numerator % denominator != 0 || rest.bytes().any(|byte| byte != b'0');
    Some(
        value(whole)
            .saturating_mul(u128::from(scale))
            .saturating_add(numerator / denominator)
            .saturating_add(u128::from(rounds_up)),
    )
}

/// `text` without its last character when that is `suffix` in either
/// case.
fn strip_unit(text: &str, suffix: char) -> Option<&str> {
    let last = text.chars().next_back()?;
    last.eq_ignore_ascii_case(&suffix)
        .then(|| &text[..text.len() - last.len_utf8()])
}

/// A whole number (no fraction, no unit).
fn whole(text: &str) -> Option<u128> {
    if text.contains('.') {
        None
    } else {
        scaled(text, 1)
    }
}

/// The amount of `dimension` that `text` names, in the dimension's stored
/// unit; `name` is what the user typed it for.
///
/// # Errors
///
/// Text that is not an amount of the dimension, zero, or an amount past
/// [`BUDGET_AMOUNT_MAX`]: the error names `name` and the text.
pub fn parse_amount(
    dimension: BudgetDimension,
    name: &str,
    text: &str,
) -> Result<u64, BudgetTextError> {
    let text = text.trim();
    let (amount, expected) = match dimension {
        BudgetDimension::Cost => (
            scaled(text.strip_prefix('$').unwrap_or(text), 1_000_000),
            "dollars, like 1.50 or $1.50",
        ),
        BudgetDimension::Tokens => (
            if let Some(thousands) = strip_unit(text, 'k') {
                scaled(thousands, 1_000)
            } else if let Some(millions) = strip_unit(text, 'm') {
                scaled(millions, 1_000_000)
            } else {
                scaled(text, 1)
            },
            "a token count, like 200000, 200k or 1.5m",
        ),
        BudgetDimension::Time => (
            if let Some(seconds) = strip_unit(text, 's') {
                scaled(seconds, 1_000)
            } else if let Some(minutes) = strip_unit(text, 'm') {
                scaled(minutes, 60_000)
            } else if let Some(hours) = strip_unit(text, 'h') {
                scaled(hours, 3_600_000)
            } else {
                None
            },
            "a duration, like 90s, 10m or 2h",
        ),
        BudgetDimension::ToolCalls => (whole(text), "a whole number of tool calls, like 50"),
        BudgetDimension::Requests => (whole(text), "a whole number of model requests, like 30"),
    };
    let stored = amount.map(|amount| {
        u64::try_from(amount)
            .ok()
            .filter(|amount| *amount <= BUDGET_AMOUNT_MAX)
    });
    let (name, value) = match stored {
        Some(Some(amount)) if amount > 0 => return Ok(amount),
        Some(Some(_) | None) | None => (name.to_string(), text.to_string()),
    };
    Err(match stored {
        Some(Some(_)) => BudgetTextError::Zero { name, value },
        Some(None) => BudgetTextError::TooLarge {
            name,
            value,
            max: match dimension {
                BudgetDimension::Cost => format!(
                    "${}.{:06}",
                    BUDGET_AMOUNT_MAX / 1_000_000,
                    BUDGET_AMOUNT_MAX % 1_000_000
                ),
                BudgetDimension::Tokens => format!("{BUDGET_AMOUNT_MAX} tokens"),
                BudgetDimension::Time => format!("{}h", BUDGET_AMOUNT_MAX / 3_600_000),
                BudgetDimension::ToolCalls => format!("{BUDGET_AMOUNT_MAX} tool calls"),
                BudgetDimension::Requests => format!("{BUDGET_AMOUNT_MAX} requests"),
            },
        },
        None => BudgetTextError::Malformed {
            name,
            value,
            expected,
        },
    })
}

/// The `key=value` words of `/budget set` and `/budget add`: `cost`,
/// `tokens`, `time`, `calls` and `requests`, any subset, each at most
/// once.
///
/// # Errors
///
/// A word that is not `key=value` with one of the five keys, a key given
/// twice, no word at all, or a value [`parse_amount`] refuses.
pub fn parse_assignments(text: &str) -> Result<BudgetLimits, BudgetTextError> {
    let mut limits = BudgetLimits::default();
    for word in text.split_whitespace() {
        let unknown = || BudgetTextError::UnknownWord {
            word: word.to_string(),
        };
        let (key, value) = word.split_once('=').ok_or_else(unknown)?;
        let dimension = match key {
            "cost" => BudgetDimension::Cost,
            "tokens" => BudgetDimension::Tokens,
            "time" => BudgetDimension::Time,
            "calls" => BudgetDimension::ToolCalls,
            "requests" => BudgetDimension::Requests,
            _ => return Err(unknown()),
        };
        if limits.get(dimension).is_some() {
            return Err(BudgetTextError::Repeated {
                name: key.to_string(),
            });
        }
        limits = limits.with(dimension, Some(parse_amount(dimension, key, value)?));
    }
    if limits.is_unlimited() {
        return Err(BudgetTextError::NoAmount);
    }
    Ok(limits)
}

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
        BudgetDimension::ToolCalls | BudgetDimension::Requests => amount.to_string(),
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

/// The one line a budget report reads as at `now_ms` (Unix milliseconds),
/// its parts joined by `separator`: per limited dimension what is used
/// (spent, held and lent) against the limit and the time left until the
/// deadline, the agent's phase when it is not working, and the overrun
/// when there is one.
#[must_use]
pub fn report_line(report: &BudgetReport, now_ms: u64, separator: &str) -> String {
    let mut parts: Vec<String> = BudgetDimension::ALL
        .into_iter()
        .filter_map(|dimension| {
            let limit = report.limits.get(dimension)?;
            if dimension == BudgetDimension::Time {
                return Some(format!("{} left", duration(time_left(report, now_ms))));
            }
            let used = report
                .spent
                .get(dimension)
                .saturating_add(report.held.get(dimension))
                .saturating_add(report.lent.get(dimension));
            Some(format!(
                "{}/{}{}",
                amount_text(dimension, used),
                amount_text(dimension, limit),
                unit(dimension)
            ))
        })
        .collect();
    if parts.is_empty() {
        parts.push("no limit".to_string());
    }
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
    format!("budget: {}", parts.join(separator))
}

/// [`report_line`] with what a full answer about the budget adds: the
/// deadline (UTC) of a budget with a time limit, and the account's owner
/// when the agent draws from another session's budget.
#[must_use]
pub fn report_detail(report: &BudgetReport, now_ms: u64, separator: &str) -> String {
    let mut line = report_line(report, now_ms, separator);
    if let Some(deadline) = report.deadline_ms {
        line.push_str(separator);
        line.push_str("deadline ");
        line.push_str(&utc_time(deadline));
    }
    if !report.agent_session_id.is_empty() && report.agent_session_id != report.session_id {
        line.push_str(separator);
        line.push_str("from the budget of ");
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
