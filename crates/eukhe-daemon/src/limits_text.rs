//! The texts of the principal's limits toggle (`budget.limits`) that every
//! surface prints: the line `/budget on` and `eukhe budget on` answer with
//! the numbers the active profile enforces, the line of `/budget off`, and
//! the plan usage notice a run with limits off gets once per plan window
//! and reset when the window's last reading passes the reserve line.

use std::time::{Duration, UNIX_EPOCH};

use eukhe_core::durable::budget::active_profile;
use eukhe_core::platform::{local_time, LocalTime};
use eukhe_types::budget::{AuthClass, LimitValue, RunKind, RunLimits};
use eukhe_types::quota::QuotaWindow;

/// What `/budget off` and `eukhe budget off` answer.
pub const LIMITS_OFF: &str =
    "Limits off: runs go until finished; a limit set for a run still applies.";

/// An instant broken down in a time zone; `None` when the zone cannot
/// convert it.
pub type LocalClock<'a> = &'a dyn Fn(u64) -> Option<LocalTime>;

/// The local time zone of this process.
#[must_use]
pub fn local_clock(epoch_ms: u64) -> Option<LocalTime> {
    local_time(UNIX_EPOCH + Duration::from_millis(epoch_ms)).ok()
}

/// The local calendar day of an instant, counted from 1970-01-01.
#[allow(
    clippy::cast_possible_wrap,
    reason = "epoch seconds stay far inside the i64 range"
)]
fn local_day(epoch_ms: u64, local: &LocalTime) -> i64 {
    ((epoch_ms / 1_000) as i64 + local.offset_seconds).div_euclid(86_400)
}

/// When `at_ms` is in local time, seen at `now_ms`: `19:35` today, `Sat
/// 14:00` within the week, `2026-08-01 14:00` later; `None` when the zone
/// cannot convert either instant.
#[must_use]
pub fn local_when(at_ms: u64, now_ms: u64, clock: LocalClock<'_>) -> Option<String> {
    const WEEKDAYS: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
    let (at, now) = (clock(at_ms)?, clock(now_ms)?);
    let time = format!("{:02}:{:02}", at.hour, at.minute);
    let day = local_day(at_ms, &at);
    Some(match day - local_day(now_ms, &now) {
        0 => time,
        1..=6 => {
            let weekday = usize::try_from((day + 4).rem_euclid(7)).unwrap_or_default();
            format!("{} {time}", WEEKDAYS[weekday])
        }
        _ => format!("{} {time}", at.date()),
    })
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

/// A time limit in its largest whole unit: `4 h`, `90 min`, `45 s`.
fn hours(ms: u64) -> String {
    match (ms % 3_600_000, ms % 60_000) {
        (0, _) => format!("{} h", ms / 3_600_000),
        (_, 0) => format!("{} min", ms / 60_000),
        (_, _) => format!("{} s", ms.div_ceil(1_000)),
    }
}

/// `a`, `a and b`, `a, b and c`.
fn listed(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [one] => one.clone(),
        [rest @ .., last] => format!("{} and {last}", rest.join(", ")),
    }
}

/// The limited dimensions of `limits` as the on line names them: `4 h,
/// 4,000 tool calls and 3,200 requests`.
fn work_limits(limits: &RunLimits) -> Vec<String> {
    let at = |value: Option<LimitValue>| value.and_then(LimitValue::at);
    let mut items = Vec::new();
    if let Some(ms) = at(limits.time_ms) {
        items.push(hours(ms));
    }
    if let Some(calls) = at(limits.tool_calls) {
        items.push(format!("{} tool calls", count(calls)));
    }
    if let Some(requests) = at(limits.requests) {
        items.push(format!("{} requests", count(requests)));
    }
    if let Some(micros) = at(limits.cost_micros) {
        let cents = micros.div_ceil(10_000);
        items.push(format!("${}.{:02}", cents / 100, cents % 100));
    }
    if let Some(tokens) = at(limits.tokens) {
        items.push(format!("{} tokens", count(tokens)));
    }
    items
}

/// What `/budget on` and `eukhe budget on` answer: the numbers the active
/// profile enforces per message (`profile(kind)`: the limits a run of
/// that kind fills with limits on), the time of the loop, scheduled and
/// autoresearch runs, and, with a plan login (`plan_line`: the percent of
/// each plan window a run ends at), the plan clause.
#[must_use]
pub fn limits_on_line(plan_line: Option<u64>, profile: &dyn Fn(RunKind) -> RunLimits) -> String {
    let work = listed(&work_limits(&profile(RunKind::Interactive)));
    let at = match (plan_line, work.is_empty()) {
        (Some(percent), false) => {
            format!("{percent} % of each plan window, or at {work} per message")
        }
        (Some(percent), true) => format!("{percent} % of each plan window"),
        (None, false) => format!("{work} per message"),
        (None, true) => "the limits the profile sets".to_owned(),
    };
    let kinds: Vec<String> = [
        (RunKind::Loop, "loop"),
        (RunKind::Scheduled, "scheduled"),
        (RunKind::Autoresearch, "autoresearch"),
    ]
    .into_iter()
    .filter_map(|(kind, name)| {
        let ms = profile(kind).time_ms.and_then(LimitValue::at)?;
        Some(format!("{name} {}", hours(ms)))
    })
    .collect();
    let kinds = if kinds.is_empty() {
        String::new()
    } else {
        format!(" ({})", kinds.join(", "))
    };
    format!("Limits on: runs end with their answer at {at}{kinds}; /budget off turns them off.")
}

/// The line `/budget on` and `eukhe budget on` answer for a model paid by
/// `auth`: the plan clause only for a plan login (at `100 - reserve` % of
/// each window), the numbers of the active profile (`profile`, the
/// setting `budget.profile`, over the limits profile).
#[must_use]
pub fn on_line(auth: AuthClass, reserve: u64, profile: &serde_json::Value) -> String {
    let plan = match auth {
        AuthClass::Plan => Some(100 - reserve.min(100)),
        AuthClass::ApiKey | AuthClass::Local => None,
    };
    limits_on_line(plan, &|kind: RunKind| {
        // A profile setting that does not read leaves the limits profile
        // alone: its error is the run's, when one starts.
        active_profile(kind, auth, profile)
            .or_else(|_| active_profile(kind, auth, &serde_json::Value::Null))
            .unwrap_or_default()
    })
}

/// A plan window as the notice names it: `the 5-hour window`, `the 7-day
/// opus window`, or by its label when its length is unknown.
fn window_name(window: &QuotaWindow) -> String {
    let qualifier = window
        .label
        .split_once(' ')
        .map_or(String::new(), |(_, rest)| format!(" {rest}"));
    let length = match window.window_minutes {
        Some(minutes) if minutes > 0 && minutes % 1_440 == 0 => {
            format!("{}-day", minutes / 1_440)
        }
        Some(minutes) if minutes > 0 && minutes % 60 == 0 => format!("{}-hour", minutes / 60),
        Some(minutes) if minutes > 0 => format!("{minutes}-minute"),
        Some(_) | None => return format!("the {} window", window.label),
    };
    format!("the {length}{qualifier} window")
}

/// The notice a run with limits off gets when the last reading of a plan
/// window passed `100 - reserve_percent` % used: `Plan usage at 80 % of
/// the 5-hour window (resets 18:40); the run continues. /budget on ends
/// runs at this point.` The reset time is local (`clock`), with its day
/// when it is not today.
#[must_use]
pub fn plan_usage_line(
    window: &QuotaWindow,
    reserve_percent: u64,
    now_ms: u64,
    clock: LocalClock<'_>,
) -> String {
    let resets = window
        .resets_at_ms
        .and_then(|at| local_when(at, now_ms, clock))
        .map_or(String::new(), |when| format!(" (resets {when})"));
    format!(
        "Plan usage at {} % of {}{resets}; the run continues. /budget on ends runs at this point.",
        100 - reserve_percent.min(100),
        window_name(window)
    )
}

#[cfg(test)]
mod tests;
