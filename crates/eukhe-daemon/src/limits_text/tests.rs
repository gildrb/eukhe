use eukhe_core::platform::LocalTime;
use eukhe_types::budget::{LimitValue, RunKind, RunLimits};
use eukhe_types::quota::QuotaWindow;

use super::{limits_on_line, plan_usage_line};

/// Sat 2026-07-25 17:20:00 UTC.
const NOW: u64 = 1_785_000_000_000;
const HOUR: u64 = 3_600_000;

/// The test zone: UTC+2. Each instant the tests use, broken down.
fn clock(epoch_ms: u64) -> Option<LocalTime> {
    let at = |day: u32, hour: u32, minute: u32| LocalTime {
        year: 2026,
        month: if day > 31 { 8 } else { 7 },
        day: if day > 31 { day - 31 } else { day },
        hour,
        minute,
        second: 0,
        millisecond: 0,
        offset_seconds: 7_200,
    };
    match epoch_ms {
        NOW => Some(at(25, 19, 20)),
        ms if ms == NOW + HOUR + 20 * 60_000 => Some(at(25, 20, 40)),
        ms if ms == NOW + 51 * HOUR => Some(at(27, 22, 20)),
        ms if ms == NOW + 240 * HOUR => Some(at(35, 19, 20)),
        _ => None,
    }
}

/// The limits profile as `eukhe_bend::rules::limits::profile` ships it,
/// for a provider with a price.
fn shipped(kind: RunKind) -> RunLimits {
    let (hours, calls, requests) = match kind {
        RunKind::Interactive | RunKind::Headless | RunKind::Sdk => (4, 4_000, 3_200),
        RunKind::Scheduled => (1, 4_000, 3_200),
        RunKind::Loop => (8, 8_000, 6_400),
        RunKind::Autoresearch => (12, 12_000, 9_600),
    };
    RunLimits {
        time_ms: Some(LimitValue::At(hours * HOUR)),
        tool_calls: Some(LimitValue::At(calls)),
        requests: Some(LimitValue::At(requests)),
        ..RunLimits::default()
    }
}

/// `/budget on` names the numbers of the active profile, with the plan
/// clause only for a plan login; a profile of the principal's own shows
/// its numbers, a local model's leaves tool calls out.
#[test]
fn the_on_line_names_the_numbers_the_profile_enforces() {
    let own = |kind: RunKind| RunLimits {
        time_ms: Some(LimitValue::At(90 * 60_000)),
        cost_micros: Some(LimitValue::At(2_000_000)),
        tool_calls: Some(LimitValue::Unlimited),
        ..shipped(kind)
    };
    let local = |kind: RunKind| RunLimits {
        tool_calls: None,
        ..shipped(kind)
    };
    assert_eq!(
        [
            limits_on_line(Some(80), &shipped),
            limits_on_line(None, &shipped),
            limits_on_line(None, &own),
            limits_on_line(Some(75), &local),
        ],
        [
            "Limits on: runs end with their answer at 80 % of each plan window, or at 4 h, 4,000 tool calls and 3,200 requests per message (loop 8 h, scheduled 1 h, autoresearch 12 h); /budget off turns them off.",
            "Limits on: runs end with their answer at 4 h, 4,000 tool calls and 3,200 requests per message (loop 8 h, scheduled 1 h, autoresearch 12 h); /budget off turns them off.",
            "Limits on: runs end with their answer at 90 min, 3,200 requests and $2.00 per message (loop 90 min, scheduled 90 min, autoresearch 90 min); /budget off turns them off.",
            "Limits on: runs end with their answer at 75 % of each plan window, or at 4 h and 3,200 requests per message (loop 8 h, scheduled 1 h, autoresearch 12 h); /budget off turns them off.",
        ]
    );
}

fn window(label: &str, minutes: Option<u64>, resets: Option<u64>) -> QuotaWindow {
    QuotaWindow {
        label: label.to_owned(),
        window_minutes: minutes,
        used_permille: 812,
        resets_at_ms: resets,
    }
}

/// The plan notice names the window by its length and its reset in local
/// time, with the day when it is not today.
#[test]
fn the_plan_notice_names_the_window_and_its_local_reset() {
    let notice = |window: &QuotaWindow| plan_usage_line(window, 20, NOW, &clock);
    assert_eq!(
        [
            notice(&window("5h", Some(300), Some(NOW + HOUR + 20 * 60_000))),
            notice(&window("7d opus", Some(10_080), Some(NOW + 51 * HOUR))),
            notice(&window("month premium", None, Some(NOW + 240 * HOUR))),
            notice(&window("5h", Some(300), None)),
        ],
        [
            "Plan usage at 80 % of the 5-hour window (resets 20:40); the run continues. /budget on ends runs at this point.",
            "Plan usage at 80 % of the 7-day opus window (resets Mon 22:20); the run continues. /budget on ends runs at this point.",
            "Plan usage at 80 % of the month premium window (resets 2026-08-04 19:20); the run continues. /budget on ends runs at this point.",
            "Plan usage at 80 % of the 5-hour window; the run continues. /budget on ends runs at this point.",
        ]
    );
}
