//! The restart budget of one worker: the failures inside the restart
//! window, on the monotonic clock. A failure past the budget gives the
//! worker up; any other failure relaunches it after a pause that doubles
//! with each failure in the window.
//!
//! The rule is one pure call, [`decide`], to the compiled Bend model
//! (`bend/ffi_supervise.bend` over bend/supervise.bend `decide`): the ages
//! of the failures in the window, in ms, newest first, relative to the
//! last failure, and the gap in ms since it. The laws
//! `restart_decide_window`, `restart_decide_verdict` and
//! `restart_gives_up` (`laws/supervise.bend`, D1) pin the decision. The budget keeps
//! the clock: it measures every failure in whole ms from its first one, so
//! the gaps telescope and the ages carry no rounding drift.

use std::time::{Duration, Instant};

use crate::timeouts::{
    self, RESTART_BASE_BACKOFF_MS, RESTART_GIVE_UP_AFTER, RESTART_MAX_BACKOFF_MS,
};

/// What the supervisor does after a worker failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RestartVerdict {
    /// Relaunch after `backoff`; `failure` failures (this one included)
    /// are in the window.
    Relaunch { failure: u32, backoff: Duration },
    /// More than [`RESTART_GIVE_UP_AFTER`] failures are in the window.
    GiveUp { failures: u32 },
}

/// The budget's configuration (the model's `Cfg`): the failures the
/// window allows, the window, the first pause and the longest pause (ms).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RestartCfg {
    pub(crate) give_up_after: u64,
    pub(crate) window_ms: u64,
    pub(crate) base_backoff_ms: u64,
    pub(crate) max_backoff_ms: u64,
}

/// The supervisor's budget configuration (its window is derived by the
/// compiled core, `timeouts::derived`).
pub(crate) fn restart_cfg() -> RestartCfg {
    RestartCfg {
        give_up_after: u64::from(RESTART_GIVE_UP_AFTER),
        window_ms: timeouts::derived().restart_window_ms,
        base_backoff_ms: RESTART_BASE_BACKOFF_MS,
        max_backoff_ms: RESTART_MAX_BACKOFF_MS,
    }
}

/// The decision on a failure `gap_ms` after the last one, from the ages
/// (ms, newest first, relative to the last failure) of the failures in
/// the window: the new ages (this failure at age 0 in front) and the
/// verdict. Every number fits the wire: the configuration is the
/// supervisor's constants, an age stays below the window, and the caller
/// saturates the gap at the window.
pub(crate) fn decide(cfg: RestartCfg, ages: &[u64], gap_ms: u64) -> (Vec<u64>, RestartVerdict) {
    eukhe_bend::expect_core(eukhe_bend::Entry::Supervise, decide_call(cfg, ages, gap_ms))
}

fn decide_call(
    cfg: RestartCfg,
    ages: &[u64],
    gap_ms: u64,
) -> Result<(Vec<u64>, RestartVerdict), eukhe_bend::Error> {
    let mut request = eukhe_bend::wire::Writer::new();
    request
        .nat(cfg.give_up_after)
        .nat(cfg.window_ms)
        .nat(cfg.base_backoff_ms)
        .nat(cfg.max_backoff_ms)
        .count(ages.len());
    for age in ages {
        request.nat(*age);
    }
    request.nat(gap_ms);
    let reply = eukhe_bend::call(eukhe_bend::Entry::Supervise, &request.finish()?)?;
    let mut reader = eukhe_bend::wire::Reader::reply(&reply)?;
    let kept = (0..reader.count()?)
        .map(|_| reader.nat())
        .collect::<Result<Vec<u64>, _>>()?;
    let verdict = if reader.tag_of(2, "a restart verdict")? == 0 {
        let failure = count(reader.nat()?);
        let backoff = Duration::from_millis(reader.nat()?);
        RestartVerdict::Relaunch { failure, backoff }
    } else {
        RestartVerdict::GiveUp {
            failures: count(reader.nat()?),
        }
    };
    reader.end()?;
    Ok((kept, verdict))
}

/// A failure count, saturated at `u32::MAX`.
fn count(n: u64) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}

/// The failures of one worker inside the restart window.
#[derive(Debug, Default)]
pub(crate) struct RestartBudget {
    /// The first failure since the budget was last cleared, and the whole
    /// ms from it to the last failure.
    clock: Option<(Instant, u64)>,
    /// The ages (ms, newest first) of the failures in the window, at the
    /// last failure.
    ages: Vec<u64>,
}

impl RestartBudget {
    /// Count a failure at `now` (a monotonic instant, never earlier than
    /// the failure before it) and decide what follows.
    pub(crate) fn on_failure(&mut self, now: Instant) -> RestartVerdict {
        let (epoch, last_ms) = *self.clock.get_or_insert((now, 0));
        let now_ms =
            u64::try_from(now.saturating_duration_since(epoch).as_millis()).unwrap_or(u64::MAX);
        // A gap of a whole window drops every age, so the gap saturates at
        // the window: exact, and inside the Bend core's Nat range.
        let cfg = restart_cfg();
        let gap_ms = now_ms.saturating_sub(last_ms).min(cfg.window_ms);
        let (ages, verdict) = decide(cfg, &self.ages, gap_ms);
        self.clock = Some((epoch, now_ms));
        self.ages = ages;
        verdict
    }

    /// Forget every failure (a client reopened the worker: a new start).
    pub(crate) fn clear(&mut self) {
        self.clock = None;
        self.ages.clear();
    }
}
