//! The watch's call on one poll of a child (rule H5,
//! `LAWS.bend`): `verdict` in `bend/child.bend`, run by the compiled
//! Bend core (`bend/ffi_child.bend`). `LAWS.bend` states what it guarantees
//! (a child with no progress is reported within `subagentStallMs`, failed
//! polls within [`CHILD_POLL_FAILURES`], a child that progresses never; the
//! call is the watch's verdict as the task's report mode acts on it, and a
//! silent task never reports).
//!
//! The checkpoint keeps the clock as it always did ([`Vigil`]: the quiet
//! time counts up, the failed polls count up); the model's clock counts
//! down what is left (`W{tok, left, tries}`): `left = stall - quiet` and
//! `tries = CHILD_POLL_FAILURES - failures`, in whole ms. The counts
//! saturate at the wire's [`NAT_MAX`] (a stall of 3000 years).

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::Entry;
use serde::{Deserialize, Serialize};

use super::task::ReportMode;

/// Failed polls in a row that report a child unreachable.
pub(crate) const CHILD_POLL_FAILURES: u32 = 5;

/// The watch's clock on one child, kept in its checkpoint.
#[derive(Debug, Clone, Copy, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Vigil {
    /// The child's progress token at the last poll that read one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) progress: Option<u64>,
    /// How long the child has shown no progress, in ms (whole ms; a
    /// checkpoint of an older eukhe may hold a fraction).
    #[serde(default)]
    pub(crate) quiet_ms: f64,
    /// Failed polls in a row.
    #[serde(default)]
    pub(crate) failures: u32,
}

/// What one poll read (`Obs` in `bend/child.bend`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Obs {
    /// The child is unsettled (running, or idle with background jobs),
    /// with its progress token when the host read one.
    Busy { progress: Option<u64> },
    /// The poll got no answer.
    Lost,
    /// The child's run answered; `replied`: the child already replied to
    /// its parent through an agent message.
    Answered { replied: bool },
    /// The child's run failed.
    Broke,
}

/// What the parent is told (`Report` in `bend/child.bend`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Report {
    Completed,
    Failed,
    Cancelled,
    Stalled,
    Unreachable,
}

/// What the task does after one poll (`Call` in `bend/child.bend`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum Call {
    /// Watch on with this clock.
    Watches(Vigil),
    /// Report this to the parent.
    Reports(Report),
    /// End with no report: why (`None`: the child replied to its parent;
    /// else the report a silent task does not send).
    Settles(Option<Report>),
}

/// A count in whole ms, as the wire carries it.
fn whole_ms(ms: f64) -> u64 {
    // A float-to-int `as` saturates (NaN reads 0): the clock's counts are
    // never negative.
    (ms.round() as u64).min(NAT_MAX)
}

/// The call on a poll that read `obs` `elapsed_ms` after the last one, for
/// a child that may show no progress for `stall_ms`, in `mode`.
pub(crate) fn verdict(
    vigil: Vigil,
    stall_ms: f64,
    elapsed_ms: f64,
    obs: Obs,
    mode: ReportMode,
) -> Call {
    eukhe_bend::expect_core(Entry::Child, ask(vigil, stall_ms, elapsed_ms, obs, mode))
}

fn ask(
    vigil: Vigil,
    stall_ms: f64,
    elapsed_ms: f64,
    obs: Obs,
    mode: ReportMode,
) -> Result<Call, eukhe_bend::Error> {
    let stall = whole_ms(stall_ms);
    let fails = u64::from(CHILD_POLL_FAILURES);
    let mut request = Writer::new();
    request.tag(0).nat(stall).nat(fails);
    put_clock(&mut request, vigil.progress);
    request
        .nat(stall.saturating_sub(whole_ms(vigil.quiet_ms)))
        .nat(fails.saturating_sub(u64::from(vigil.failures)))
        .nat(whole_ms(elapsed_ms));
    match obs {
        Obs::Busy { progress } => {
            request.tag(0);
            put_clock(&mut request, progress);
        }
        Obs::Lost => {
            request.tag(1);
        }
        Obs::Answered { replied } => {
            request.tag(2).bool(replied);
        }
        Obs::Broke => {
            request.tag(3);
        }
    }
    request.tag(match mode {
        ReportMode::Inbox => 0,
        ReportMode::Silent => 1,
    });
    let reply = eukhe_bend::call(Entry::Child, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let call = match reply.tag_of(3, "a child task's call")? {
        0 => {
            let progress = if reply.maybe()? {
                Some(reply.nat()?)
            } else {
                None
            };
            let left = reply.nat()?;
            let tries = reply.nat()?;
            Call::Watches(Vigil {
                progress,
                quiet_ms: stall.saturating_sub(left) as f64,
                // At most CHILD_POLL_FAILURES.
                failures: fails.saturating_sub(tries) as u32,
            })
        }
        1 => Call::Reports(get_report(&mut reply)?),
        // `tag_of` answers a tag below 3: this is 2.
        _ => Call::Settles(if reply.maybe()? {
            Some(get_report(&mut reply)?)
        } else {
            None
        }),
    };
    reply.end()?;
    Ok(call)
}

/// A progress token, saturated at the wire's largest Nat: a count of acts
/// never comes near it.
fn put_clock(request: &mut Writer, progress: Option<u64>) {
    match progress {
        None => request.none(),
        Some(token) => request.some().nat(token.min(NAT_MAX)),
    };
}

pub(super) fn get_report(reply: &mut Reader<'_>) -> Result<Report, WireError> {
    Ok(match reply.tag_of(5, "a child report")? {
        0 => Report::Completed,
        1 => Report::Failed,
        2 => Report::Cancelled,
        3 => Report::Stalled,
        // `tag_of` answers a tag below 5: this is 4.
        _ => Report::Unreachable,
    })
}
