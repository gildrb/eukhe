//! Which daemon commands a tab may `run`, and how they are sent: the
//! compiled Bend core decides (`bend/dash_policy.bend`, entry
//! `bend/ffi_dash_policy.bend`, laws `laws/dash_policy.bend`). The bound
//! session's user controls go to the bound session (the bridge sets its
//! id); catalog commands (saved sessions, schedules) go with no session id;
//! everything else is refused, a command the core does not list included.

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};

/// Whether, and how, the dashboard runs one command for a tab.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Verdict {
    /// Sent for the bound session (the bridge sets `activeSessionId`).
    Bound,
    /// Sent with no session id: the command names its sessions itself.
    Catalog,
    Refused,
}

/// The verdict on the daemon command whose `type` is `kind` (a name the
/// bridge already parsed as a `DaemonCommand`).
pub(crate) fn verdict(kind: &str) -> Verdict {
    let answer = || -> Result<Verdict, Error> {
        let reply = call(Entry::DashPolicy, &Writer::new().str(kind).finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let verdict = match reader.tag_of(3, "a command verdict")? {
            0 => Verdict::Bound,
            1 => Verdict::Catalog,
            2.. => Verdict::Refused,
        };
        reader.end()?;
        Ok(verdict)
    };
    expect_core(Entry::DashPolicy, answer())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_core_decides_each_kind_of_verdict() {
        assert_eq!(
            ["get_state", "cron_list", "create"].map(verdict),
            [Verdict::Bound, Verdict::Catalog, Verdict::Refused]
        );
    }
}
