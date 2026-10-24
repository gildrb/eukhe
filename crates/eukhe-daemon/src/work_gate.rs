//! Whether a worker holds work, and the gate that keeps it from starting
//! new work while a supervisor replacement decides. The decisions (a run
//! start at the gate, a quiesce, the commit of an idle shutdown) run as
//! the compiled Bend core (`bend/ffi_launcher.bend`, the model
//! `bend/launcher.bend`; laws `launcher_ffi_answers` and
//! `idle_shutdown_never_aborts` in `laws/launcher.bend`), as does the
//! orphan exit (`bend/ffi_orphan.bend`).
//!
//! An idle shutdown is two-phase. The supervisor asks every worker to
//! quiesce. A worker answers under its session lock: with work it answers
//! [`QuiesceAnswer::Busy`]; without work it closes its gate and answers
//! [`QuiesceAnswer::Quiesced`]. A closed gate refuses every new run, so a
//! quiesced worker stays idle. The supervisor stops the workers only when
//! every answer is `Quiesced`; otherwise it opens the gates again and
//! refuses the shutdown as busy. The client never decides.

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::{Entry, Error};

/// The work a worker holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Work {
    /// No run, compaction, queued input, background job or unsettled
    /// child: a stop interrupts nothing.
    Idle,
    /// Work that a stop would interrupt.
    Ongoing,
}

/// A worker's answer to a quiesce.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum QuiesceAnswer {
    /// The worker was idle and its gate is now closed.
    Quiesced,
    /// The worker holds work; its gate stays as it was.
    Busy,
}

/// The gate of one worker: closed while a replacement decides.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct WorkGate {
    closed: bool,
}

impl WorkGate {
    /// Whether a new run may start now (the core's answer: only at an
    /// open gate).
    pub(crate) fn admits(self) -> bool {
        eukhe_bend::expect_core(Entry::Launcher, admits(self.closed))
    }

    /// Quiesce with the worker's `work`, read under the same lock as this
    /// call: an idle worker closes its gate, a busy one keeps it as it is
    /// (the core's answer).
    pub(crate) fn quiesce(&mut self, work: Work) -> QuiesceAnswer {
        let (closed, answer) = eukhe_bend::expect_core(Entry::Launcher, quiesce(work, self.closed));
        self.closed = closed;
        answer
    }

    /// The replacement did not commit: new work may start again.
    pub(crate) fn release(&mut self) {
        self.closed = false;
    }
}

fn admits(closed: bool) -> Result<bool, Error> {
    let mut request = Writer::new();
    request.tag(0).bool(closed);
    let reply = eukhe_bend::call(Entry::Launcher, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let admits = reader.bool()?;
    reader.end()?;
    Ok(admits)
}

fn quiesce(work: Work, closed: bool) -> Result<(bool, QuiesceAnswer), Error> {
    let mut request = Writer::new();
    request.tag(1).bool(work == Work::Ongoing).bool(closed);
    let reply = eukhe_bend::call(Entry::Launcher, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let closed = reader.bool()?;
    let answer = if reader.bool()? {
        QuiesceAnswer::Quiesced
    } else {
        QuiesceAnswer::Busy
    };
    reader.end()?;
    Ok((closed, answer))
}

/// Whether an idle shutdown commits (the core's answer: only when every
/// worker quiesced).
pub(crate) fn idle_shutdown_commits(answers: impl IntoIterator<Item = QuiesceAnswer>) -> bool {
    eukhe_bend::expect_core(Entry::Launcher, commits(answers))
}

fn commits(answers: impl IntoIterator<Item = QuiesceAnswer>) -> Result<bool, Error> {
    let answers: Vec<bool> = answers
        .into_iter()
        .map(|answer| answer == QuiesceAnswer::Quiesced)
        .collect();
    let mut request = Writer::new();
    request.tag(2).count(answers.len());
    for quiesced in answers {
        request.bool(quiesced);
    }
    let reply = eukhe_bend::call(Entry::Launcher, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let commits = reader.bool()?;
    reader.end()?;
    Ok(commits)
}

/// The core's adoption verdict for a worker that reports a build (`None`:
/// none): `Some(true)` the supervisor's build, `Some(false)` another.
/// `true`: the worker is adopted.
pub(crate) fn adopts(worker_build: Option<bool>) -> bool {
    eukhe_bend::expect_core(Entry::Launcher, adopt(worker_build))
}

fn adopt(worker_build: Option<bool>) -> Result<bool, Error> {
    let mut request = Writer::new();
    request.tag(3);
    match worker_build {
        None => request.none(),
        Some(same) => request.some().nat(u64::from(!same)),
    };
    let reply = eukhe_bend::call(Entry::Launcher, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let adopt = reader.tag_of(2, "an adoption verdict")? == 0;
    reader.end()?;
    Ok(adopt)
}

/// How a worker whose supervisor is lost exits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OrphanExit {
    /// No work: close the session (nothing to abort) and record the
    /// session idle.
    Close,
    /// Work in flight: record the session busy and exit the way a crash
    /// does, without an abort or a close, so a later supervisor resumes
    /// the work from its storage.
    Handover,
}

/// The orphan decision of the compiled Bend core (`bend/ffi_orphan.bend`,
/// the model `bend/orphan.bend`): whether a worker whose supervisor has
/// been unreachable for `absent_ms` exits now with the window `window_ms`
/// (`None`: a window past the wire's range, which never expires), and how
/// it exits with `work`. Both numbers are at most
/// [`eukhe_bend::wire::NAT_MAX`]: the caller saturates them.
pub(crate) fn orphan_decision(
    window_ms: Option<u64>,
    absent_ms: u64,
    work: Work,
) -> (bool, OrphanExit) {
    eukhe_bend::expect_core(
        eukhe_bend::Entry::Orphan,
        orphan_call(window_ms, absent_ms, work),
    )
}

fn orphan_call(
    window_ms: Option<u64>,
    absent_ms: u64,
    work: Work,
) -> Result<(bool, OrphanExit), eukhe_bend::Error> {
    let mut request = eukhe_bend::wire::Writer::new();
    match window_ms {
        Some(window_ms) => request.some().nat(window_ms),
        None => request.none(),
    };
    request.nat(absent_ms).tag(match work {
        Work::Idle => 0,
        Work::Ongoing => 1,
    });
    let reply = eukhe_bend::call(eukhe_bend::Entry::Orphan, &request.finish()?)?;
    let mut reader = eukhe_bend::wire::Reader::reply(&reply)?;
    let due = reader.bool()?;
    let exit = if reader.tag_of(2, "an orphan exit")? == 0 {
        OrphanExit::Close
    } else {
        OrphanExit::Handover
    };
    reader.end()?;
    Ok((due, exit))
}

/// The orphan exit for a worker that holds `work`: [`OrphanExit::Close`]
/// without work, [`OrphanExit::Handover`] with work (the law
/// `orphan_exit_by_work`).
pub(crate) fn orphan_exit(work: Work) -> OrphanExit {
    orphan_decision(None, 0, work).1
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The gate's, the commit's and the adoption's decisions come from the
    /// compiled core: an idle worker's quiesce closes its gate and a run
    /// start then waits; a busy answer refuses the commit; only the
    /// supervisor's build is adopted.
    #[test]
    fn the_replacement_decisions_come_from_the_compiled_core() {
        let mut gate = WorkGate::default();
        let open = gate.admits();
        let answer = gate.quiesce(Work::Idle);
        assert_eq!(
            (
                open,
                answer,
                gate.admits(),
                idle_shutdown_commits([QuiesceAnswer::Quiesced, QuiesceAnswer::Busy]),
                adopts(Some(true)),
                adopts(None),
            ),
            (true, QuiesceAnswer::Quiesced, false, false, true, false)
        );
    }
}
