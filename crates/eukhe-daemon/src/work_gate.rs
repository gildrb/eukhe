//! Whether a worker holds work, and the gate that keeps it from starting
//! new work while a supervisor replacement decides. The model is
//! bend/launcher.bend (the gate) and bend/orphan.bend (the orphan exit);
//! the laws `idle_shutdown_never_aborts` and `orphan_never_aborts_resumable`
//! (LAWS.bend, D1) prove what the supervisor and the worker build on them.
//!
//! An idle shutdown is two-phase. The supervisor asks every worker to
//! quiesce. A worker answers under its session lock: with work it answers
//! [`QuiesceAnswer::Busy`]; without work it closes its gate and answers
//! [`QuiesceAnswer::Quiesced`]. A closed gate refuses every new run, so a
//! quiesced worker stays idle. The supervisor stops the workers only when
//! every answer is `Quiesced`; otherwise it opens the gates again and
//! refuses the shutdown as busy. The client never decides.

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
    /// The worker holds work; its gate stays open.
    Busy,
}

/// Whether a new run may start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Admission {
    Open,
    /// A replacement is deciding: new work waits for it.
    Quiesced,
}

/// The gate of one worker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct WorkGate {
    admission: Admission,
}

impl Default for WorkGate {
    fn default() -> Self {
        Self {
            admission: Admission::Open,
        }
    }
}

impl WorkGate {
    /// Whether a new run may start now.
    pub(crate) fn admission(self) -> Admission {
        self.admission
    }

    /// Quiesce with the worker's `work`, read under the same lock as this
    /// call: an idle worker closes its gate, a busy one keeps it open.
    pub(crate) fn quiesce(&mut self, work: Work) -> QuiesceAnswer {
        match work {
            Work::Idle => {
                self.admission = Admission::Quiesced;
                QuiesceAnswer::Quiesced
            }
            Work::Ongoing => QuiesceAnswer::Busy,
        }
    }

    /// The replacement did not commit: new work may start again.
    pub(crate) fn release(&mut self) {
        self.admission = Admission::Open;
    }
}

/// Whether an idle shutdown commits: only when every worker quiesced.
pub(crate) fn idle_shutdown_commits(answers: impl IntoIterator<Item = QuiesceAnswer>) -> bool {
    answers
        .into_iter()
        .all(|answer| answer == QuiesceAnswer::Quiesced)
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
