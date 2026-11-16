//! The decisions of a headless run (`eukhe -p`, `--mode json`,
//! `--mode rpc`): whether it may stop waiting for the work its turn
//! started (`bend/headless_settle.bend`, entry
//! `bend/ffi_headless_settle.bend`; `laws/headless_settle.bend`), and the
//! process exit code with its cause (`bend/headless_exit.bend`, entry
//! `bend/ffi_headless_exit.bend`; `laws/headless_exit.bend`), then whether
//! that exit stands for the run's task (`bend/headless_task.bend`, entry
//! `bend/ffi_headless_task.bend`; `laws/headless_task.bend`). Rust gathers
//! the facts and acts on the answer; the rules run in the compiled core.

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, Entry, Error};

/// The facts of one settle check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SettleFacts {
    /// The main conversation runs or holds queued input.
    pub busy: bool,
    /// Running session jobs (Cell, Shell).
    pub jobs: u64,
    /// Running kernel background commands.
    pub kernel_jobs: u64,
    /// Unsettled subagents.
    pub children: u64,
    /// Unsettled workflow runs.
    pub workflow_runs: u64,
    /// Settle notices being admitted right now.
    pub wakes: u64,
    /// The pending-work read failed.
    pub unknown: bool,
    /// The stated wait limit elapsed.
    pub limit_hit: bool,
}

/// What a headless run does next.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Settle {
    /// Nothing is left: the run may stop.
    Done,
    /// Work is pending: keep waiting for it.
    Wait,
    /// Work is pending and the wait limit elapsed: stop waiting.
    GiveUp,
}

/// Whether a headless run may stop waiting. A count past the wire's
/// largest Nat is sent as that Nat: the rule reads only whether a count
/// is zero.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn settle(facts: &SettleFacts) -> Result<Settle, Error> {
    let mut request = Writer::new();
    request
        .bool(facts.busy)
        .nat(facts.jobs.min(NAT_MAX))
        .nat(facts.kernel_jobs.min(NAT_MAX))
        .nat(facts.children.min(NAT_MAX))
        .nat(facts.workflow_runs.min(NAT_MAX))
        .nat(facts.wakes.min(NAT_MAX))
        .bool(facts.unknown)
        .bool(facts.limit_hit);
    let reply = call(Entry::HeadlessSettle, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let decided = match reader.tag_of(3, "a settle decision")? {
        0 => Settle::Done,
        1 => Settle::Wait,
        _ => Settle::GiveUp,
    };
    reader.end()?;
    Ok(decided)
}

/// Why a run settled unanswered, in the closed vocabulary of the exit
/// rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Unanswered {
    ModelError,
    RunLimit,
    NoModel,
    ForcedTool,
    Faulted,
    Aborted,
    Reset,
    Stale,
    Withdrawn,
    Other,
    /// The budget refused the run's request: the run's failure is the
    /// budget refusal on its terminal entry (set by the runtime, never
    /// read from a reason).
    BudgetRefused,
}

impl Unanswered {
    /// The reason a run record names (`model_error`, `run_limit`,
    /// `no_model`, `forced_tool`, `faulted`, `aborted`, `reset`, `stale`,
    /// `withdrawn`); any other text is [`Unanswered::Other`].
    #[must_use]
    pub fn from_reason(reason: &str) -> Self {
        match reason {
            "model_error" => Unanswered::ModelError,
            "run_limit" => Unanswered::RunLimit,
            "no_model" => Unanswered::NoModel,
            "forced_tool" => Unanswered::ForcedTool,
            "faulted" => Unanswered::Faulted,
            "aborted" => Unanswered::Aborted,
            "reset" => Unanswered::Reset,
            "stale" => Unanswered::Stale,
            "withdrawn" => Unanswered::Withdrawn,
            _ => Unanswered::Other,
        }
    }

    fn tag(self) -> u32 {
        match self {
            Unanswered::ModelError => 0,
            Unanswered::RunLimit => 1,
            Unanswered::NoModel => 2,
            Unanswered::ForcedTool => 3,
            Unanswered::Faulted => 4,
            Unanswered::Aborted => 5,
            Unanswered::Reset => 6,
            Unanswered::Stale => 7,
            Unanswered::Withdrawn => 8,
            Unanswered::Other => 9,
            Unanswered::BudgetRefused => 10,
        }
    }

    fn read(reader: &mut Reader<'_>) -> Result<Self, WireError> {
        Ok(match reader.tag_of(11, "an unanswered reason")? {
            0 => Unanswered::ModelError,
            1 => Unanswered::RunLimit,
            2 => Unanswered::NoModel,
            3 => Unanswered::ForcedTool,
            4 => Unanswered::Faulted,
            5 => Unanswered::Aborted,
            6 => Unanswered::Reset,
            7 => Unanswered::Stale,
            8 => Unanswered::Withdrawn,
            9 => Unanswered::Other,
            // `tag_of` answers a tag below 11: this is 10.
            _ => Unanswered::BudgetRefused,
        })
    }
}

/// How the last run settled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunEnd {
    NoRun,
    Answered,
    Unanswered(Unanswered),
}

/// The terminal transcript entry of a headless run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Primary {
    /// No entry.
    Nothing,
    /// An assistant reply that stopped (stop, length).
    Answer,
    /// An assistant reply left unfinished (tool use, pending, deferred).
    Unfinished,
    /// An assistant reply that stopped with a provider error.
    ProviderError,
    /// An aborted assistant reply.
    Aborted,
    /// A slash command that succeeded.
    SlashOk,
    /// A slash command that failed.
    SlashFailed,
    /// A request the budget refused or stopped (its error carries the
    /// budget-refusal diagnostic).
    BudgetRefused,
}

/// How the settle wait ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Wait {
    /// Nothing ran that could wake the session.
    Quiet,
    /// The wait gave up at its limit.
    GaveUp,
    /// The wait ended at the time budget's deadline.
    BudgetDeadline,
}

/// The facts of a finished headless run.
// Each flag is an independent fact the exit rule reads (the API the
// headless runtime fills); a state machine would merge facts that hold
// together.
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExitFacts {
    /// A session command prompt failed.
    pub command_failed: bool,
    /// How the settle wait ended.
    pub wait: Wait,
    /// The last run's settlement.
    pub run: RunEnd,
    /// The terminal transcript entry.
    pub primary: Primary,
    /// A compaction failed.
    pub compaction_failed: bool,
    /// An autonomous turn failed.
    pub autonomous_failed: bool,
    /// The agent's budget phase is wrap-up or exhausted and its last
    /// reply is its final answer from the reserve, delivered.
    pub budget_answered: bool,
}

/// Why a headless run exits as it does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExitCause {
    Answered,
    CommandFailed,
    GaveUp,
    RunFailed(Unanswered),
    ProviderError,
    Aborted,
    Unfinished,
    SlashFailed,
    CompactionFailed,
    AutonomousFailed,
    /// The budget ended the run after its final answer from the reserve.
    BudgetLimited,
    /// The budget ended the run before a final answer was delivered.
    BudgetUnanswered,
}

/// The exit of a headless run: the process code and its cause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Exit {
    pub code: u8,
    pub cause: ExitCause,
}

/// The exit code of a finished headless run, and its cause.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn exit(facts: &ExitFacts) -> Result<Exit, Error> {
    let mut request = Writer::new();
    request.bool(facts.command_failed).tag(match facts.wait {
        Wait::Quiet => 0,
        Wait::GaveUp => 1,
        Wait::BudgetDeadline => 2,
    });
    match facts.run {
        RunEnd::NoRun => request.tag(0),
        RunEnd::Answered => request.tag(1),
        RunEnd::Unanswered(reason) => request.tag(2).tag(reason.tag()),
    };
    request
        .tag(match facts.primary {
            Primary::Nothing => 0,
            Primary::Answer => 1,
            Primary::Unfinished => 2,
            Primary::ProviderError => 3,
            Primary::Aborted => 4,
            Primary::SlashOk => 5,
            Primary::SlashFailed => 6,
            Primary::BudgetRefused => 7,
        })
        .bool(facts.compaction_failed)
        .bool(facts.autonomous_failed)
        .bool(facts.budget_answered);
    let reply = call(Entry::HeadlessExit, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let code = u8::try_from(reader.nat()?).map_err(|_| WireError::Malformed {
        at: 0,
        expected: "an exit code",
    })?;
    let cause = match reader.tag_of(12, "an exit cause")? {
        0 => ExitCause::Answered,
        1 => ExitCause::CommandFailed,
        2 => ExitCause::GaveUp,
        3 => ExitCause::RunFailed(Unanswered::read(&mut reader)?),
        4 => ExitCause::ProviderError,
        5 => ExitCause::Aborted,
        6 => ExitCause::Unfinished,
        7 => ExitCause::SlashFailed,
        8 => ExitCause::CompactionFailed,
        9 => ExitCause::AutonomousFailed,
        10 => ExitCause::BudgetLimited,
        // `tag_of` answers a tag below 12: this is 11.
        _ => ExitCause::BudgetUnanswered,
    };
    reader.end()?;
    Ok(Exit { code, cause })
}

impl ExitCause {
    /// The cause as the exit entry spells it (`bend/ffi_headless_exit.bend`).
    fn write(self, request: &mut Writer) {
        match self {
            ExitCause::Answered => request.tag(0),
            ExitCause::CommandFailed => request.tag(1),
            ExitCause::GaveUp => request.tag(2),
            ExitCause::RunFailed(reason) => request.tag(3).tag(reason.tag()),
            ExitCause::ProviderError => request.tag(4),
            ExitCause::Aborted => request.tag(5),
            ExitCause::Unfinished => request.tag(6),
            ExitCause::SlashFailed => request.tag(7),
            ExitCause::CompactionFailed => request.tag(8),
            ExitCause::AutonomousFailed => request.tag(9),
            ExitCause::BudgetLimited => request.tag(10),
            ExitCause::BudgetUnanswered => request.tag(11),
        };
    }
}

/// The judge's reading of a headless run's final answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Report {
    /// Not asked: the run did not answer, did not act, answered with no
    /// text, or the core has not asked yet.
    Unasked,
    /// The answer states no work of the task left.
    Done,
    /// The answer states work of the task left.
    Left,
    /// The judge gave no verdict (its request failed or was stopped, its
    /// reply was unreadable).
    Unjudged,
}

/// Whether a headless run acted: a tool call with an effect (an edit, a
/// write, a program run, a spawned child).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Activity {
    /// The run acted: its final answer is the judge's to read.
    Acted,
    /// The run only read and answered: it is never judged.
    ReadOnly,
}

/// What the exit of a headless run says of its task.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Task {
    /// The exit stands as [`exit`] decided it.
    Stands,
    /// The run answered with work left: its final answer states work
    /// left.
    Incomplete,
    /// The judge reads the run's final answer and gave no verdict on it:
    /// the run exits [`UNJUDGED_CODE`].
    Unjudged,
    /// The judge must read the run's final answer: ask it, then decide
    /// again with its reading.
    Ask,
}

/// The exit code of a headless run whose final answer the judge could not
/// read (`bend/headless_task.bend` `unjudged_code`): 0 is done, 1 a
/// failure or work left, 2 a usage error.
pub const UNJUDGED_CODE: u8 = 3;

/// The exit of a headless run's task: the process code and the task.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TaskExit {
    pub code: u8,
    pub task: Task,
}

/// Whether the exit of a headless run whose exit had cause `cause`, that
/// acted or not (`activity`) and whose final answer the judge read as
/// `report` stands for its task, and the process code: an answered run
/// that acted whose answer states work left is incomplete (exit 1); one
/// whose answer the judge gave no verdict on is unjudged
/// ([`UNJUDGED_CODE`]); one that acted and has no reading yet asks for the
/// judge ([`Task::Ask`]); a run that did not act is never judged.
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn task(cause: ExitCause, activity: Activity, report: Report) -> Result<TaskExit, Error> {
    let mut request = Writer::new();
    cause.write(&mut request);
    request
        .bool(match activity {
            Activity::Acted => true,
            Activity::ReadOnly => false,
        })
        .tag(match report {
            Report::Unasked => 0,
            Report::Done => 1,
            Report::Left => 2,
            Report::Unjudged => 3,
        });
    let reply = call(Entry::HeadlessTask, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let code = u8::try_from(reader.nat()?).map_err(|_| WireError::Malformed {
        at: 0,
        expected: "an exit code",
    })?;
    let task = match reader.tag_of(4, "a task")? {
        0 => Task::Stands,
        1 => Task::Incomplete,
        2 => Task::Unjudged,
        // `tag_of` answers a tag below 4: this is 3.
        _ => Task::Ask,
    };
    reader.end()?;
    Ok(TaskExit { code, task })
}

#[cfg(test)]
mod tests {
    use super::*;

    const QUIET: SettleFacts = SettleFacts {
        busy: false,
        jobs: 0,
        kernel_jobs: 0,
        children: 0,
        workflow_runs: 0,
        wakes: 0,
        unknown: false,
        limit_hit: false,
    };

    /// Nothing left: done, at the limit or not.
    #[test]
    fn a_quiet_run_is_done() {
        assert_eq!(settle(&QUIET).unwrap(), Settle::Done);
        let at_limit = SettleFacts {
            limit_hit: true,
            ..QUIET
        };
        assert_eq!(settle(&at_limit).unwrap(), Settle::Done);
    }

    /// Each kind of pending work keeps the run waiting below the limit
    /// and gives up at it.
    #[test]
    fn pending_work_waits_then_gives_up() {
        let pending = [
            SettleFacts {
                busy: true,
                ..QUIET
            },
            SettleFacts { jobs: 1, ..QUIET },
            SettleFacts {
                kernel_jobs: 2,
                ..QUIET
            },
            SettleFacts {
                children: 3,
                ..QUIET
            },
            SettleFacts {
                workflow_runs: 1,
                ..QUIET
            },
            SettleFacts { wakes: 1, ..QUIET },
            SettleFacts {
                unknown: true,
                ..QUIET
            },
            SettleFacts {
                jobs: u64::MAX,
                ..QUIET
            },
        ];
        for facts in pending {
            assert_eq!(settle(&facts).unwrap(), Settle::Wait, "{facts:?}");
            let at_limit = SettleFacts {
                limit_hit: true,
                ..facts
            };
            assert_eq!(settle(&at_limit).unwrap(), Settle::GiveUp, "{facts:?}");
        }
    }

    const ANSWERED: ExitFacts = ExitFacts {
        command_failed: false,
        wait: Wait::Quiet,
        run: RunEnd::Answered,
        primary: Primary::Answer,
        compaction_failed: false,
        autonomous_failed: false,
        budget_answered: false,
    };

    fn failed(cause: ExitCause) -> Exit {
        Exit { code: 1, cause }
    }

    #[test]
    fn an_answered_run_exits_zero() {
        assert_eq!(
            exit(&ANSWERED).unwrap(),
            Exit {
                code: 0,
                cause: ExitCause::Answered
            }
        );
        let slash = ExitFacts {
            run: RunEnd::NoRun,
            primary: Primary::SlashOk,
            ..ANSWERED
        };
        assert_eq!(exit(&slash).unwrap().code, 0);
    }

    #[test]
    fn a_failed_command_exits_one_before_everything() {
        let facts = ExitFacts {
            command_failed: true,
            wait: Wait::GaveUp,
            run: RunEnd::Unanswered(Unanswered::ModelError),
            primary: Primary::ProviderError,
            compaction_failed: true,
            autonomous_failed: true,
            budget_answered: true,
        };
        assert_eq!(exit(&facts).unwrap(), failed(ExitCause::CommandFailed));
    }

    #[test]
    fn a_give_up_exits_one_before_the_run() {
        let facts = ExitFacts {
            wait: Wait::GaveUp,
            run: RunEnd::Unanswered(Unanswered::Faulted),
            budget_answered: true,
            ..ANSWERED
        };
        assert_eq!(exit(&facts).unwrap(), failed(ExitCause::GaveUp));
    }

    #[test]
    fn every_run_failure_exits_one_before_the_transcript() {
        for reason in [
            Unanswered::ModelError,
            Unanswered::RunLimit,
            Unanswered::NoModel,
            Unanswered::ForcedTool,
            Unanswered::Faulted,
            Unanswered::Aborted,
            Unanswered::Other,
        ] {
            let facts = ExitFacts {
                run: RunEnd::Unanswered(reason),
                primary: Primary::Unfinished,
                ..ANSWERED
            };
            assert_eq!(exit(&facts).unwrap(), failed(ExitCause::RunFailed(reason)));
        }
    }

    /// A reset, a stale run and a withdrawn input are no failure of the
    /// run: the transcript decides.
    #[test]
    fn a_reset_stale_or_withdrawn_run_falls_through() {
        for reason in [Unanswered::Reset, Unanswered::Stale, Unanswered::Withdrawn] {
            let clean = ExitFacts {
                run: RunEnd::Unanswered(reason),
                ..ANSWERED
            };
            assert_eq!(exit(&clean).unwrap().code, 0);
            let aborted = ExitFacts {
                primary: Primary::Aborted,
                ..clean
            };
            assert_eq!(exit(&aborted).unwrap(), failed(ExitCause::Aborted));
        }
    }

    #[test]
    fn a_failed_transcript_entry_exits_one_before_the_flags() {
        for (primary, cause) in [
            (Primary::ProviderError, ExitCause::ProviderError),
            (Primary::Aborted, ExitCause::Aborted),
            (Primary::Unfinished, ExitCause::Unfinished),
            (Primary::SlashFailed, ExitCause::SlashFailed),
        ] {
            let facts = ExitFacts {
                primary,
                compaction_failed: true,
                ..ANSWERED
            };
            assert_eq!(exit(&facts).unwrap(), failed(cause));
        }
    }

    #[test]
    fn a_failed_compaction_exits_one_before_an_autonomous_failure() {
        let facts = ExitFacts {
            compaction_failed: true,
            autonomous_failed: true,
            ..ANSWERED
        };
        assert_eq!(exit(&facts).unwrap(), failed(ExitCause::CompactionFailed));
    }

    #[test]
    fn a_failed_autonomous_turn_exits_one() {
        let facts = ExitFacts {
            primary: Primary::Nothing,
            autonomous_failed: true,
            ..ANSWERED
        };
        assert_eq!(exit(&facts).unwrap(), failed(ExitCause::AutonomousFailed));
    }

    /// The budget ended the run after its final answer from the reserve:
    /// the wait at the deadline, a run and a terminal entry the budget
    /// refused are no failure, and the run is budget-limited. Without that
    /// answer each of them exits 1 as budget-unanswered.
    #[test]
    fn a_used_up_budget_exits_by_its_final_answer() {
        let deadline = ExitFacts {
            wait: Wait::BudgetDeadline,
            ..ANSWERED
        };
        let refused = ExitFacts {
            run: RunEnd::Unanswered(Unanswered::BudgetRefused),
            primary: Primary::BudgetRefused,
            ..ANSWERED
        };
        let answered = |facts: ExitFacts| ExitFacts {
            budget_answered: true,
            ..facts
        };
        let limited = Exit {
            code: 0,
            cause: ExitCause::BudgetLimited,
        };
        assert_eq!(
            [
                exit(&answered(deadline)).unwrap(),
                exit(&answered(refused)).unwrap(),
                exit(&answered(ANSWERED)).unwrap(),
                exit(&deadline).unwrap(),
                exit(&refused).unwrap(),
            ],
            [
                limited,
                limited,
                limited,
                failed(ExitCause::BudgetUnanswered),
                failed(ExitCause::BudgetUnanswered),
            ]
        );
    }

    /// The final answer from the reserve hides no other failure.
    #[test]
    fn a_final_answer_from_the_reserve_keeps_other_failures() {
        let at_deadline = ExitFacts {
            wait: Wait::BudgetDeadline,
            budget_answered: true,
            ..ANSWERED
        };
        assert_eq!(
            [
                exit(&ExitFacts {
                    run: RunEnd::Unanswered(Unanswered::ModelError),
                    ..at_deadline
                })
                .unwrap(),
                exit(&ExitFacts {
                    primary: Primary::ProviderError,
                    ..at_deadline
                })
                .unwrap(),
                exit(&ExitFacts {
                    compaction_failed: true,
                    ..at_deadline
                })
                .unwrap(),
            ],
            [
                failed(ExitCause::RunFailed(Unanswered::ModelError)),
                failed(ExitCause::ProviderError),
                failed(ExitCause::CompactionFailed),
            ]
        );
    }

    /// An answered run that acted and whose final answer states work left
    /// did not finish its task: it exits 1 as incomplete. An acted answer
    /// not read yet asks for the judge; one the judge gave no verdict on
    /// exits 3. A run that did not act is never judged; without work left,
    /// or with any other cause, the exit stands.
    #[test]
    fn an_answer_with_work_left_is_incomplete() {
        let incomplete = TaskExit {
            code: 1,
            task: Task::Incomplete,
        };
        let stands = |code| TaskExit {
            code,
            task: Task::Stands,
        };
        let three = |task| TaskExit {
            code: UNJUDGED_CODE,
            task,
        };
        let answered = |activity, report| task(ExitCause::Answered, activity, report).unwrap();
        let acted = |report| answered(Activity::Acted, report);
        assert_eq!(
            [
                acted(Report::Left),
                acted(Report::Unjudged),
                acted(Report::Unasked),
                acted(Report::Done),
                answered(Activity::ReadOnly, Report::Unasked),
                answered(Activity::ReadOnly, Report::Left),
                task(ExitCause::BudgetLimited, Activity::Acted, Report::Left).unwrap(),
                task(
                    ExitCause::RunFailed(Unanswered::Stale),
                    Activity::Acted,
                    Report::Left
                )
                .unwrap(),
                task(ExitCause::GaveUp, Activity::Acted, Report::Unasked).unwrap(),
            ],
            [
                incomplete,
                three(Task::Unjudged),
                three(Task::Ask),
                stands(0),
                stands(0),
                stands(0),
                stands(0),
                stands(1),
                stands(1),
            ]
        );
    }

    /// Every cause the exit rule answers reaches the task rule intact: the
    /// code of a standing exit is the exit's own.
    #[test]
    fn every_cause_keeps_its_code_without_work_left() {
        let reasons = [
            Unanswered::ModelError,
            Unanswered::RunLimit,
            Unanswered::NoModel,
            Unanswered::ForcedTool,
            Unanswered::Faulted,
            Unanswered::Aborted,
            Unanswered::Reset,
            Unanswered::Stale,
            Unanswered::Withdrawn,
            Unanswered::Other,
            Unanswered::BudgetRefused,
        ];
        let causes = [
            (ExitCause::Answered, 0),
            (ExitCause::CommandFailed, 1),
            (ExitCause::GaveUp, 1),
            (ExitCause::ProviderError, 1),
            (ExitCause::Aborted, 1),
            (ExitCause::Unfinished, 1),
            (ExitCause::SlashFailed, 1),
            (ExitCause::CompactionFailed, 1),
            (ExitCause::AutonomousFailed, 1),
            (ExitCause::BudgetLimited, 0),
            (ExitCause::BudgetUnanswered, 1),
        ]
        .into_iter()
        .chain(reasons.map(|reason| (ExitCause::RunFailed(reason), 1)));
        for (cause, code) in causes {
            assert_eq!(
                task(cause, Activity::Acted, Report::Done).unwrap(),
                TaskExit {
                    code,
                    task: Task::Stands
                },
                "{cause:?}"
            );
        }
    }

    #[test]
    fn reasons_map_to_the_closed_vocabulary() {
        let read: Vec<Unanswered> = [
            "model_error",
            "run_limit",
            "no_model",
            "forced_tool",
            "faulted",
            "aborted",
            "reset",
            "stale",
            "withdrawn",
            "provider_down",
        ]
        .into_iter()
        .map(Unanswered::from_reason)
        .collect();
        assert_eq!(
            read,
            [
                Unanswered::ModelError,
                Unanswered::RunLimit,
                Unanswered::NoModel,
                Unanswered::ForcedTool,
                Unanswered::Faulted,
                Unanswered::Aborted,
                Unanswered::Reset,
                Unanswered::Stale,
                Unanswered::Withdrawn,
                Unanswered::Other,
            ]
        );
    }
}
