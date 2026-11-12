//! The loop on an open eukhe session with a faux model: one test per
//! requirement of spec/README.md L1-L9 that Rust carries out (the
//! decisions themselves are proven in `laws/loop/`). The condition
//! commands are real shell commands run in the session cwd.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_ai::providers::faux::{
    faux_assistant_message, FauxAssistantMessageOptions, FauxResponseStep,
};
use eukhe_ai::providers::faux_script::{
    create_faux_script_models, parse_faux_script, FauxScriptProvider,
};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::{UserData, USER_ENTRY};
use eukhe_durable::harness::types::{ConversationAbortOptions, InputSubmissionDraft, WhenBusy};
use eukhe_durable::harness::ConversationEntryQuery;
use eukhe_durable::types::EntryData;
use eukhe_types::budget::BudgetLimits;
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::loop_mode::{
    LoopCheck, LoopCondition, LoopEnd, LoopEvidence, LoopLimit, LoopPhase, LoopState, LoopStatus,
    LoopVerdict,
};
use eukhe_types::pi_ai::{Message, StopReason, UserContent};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::json;
use tokio::sync::watch;

use super::{
    hold_loop_for_compaction, loop_status, resume_loop_after_compaction, watch_loop_updates,
    LOOP_MODE_DOC, LOOP_NOTICE_CUSTOM_TYPE,
};
use crate::durable::entries::CUSTOM_ENTRY;
use crate::durable::goals::read_doc;
use crate::durable::session_commands::{classify_session_command, execute_session_command};
use crate::durable::{open_session, EukheSession, ModelRequest, SessionConfig, SessionStorage};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// A condition command that fails (exit 1) until its `n`th run, counting
/// its runs in the file `runs` of the session cwd.
fn nth_run(n: u32) -> String {
    format!("r=$(cat runs 2>/dev/null || echo 0); r=$((r+1)); echo $r > runs; test $r -ge {n}")
}

fn answer(text: &str) -> FauxResponseStep {
    faux_assistant_message(text, FauxAssistantMessageOptions::default()).into()
}

/// A response whose request fails at the provider.
fn failure() -> FauxResponseStep {
    faux_assistant_message(
        "",
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Error),
            error_message: Some("provider exploded".to_owned()),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

/// A response that arrives once `release` is sent (or never, when the
/// request is cancelled first); `reached` resolves once it is requested.
fn gated(text: &str) -> (FauxResponseStep, watch::Receiver<bool>, watch::Sender<bool>) {
    let (reached, reached_rx) = watch::channel(false);
    let (release, released) = watch::channel(false);
    let text = text.to_owned();
    let step = FauxResponseStep::Factory(Arc::new(move |_, options, _, _| {
        reached.send_replace(true);
        let signal = options.and_then(|options| options.stream.request.signal.clone());
        let mut released = released.clone();
        let text = text.clone();
        let pending: BoxFuture<'static, _> = async move {
            let open = async {
                // A dropped sender never releases: wait for the cancel.
                if released.wait_for(|open| *open).await.is_err() {
                    futures::future::pending::<()>().await;
                }
            };
            if let Some(signal) = signal {
                tokio::select! {
                    () = open => Ok(faux_assistant_message(
                        text.as_str(),
                        FauxAssistantMessageOptions::default(),
                    )),
                    cancelled = signal.cancelled() => Err(cancelled),
                }
            } else {
                open.await;
                Ok(faux_assistant_message(
                    text.as_str(),
                    FauxAssistantMessageOptions::default(),
                ))
            }
        }
        .boxed();
        pending
    }));
    (step, reached_rx, release)
}

struct Lab {
    dir: tempfile::TempDir,
    session: EukheSession,
    provider: FauxScriptProvider,
}

fn project(dir: &Path) -> PathBuf {
    dir.join("project")
}

/// Open (or reopen) the session of `dir` on a fresh faux model answering
/// `responses` in order.
async fn open_in(
    dir: &Path,
    storage: SessionStorage,
    responses: Vec<FauxResponseStep>,
) -> (EukheSession, FauxScriptProvider) {
    let agent_dir = dir.join("agent");
    let cwd = project(dir);
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&cwd).expect("cwd");
    // A failed request ends its run at once: the loop counts failed turns,
    // the provider retries are not under test.
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({ "retry": { "enabled": false } }).to_string(),
    )
    .expect("settings");
    let script = parse_faux_script(&json!({ "responses": [] }).to_string()).expect("the script");
    let (models, provider) = create_faux_script_models(script);
    provider.set_responses(responses);
    let mut config = SessionConfig::new(
        &agent_dir,
        &cwd,
        "0192a000-0000-7000-8000-0000000000d1",
        storage,
    );
    config.models = Some(models);
    config.model = Some(ModelRequest {
        provider: Some("faux".to_owned()),
        pattern: "faux-1".to_owned(),
    });
    let session = open_session(config, cx()).await.expect("the session opens");
    (session, provider)
}

async fn open(responses: Vec<FauxResponseStep>) -> Lab {
    let dir = tempfile::tempdir().expect("tempdir");
    let (session, provider) = open_in(dir.path(), SessionStorage::Memory, responses).await;
    Lab {
        dir,
        session,
        provider,
    }
}

impl Lab {
    /// Run the session command `text`; its result row's text.
    async fn run(&self, text: &str) -> String {
        let command = classify_session_command(text).expect("a session command");
        let outcome =
            execute_session_command(&self.session, &self.session.main(), &command, cx()).await;
        if let Some(error) = outcome.error {
            return format!("Command failed: {error}");
        }
        self.rows(eukhe_types::slash_commands::SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE)
            .await
            .pop()
            .expect("a result row")
    }

    async fn idle(&self) {
        self.session
            .harness()
            .wait_for_idle(cx())
            .await
            .expect("idle");
    }

    async fn status(&self) -> LoopStatus {
        loop_status(self.session.harness(), self.session.main().id(), cx())
            .await
            .expect("the loop status")
    }

    /// Wait until the loop's status meets `ready`.
    async fn until(&self, ready: impl Fn(&LoopStatus) -> bool) -> LoopStatus {
        let mut updates =
            watch_loop_updates(self.session.harness(), self.session.main().id(), cx())
                .expect("the loop watch");
        loop {
            let status = updates.next().await.expect("a loop update");
            if ready(&status) {
                return status;
            }
        }
    }

    /// The user entries, oldest first: each text with the loop iteration
    /// that sent it (`None`: the user's own).
    async fn sent(&self) -> Vec<(String, Option<u64>)> {
        let page = self
            .session
            .main()
            .entries(ConversationEntryQuery::default(), 1000, None, cx())
            .await
            .expect("entries");
        page.items
            .into_iter()
            .rev()
            .filter(|entry| entry.kind == USER_ENTRY.kind())
            .filter_map(|entry| {
                let origin = UserData::decode(entry.data.as_ref())
                    .expect("origin")
                    .origin;
                let iteration = match origin {
                    InputOrigin::Loop { iteration } => Some(iteration),
                    InputOrigin::User => None,
                    other => panic!("an unexpected input: {other:?}"),
                };
                match entry.model.as_ref()?.first()? {
                    Message::User(message) => match &message.content {
                        UserContent::Text(text) => Some((text.clone(), iteration)),
                        UserContent::Blocks(_) => None,
                    },
                    _ => None,
                }
            })
            .collect()
    }

    /// The texts of the custom rows of `custom_type`, oldest first.
    async fn rows(&self, custom_type: &str) -> Vec<String> {
        let page = self
            .session
            .main()
            .entries(ConversationEntryQuery::default(), 1000, None, cx())
            .await
            .expect("entries");
        page.items
            .into_iter()
            .rev()
            .filter_map(|entry| CUSTOM_ENTRY.narrow(entry).expect("narrow"))
            .map(|entry| entry.data().clone())
            .filter(|data| data.custom_type == custom_type)
            .filter_map(|data| match data.content {
                Some(UserContent::Text(text)) => Some(text),
                Some(UserContent::Blocks(_)) | None => None,
            })
            .collect()
    }

    async fn notices(&self) -> Vec<String> {
        self.rows(LOOP_NOTICE_CUSTOM_TYPE).await
    }

    async fn close(self) {
        self.session.close(cx()).await.expect("close");
    }
}

fn sends(text: &str, iterations: &[u64]) -> Vec<(String, Option<u64>)> {
    iterations
        .iter()
        .map(|iteration| (text.to_owned(), Some(*iteration)))
        .collect()
}

#[allow(clippy::unnecessary_wraps)]
fn until(command: &str) -> Option<LoopCondition> {
    Some(LoopCondition {
        command: command.to_owned(),
        until: true,
    })
}

/// L1-L3: `/loop --until` sends its prompt again after every turn until
/// the command succeeds: three turns for a condition met at its third
/// check, the same text each time, one end row, the evidence kept.
#[tokio::test]
async fn a_loop_repeats_until_its_condition_command_succeeds() {
    let lab = open(vec![
        answer("one"),
        answer("two"),
        answer("three"),
        answer("no"),
    ])
    .await;
    let check = nth_run(3);
    let shown = lab.run(&format!("/loop 10 --until '{check}' fix it")).await;
    assert!(
        shown.starts_with("Loop mode enabled. Limited to 10 iterations. 10 of 10 iterations remaining. Continuing until `"),
        "{shown}"
    );
    assert!(
        shown.ends_with(
            " Repeating it after each turn. Esc suspends the ongoing loop; /loop again to disable."
        ),
        "{shown}"
    );
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("fix it", &[1, 2, 3]));
    let notices = lab.notices().await;
    assert_eq!(notices.len(), 1, "{notices:?}");
    assert!(
        notices[0].starts_with("Loop condition `")
            && notices[0].ends_with("` is now satisfied. Loop mode disabled."),
        "{notices:?}"
    );
    let status = lab.status().await;
    assert_eq!(
        (status.state, status.verdict, status.limit),
        (
            LoopState {
                phase: LoopPhase::Ended {
                    end: LoopEnd::Satisfied
                },
                iteration: 3,
                remaining: Some(8),
                deadline_ms: None,
                condition: until(&check),
                prompt: "fix it".to_owned(),
                failures: 0,
                last_check: Some(LoopCheck {
                    iteration: 3,
                    evidence: LoopEvidence::Exited { code: 0 },
                }),
            },
            Some(LoopVerdict::Confirmed),
            Some(LoopLimit::Iterations { iterations: 10 }),
        )
    );
    // The condition command ran once per turn, and not before the first.
    assert_eq!(
        std::fs::read_to_string(project(lab.dir.path()).join("runs"))
            .expect("runs")
            .trim(),
        "3"
    );
    assert_eq!(lab.provider.get_pending_response_count(), 1);
    lab.close().await;
}

/// L4: a count bounds the automatic iterations: `/loop 2` sends the prompt
/// twice more after the first turn, then ends as out of turns.
#[tokio::test]
async fn a_count_bounds_the_automatic_iterations() {
    let lab = open(vec![answer("1"), answer("2"), answer("3"), answer("no")]).await;
    lab.run("/loop 2 go").await;
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("go", &[1, 2, 3]));
    assert_eq!(
        lab.notices().await,
        vec!["Loop limit reached. Loop mode disabled.".to_owned()]
    );
    let status = lab.status().await;
    assert_eq!(
        (status.state.phase, status.state.remaining, status.verdict),
        (
            LoopPhase::Ended {
                end: LoopEnd::OutOfTurns
            },
            Some(0),
            None
        )
    );
    lab.close().await;
}

/// L4: the session's budget decides whether it funds the next iteration:
/// with a budget of three model requests, `/loop 10 go` runs three turns
/// (one request each) and then, long before its count, ends as out of
/// budget: no further request reaches the provider.
#[tokio::test]
async fn a_loop_stops_when_the_budget_funds_no_further_turn() {
    let lab = open(vec![
        answer("1"),
        answer("2"),
        answer("3"),
        answer("4"),
        answer("no"),
    ])
    .await;
    lab.session
        .budget()
        .set(BudgetLimits {
            requests: Some(3),
            ..BudgetLimits::default()
        })
        .expect("the budget is set");
    lab.run("/loop 10 go").await;
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("go", &[1, 2, 3]));
    assert_eq!(
        lab.notices().await,
        vec!["Loop stopped: the budget funds no further turn. Loop mode disabled.".to_owned()]
    );
    let status = lab.status().await;
    assert_eq!(
        status.state.phase,
        LoopPhase::Ended {
            end: LoopEnd::OutOfBudget
        }
    );
    // No fourth request reached the provider.
    assert_eq!(lab.provider.get_pending_response_count(), 2);
    lab.close().await;
}

/// L1, L2: `/loop` with no prompt waits; the next prompt the user sends
/// becomes the loop's prompt and is the first iteration.
#[tokio::test]
async fn an_armed_loop_repeats_the_next_prompt_of_the_user() {
    let lab = open(vec![answer("1"), answer("2"), answer("no")]).await;
    let shown = lab.run("/loop 1").await;
    assert_eq!(
        shown,
        "Loop mode enabled. Limited to 1 iteration. 1 of 1 iteration remaining. Your next prompt will repeat after each turn. Esc suspends the ongoing loop; /loop again to disable."
    );
    assert_eq!(lab.status().await.state.phase, LoopPhase::Armed);
    lab.session
        .main()
        .submit(InputSubmissionDraft::new("polish it"), cx())
        .await
        .expect("submit");
    lab.idle().await;
    assert_eq!(
        lab.sent().await,
        vec![
            ("polish it".to_owned(), None),
            ("polish it".to_owned(), Some(2))
        ]
    );
    assert_eq!(
        lab.status().await.state.phase,
        LoopPhase::Ended {
            end: LoopEnd::OutOfTurns
        }
    );
    lab.close().await;
}

/// L3: a condition command that breaks (a status above 1) ends the loop
/// as a broken check, with the broken-check line; it is never read as
/// "not yet".
#[tokio::test]
async fn a_broken_condition_ends_the_loop() {
    let lab = open(vec![answer("1"), answer("no")]).await;
    lab.run("/loop --until 'echo boom; exit 3' go").await;
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("go", &[1]));
    assert_eq!(
        lab.notices().await,
        vec![
            "Loop condition `echo boom; exit 3` failed (exit 3): boom. Loop mode disabled."
                .to_owned()
        ]
    );
    let status = lab.status().await;
    assert_eq!(
        (status.state.phase, status.verdict),
        (
            LoopPhase::Ended {
                end: LoopEnd::CheckBroke
            },
            Some(LoopVerdict::Broken)
        )
    );
    lab.close().await;
}

/// L3: `--while` goes on while the command succeeds and stops once it
/// fails, with the while-condition end line.
#[tokio::test]
async fn a_while_loop_stops_once_its_command_fails() {
    let lab = open(vec![answer("1"), answer("2"), answer("no")]).await;
    // Succeeds at its first run, fails (exit 1) from the second.
    let check = "r=$(cat runs 2>/dev/null || echo 0); r=$((r+1)); echo $r > runs; test $r -lt 2";
    lab.run(&format!("/loop --while '{check}' go")).await;
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("go", &[1, 2]));
    let notices = lab.notices().await;
    assert!(
        notices.len() == 1 && notices[0].ends_with("` no longer holds. Loop mode disabled."),
        "{notices:?}"
    );
    lab.close().await;
}

/// L1, L6: `/loop` while a loop is on ends it, once; the turn in flight
/// runs to its end and nothing follows it; `/loop --stop` then finds no
/// loop and starts none.
#[tokio::test]
async fn loop_again_ends_the_loop_once() {
    let (first, mut reached, release) = gated("1");
    let lab = open(vec![first, answer("no")]).await;
    lab.run("/loop go").await;
    reached
        .wait_for(|reached| *reached)
        .await
        .expect("the turn runs");
    assert_eq!(lab.run("/loop 5 other").await, "Loop mode disabled.");
    release.send_replace(true);
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("go", &[1]));
    assert_eq!(
        lab.status().await.state.phase,
        LoopPhase::Ended {
            end: LoopEnd::Stopped
        }
    );
    assert_eq!(lab.run("/loop --stop").await, "Loop mode is not enabled.");
    // The command reports its own end: no second end row.
    assert_eq!(lab.notices().await, Vec::<String>::new());
    assert_eq!(lab.provider.get_pending_response_count(), 1);
    lab.close().await;
}

/// L5: an abort while a turn of the loop runs pauses the loop: nothing
/// starts by itself; the next prompt the user sends becomes the loop's
/// prompt and the loop goes on inside its count.
#[tokio::test]
async fn an_abort_in_a_turn_pauses_the_loop_until_the_user_prompts() {
    let (stuck, mut reached, _release) = gated("never");
    let lab = open(vec![stuck, answer("a"), answer("b"), answer("no")]).await;
    lab.run("/loop 1 go").await;
    reached
        .wait_for(|reached| *reached)
        .await
        .expect("the turn runs");
    lab.session
        .main()
        .abort(ConversationAbortOptions::default(), cx())
        .await
        .expect("abort");
    let paused = lab
        .until(|status| status.state.phase == LoopPhase::Paused)
        .await;
    assert_eq!(
        (paused.state.prompt.as_str(), paused.state.remaining),
        ("", Some(1))
    );
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("go", &[1]));
    lab.session
        .main()
        .submit(InputSubmissionDraft::new("new plan"), cx())
        .await
        .expect("submit");
    lab.idle().await;
    assert_eq!(
        lab.sent().await,
        vec![
            ("go".to_owned(), Some(1)),
            ("new plan".to_owned(), None),
            ("new plan".to_owned(), Some(3)),
        ]
    );
    assert_eq!(
        lab.notices().await,
        vec!["Loop limit reached. Loop mode disabled.".to_owned()]
    );
    lab.close().await;
}

/// L5: an abort while the condition command runs pauses the loop too:
/// the command's late answer starts nothing.
#[tokio::test]
async fn an_abort_in_the_check_pauses_the_loop() {
    let lab = open(vec![answer("1"), answer("no")]).await;
    lab.run("/loop --until 'sleep 20' go").await;
    lab.until(|status| status.state.phase == LoopPhase::Judging)
        .await;
    lab.session
        .main()
        .abort(ConversationAbortOptions::default(), cx())
        .await
        .expect("abort");
    lab.until(|status| status.state.phase == LoopPhase::Paused)
        .await;
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("go", &[1]));
    assert_eq!(lab.provider.get_pending_response_count(), 1);
    lab.close().await;
}

/// L4: a failed turn does not end the loop, three in a row do: the loop
/// sends its prompt again after the first and the second failure and
/// gives up at the third.
#[tokio::test]
async fn three_failed_turns_in_a_row_end_the_loop() {
    let lab = open(vec![failure(), failure(), failure(), answer("no")]).await;
    lab.run("/loop go").await;
    let ended = lab
        .until(|status| matches!(status.state.phase, LoopPhase::Ended { .. }))
        .await;
    assert_eq!(
        (
            ended.state.phase,
            ended.state.failures,
            ended.state.iteration
        ),
        (
            LoopPhase::Ended {
                end: LoopEnd::TurnsFailed
            },
            3,
            3
        )
    );
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("go", &[1, 2, 3]));
    assert_eq!(
        lab.notices().await,
        vec!["Loop stopped: 3 turns failed in a row. Loop mode disabled.".to_owned()]
    );
    assert_eq!(lab.provider.get_pending_response_count(), 1);
    lab.close().await;
}

/// L8: a message the user queues while a turn of the loop runs is not
/// lost and not overtaken: it runs before the next iteration, and the
/// loop keeps its own prompt.
#[tokio::test]
async fn a_queued_user_message_runs_before_the_next_iteration() {
    let (first, mut reached, release) = gated("1");
    let lab = open(vec![
        first,
        answer("2"),
        answer("3"),
        answer("4"),
        answer("no"),
    ])
    .await;
    lab.run("/loop 2 go").await;
    reached
        .wait_for(|reached| *reached)
        .await
        .expect("the turn runs");
    lab.session
        .main()
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text("also this".to_owned()),
                when_busy: Some(WhenBusy::FollowUp),
                origin: InputOrigin::User,
                entry: None,
            },
            cx(),
        )
        .await
        .expect("queued");
    release.send_replace(true);
    lab.idle().await;
    assert_eq!(
        lab.sent().await,
        vec![
            ("go".to_owned(), Some(1)),
            ("also this".to_owned(), None),
            ("go".to_owned(), Some(2)),
            ("go".to_owned(), Some(3)),
        ]
    );
    assert_eq!(
        lab.status().await.state.phase,
        LoopPhase::Ended {
            end: LoopEnd::OutOfTurns
        }
    );
    lab.close().await;
}

/// L7: a session that closes with iteration 2 in flight (a worker crash)
/// reopens with the same loop at the same iteration: the turn in flight
/// resumes, its prompt is not sent again, and the loop runs on to its
/// confirmed end.
#[tokio::test]
async fn a_loop_resumes_at_the_same_iteration_after_a_crash() {
    let dir = tempfile::tempdir().expect("tempdir");
    let storage = || SessionStorage::Jsonl {
        dir: dir.path().join("session"),
        fsync: true,
    };
    let check = nth_run(3);
    let (stuck, mut reached, _release) = gated("never");
    let (session, provider) = open_in(dir.path(), storage(), vec![answer("one"), stuck]).await;
    let lab = Lab {
        dir: tempfile::tempdir().expect("tempdir"),
        session,
        provider,
    };
    lab.run(&format!("/loop 10 --until '{check}' fix it")).await;
    reached
        .wait_for(|reached| *reached)
        .await
        .expect("iteration 2 runs");
    let before = lab.status().await;
    assert_eq!(
        (before.state.phase, before.state.iteration, before.verdict),
        (LoopPhase::Turn, 2, Some(LoopVerdict::Refuted))
    );
    assert_eq!(lab.sent().await, sends("fix it", &[1, 2]));
    // The crash: the session closes with the run in flight.
    lab.session.close(cx()).await.expect("close");

    let (session, provider) = open_in(
        dir.path(),
        storage(),
        vec![answer("two"), answer("three"), answer("no")],
    )
    .await;
    let lab = Lab {
        dir: tempfile::tempdir().expect("tempdir"),
        session,
        provider,
    };
    assert_eq!(lab.status().await, before);
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("fix it", &[1, 2, 3]));
    let status = lab.status().await;
    assert_eq!(
        (
            status.state.phase,
            status.state.iteration,
            status.state.condition,
            status.state.remaining
        ),
        (
            LoopPhase::Ended {
                end: LoopEnd::Satisfied
            },
            3,
            until(&check),
            Some(8)
        )
    );
    assert_eq!(lab.notices().await.len(), 1);
    assert_eq!(lab.provider.get_pending_response_count(), 1);
    lab.close().await;
}

/// L7: a session that closes while the condition command runs reopens
/// judging the same iteration: the check runs again and no iteration is
/// repeated. The check runs at the final answer, before the Harness
/// commits that answer, so the resumed generation asks the model for it
/// once more (the one request this crash costs; no tool runs again).
#[tokio::test]
async fn a_crash_in_the_check_runs_the_check_again() {
    let dir = tempfile::tempdir().expect("tempdir");
    let storage = || SessionStorage::Jsonl {
        dir: dir.path().join("session"),
        fsync: true,
    };
    // Waits for the file `go`, then succeeds.
    let check = "while [ ! -f go ]; do sleep 0.05; done";
    let (session, provider) = open_in(dir.path(), storage(), vec![answer("one")]).await;
    let lab = Lab {
        dir: tempfile::tempdir().expect("tempdir"),
        session,
        provider,
    };
    lab.run(&format!("/loop --until '{check}' fix it")).await;
    let before = lab
        .until(|status| status.state.phase == LoopPhase::Judging)
        .await;
    lab.session.close(cx()).await.expect("close");

    std::fs::write(project(dir.path()).join("go"), "").expect("go");
    let (session, provider) = open_in(
        dir.path(),
        storage(),
        vec![answer("one again"), answer("no")],
    )
    .await;
    let lab = Lab {
        dir: tempfile::tempdir().expect("tempdir"),
        session,
        provider,
    };
    assert_eq!(lab.status().await.state, before.state);
    let ended = lab
        .until(|status| matches!(status.state.phase, LoopPhase::Ended { .. }))
        .await;
    assert_eq!(
        (ended.state.phase, ended.state.iteration),
        (
            LoopPhase::Ended {
                end: LoopEnd::Satisfied
            },
            1
        )
    );
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("fix it", &[1]));
    assert_eq!(lab.provider.get_pending_response_count(), 1);
    lab.close().await;
}

/// L9: while the loop runs, its status says why: the iteration in
/// flight, what is left, the condition, and the last evidence read with
/// its verdict; `/loop --status` spells it.
#[tokio::test]
async fn the_status_says_why_the_loop_still_runs() {
    let (stuck, mut reached, release) = gated("2");
    let lab = open(vec![answer("1"), stuck, answer("no")]).await;
    lab.run("/loop 5 --until 'test -f done' fix it").await;
    reached
        .wait_for(|reached| *reached)
        .await
        .expect("iteration 2 runs");
    let status = lab.status().await;
    assert_eq!(
        (status.state.clone(), status.verdict),
        (
            LoopState {
                phase: LoopPhase::Turn,
                iteration: 2,
                remaining: Some(4),
                deadline_ms: None,
                condition: until("test -f done"),
                prompt: "fix it".to_owned(),
                failures: 0,
                last_check: Some(LoopCheck {
                    iteration: 1,
                    evidence: LoopEvidence::Exited { code: 1 },
                }),
            },
            Some(LoopVerdict::Refuted)
        )
    );
    assert_eq!(
        lab.run("/loop --status").await,
        "Loop: running iteration 2, 4 of 5 iterations remaining, until `test -f done` succeeds, last check after iteration 1: exit 1"
    );
    std::fs::write(project(lab.dir.path()).join("done"), "").expect("done");
    release.send_replace(true);
    lab.idle().await;
    assert_eq!(
        lab.run("/loop --status").await,
        "Loop: off. Last loop: Loop condition `test -f done` is now satisfied. Loop mode disabled."
    );
    lab.close().await;
}

/// A manual compaction cuts the turn in flight: held, the loop does not
/// read the abort as the user's interrupt, and sends the cut turn again
/// as the same iteration.
#[tokio::test]
async fn a_compaction_sends_the_cut_turn_again() {
    let (stuck, mut reached, _release) = gated("never");
    let lab = open(vec![stuck, answer("1"), answer("2"), answer("no")]).await;
    lab.run("/loop 1 go").await;
    reached
        .wait_for(|reached| *reached)
        .await
        .expect("the turn runs");
    let main = lab.session.main();
    assert!(hold_loop_for_compaction(lab.session.harness(), &main, cx())
        .await
        .expect("hold"));
    main.abort(ConversationAbortOptions::default(), cx())
        .await
        .expect("abort");
    lab.idle().await;
    assert_eq!(lab.status().await.state.phase, LoopPhase::Turn);
    resume_loop_after_compaction(lab.session.deps(), &main, cx())
        .await
        .expect("resume");
    lab.idle().await;
    assert_eq!(lab.sent().await, sends("go", &[1, 1, 2]));
    assert_eq!(
        lab.notices().await,
        vec!["Loop limit reached. Loop mode disabled.".to_owned()]
    );
    let doc = read_doc(lab.session.harness(), &LOOP_MODE_DOC, main.id(), cx())
        .await
        .expect("read")
        .expect("the loop document");
    assert_eq!((doc.held, doc.resends), (false, 1));
    lab.close().await;
}

/// Malformed arguments fail with the malformed-arguments message and start
/// nothing.
#[tokio::test]
async fn malformed_arguments_start_no_loop() {
    let lab = open(vec![answer("no")]).await;
    assert_eq!(
        lab.run("/loop --until").await,
        "Command failed: --until needs a shell command. Quote it when it contains spaces: /loop --until 'bun test'."
    );
    assert_eq!(
        lab.run("/loop 0").await,
        "Command failed: Loop count must be a positive integer."
    );
    assert_eq!(lab.status().await, LoopStatus::default());
    assert_eq!(lab.provider.get_pending_response_count(), 1);
    lab.close().await;
}
