//! The work-left Director on a real Harness with faux models and a
//! scripted final-answer judge: an answer that asks to go on continues the
//! run with no user input; an answer the judge reads as done, or gives no
//! verdict on, stands; a run that only read, or has input queued, is never
//! judged; the progress check ends a chain that makes no new tool result.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_tool_call, FauxAssistantMessageOptions, FauxResponseStep,
};
use eukhe_ai::typebox::{TSchema, Type};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::define::{define_extension, define_tool, hook};
use eukhe_durable::harness::types::{
    Extension, GenerationHooks, InputSubmissionDraft, ToolExecutionResult, ToolRegistration,
    WhenBusy,
};
use eukhe_durable::harness::GENERATION_TASK;
use eukhe_durable::storage::MemoryStorage;
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{
    AssistantMessage, JsonObject, StopReason, TextContent, ToolResultMessage, UserContent,
    UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;

use super::work_left::{work_left_hook, WorkLeftHost};
use super::{
    director_state, tool_acted, DirectorLimits, WorkLeftOutcome, DIRECTOR_NOTICE_CUSTOM_TYPE,
};
use crate::durable::acceptance::{Judge, JudgeQuestion, JudgeReply, JudgeRequest};
use crate::durable::entries::CUSTOM_ENTRY;
use crate::durable::goals::tests::{
    answer, entries, setup_with, submit, user_origins, user_texts, Setup,
};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// The judge's replies, served in order (none left: no verdict), and the
/// answers it was asked to read.
struct ScriptedJudge {
    replies: Mutex<VecDeque<JudgeReply>>,
    asked: Mutex<Vec<String>>,
}

impl ScriptedJudge {
    fn asked(&self) -> Vec<String> {
        self.asked
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

impl Judge for ScriptedJudge {
    fn judge(&self, request: JudgeRequest, _cx: &Context) -> BoxFuture<'_, JudgeReply> {
        assert_eq!(request.question, JudgeQuestion::Report);
        self.asked
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(request.evidence);
        let reply = self
            .replies
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .pop_front()
            .unwrap_or_else(|| JudgeReply::Unavailable("no scripted reply".to_owned()));
        futures::future::ready(reply).boxed()
    }
}

fn verdict(text: &str) -> JudgeReply {
    JudgeReply::Text(text.to_owned())
}

/// A `write` tool: a tool with an effect (it is not a read tool).
fn write_extension() -> Arc<Extension> {
    let schema: TSchema = Type::object(Vec::<(String, TSchema)>::new());
    let tool = define_tool(ToolRegistration::new(
        "write",
        "write tool",
        schema,
        |_, _, _| async {
            Ok(ToolExecutionResult {
                output: Some(vec![UserContentBlock::Text(TextContent::new("written"))]),
                ..ToolExecutionResult::default()
            })
        },
    ));
    define_extension(Extension {
        name: "test.write".to_owned(),
        tools: vec![tool],
        ..Extension::default()
    })
}

fn write_call() -> FauxResponseStep {
    faux_assistant_message(
        faux_tool_call("write", JsonObject::new(), Some("call-write".to_owned())),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

/// The goal extension's setup with the work-left Director's hook in an
/// extension installed after it, judged by `replies`, and the `write` tool.
/// Once a test puts an answer in `rerun`, a hook after the Director's
/// reruns the work-left step of each final answer the Director let stand,
/// in the same generation, with that answer, and keeps what it returned in
/// `reruns`.
struct WorkLeftSetup {
    setup: Setup,
    judge: Arc<ScriptedJudge>,
    rerun: Arc<Mutex<Option<AssistantMessage>>>,
    reruns: Arc<Mutex<Vec<Option<String>>>>,
}

fn work_left_setup(replies: Vec<JudgeReply>) -> WorkLeftSetup {
    let judge = Arc::new(ScriptedJudge {
        replies: Mutex::new(replies.into()),
        asked: Mutex::default(),
    });
    let host_judge: Arc<dyn Judge> = Arc::<ScriptedJudge>::clone(&judge);
    let rerun: Arc<Mutex<Option<AssistantMessage>>> = Arc::default();
    let reruns: Arc<Mutex<Vec<Option<String>>>> = Arc::default();
    let (with, kept) = (Arc::clone(&rerun), Arc::clone(&reruns));
    let setup = setup_with(move |beside| {
        let host = WorkLeftHost {
            harness: beside.cell.clone(),
            budget: Arc::clone(beside.budget),
            judge: host_judge,
            limits: beside.limits,
            work: Arc::default(),
        };
        let again = host.clone();
        let rerun = hook(
            &*GENERATION_TASK,
            GenerationHooks {
                on_yield: Some(Arc::new(move |_, api, cx| {
                    let (host, with, kept, api, cx) = (
                        again.clone(),
                        Arc::clone(&with),
                        Arc::clone(&kept),
                        api.clone(),
                        cx.clone(),
                    );
                    async move {
                        let answer = with.lock().unwrap_or_else(PoisonError::into_inner).clone();
                        if let Some(answer) = answer {
                            let outcome = host.on_yield(&answer, &api, &cx).await?;
                            kept.lock()
                                .unwrap_or_else(PoisonError::into_inner)
                                .push(outcome);
                        }
                        Ok(None)
                    }
                    .boxed()
                })),
                ..GenerationHooks::default()
            },
        );
        let work_left = define_extension(Extension {
            name: "test.work_left".to_owned(),
            hooks: vec![work_left_hook(host), rerun],
            ..Extension::default()
        });
        vec![work_left, write_extension()]
    });
    WorkLeftSetup {
        setup,
        judge,
        rerun,
        reruns,
    }
}

/// The texts of the Director's display rows.
fn notices(entries: &[eukhe_durable::types::EntryRecord]) -> Vec<String> {
    entries
        .iter()
        .filter_map(|entry| {
            CUSTOM_ENTRY
                .narrow(entry.clone())
                .expect("eukhe.custom data")
        })
        .filter(|row| row.data().custom_type == DIRECTOR_NOTICE_CUSTOM_TYPE)
        .filter_map(|row| match &row.data().content {
            Some(UserContent::Text(text)) => Some(text.clone()),
            Some(UserContent::Blocks(_)) | None => None,
        })
        .collect()
}

/// Regression: a run that acted and answered "Should I continue with step
/// 2?" stopped until the user came back. The judge reads work left, so the
/// run goes on to a second turn with one harness continuation (never a
/// user message), and that turn's answer, read as done, ends it.
#[tokio::test]
async fn an_answer_that_asks_to_go_on_continues_the_run_without_the_user() {
    let WorkLeftSetup { setup, judge, .. } = work_left_setup(vec![
        verdict("FAIL\n- step 2: migrate the callers"),
        verdict("PASS"),
    ]);
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup.faux.set_responses(vec![
        write_call(),
        answer("Step 1 is done. Should I continue with step 2?"),
        answer("Step 2 is done: the callers are migrated."),
    ]);

    submit(&root, "migrate the callers in two steps").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let entries = entries(&root).await;
    assert_eq!(
        (
            user_origins(&entries),
            user_texts(&entries).get(1).cloned(),
            notices(&entries),
            judge.asked(),
            setup.faux.get_pending_response_count(),
        ),
        (
            vec![InputOrigin::User, InputOrigin::Director],
            Some(
                "[director: work left] The final answer leaves task work undone:\n- step 2: migrate the callers\n\nNobody is watching this run to answer a question or grant leave. Decide and act: do the remaining work now, then give the final answer. State each assumption made in the final answer. Work that truly cannot be done (a refusal, a missing credential, a check's protected file) goes into the final answer; the rest gets done."
                    .to_owned()
            ),
            vec![
                "The final answer left task work undone (step 2: migrate the callers); the run went on."
                    .to_owned()
            ],
            vec![
                "Step 1 is done. Should I continue with step 2?".to_owned(),
                "Step 2 is done: the callers are migrated.".to_owned(),
            ],
            0,
        )
    );
    // The last decision is recorded with the stack: the done answer stood.
    let state = director_state(&harness, root.id(), cx())
        .await
        .expect("read");
    assert_eq!(
        state.work_left.map(|record| record.outcome),
        Some(WorkLeftOutcome::Yield)
    );
    harness.close(cx()).await.expect("close");
}

/// An answer the judge reads as done stands, and so does one it gives no
/// verdict on: an unjudged answer never continues.
#[tokio::test]
async fn a_done_or_unjudged_answer_stands() {
    for reply in [
        verdict("PASS"),
        JudgeReply::Unavailable("429 usage limit".to_owned()),
        verdict("maybe"),
    ] {
        let WorkLeftSetup { setup, judge, .. } = work_left_setup(vec![reply.clone()]);
        let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
        setup.faux.set_responses(vec![
            write_call(),
            answer("Step 1 is done."),
            answer("unused"),
        ]);

        submit(&root, "do step 1").await;
        harness.wait_for_idle(cx()).await.expect("idle");

        assert_eq!(
            (
                user_origins(&entries(&root).await),
                judge.asked().len(),
                setup.faux.get_pending_response_count(),
            ),
            (vec![InputOrigin::User], 1, 1),
            "{reply:?}"
        );
        harness.close(cx()).await.expect("close");
    }
}

/// A run that only answered (no tool call with an effect since the user's
/// message) is never judged: its question stands for the user.
#[tokio::test]
async fn a_run_that_did_not_act_is_never_judged() {
    let WorkLeftSetup { setup, judge, .. } = work_left_setup(vec![verdict("FAIL\n- everything")]);
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup.faux.set_responses(vec![
        answer("Which of the two designs do you mean?"),
        answer("unused"),
    ]);

    submit(&root, "build the design").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    assert_eq!(
        (
            user_origins(&entries(&root).await),
            judge.asked(),
            setup.faux.get_pending_response_count(),
        ),
        (vec![InputOrigin::User], Vec::<String>::new(), 1)
    );
    harness.close(cx()).await.expect("close");
}

/// User input queued while the answer streams owns the boundary: the
/// answer is not judged and the queued message runs next.
#[tokio::test]
async fn queued_user_input_holds_the_answer() {
    let WorkLeftSetup { setup, judge, .. } = work_left_setup(vec![verdict("FAIL\n- step 2")]);
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let queuing = root.clone();
    let queue_then_answer = FauxResponseStep::Factory(Arc::new(move |_, _, _, _| {
        let root = queuing.clone();
        async move {
            root.submit(
                InputSubmissionDraft {
                    request_id: None,
                    content: UserContent::Text("also update the docs".to_owned()),
                    when_busy: Some(WhenBusy::FollowUp),
                    origin: InputOrigin::User,
                    entry: None,
                },
                cx(),
            )
            .await
            .expect("the follow-up is admitted");
            Ok(faux_assistant_message(
                "Step 1 is done. Should I continue with step 2?",
                FauxAssistantMessageOptions::default(),
            ))
        }
        .boxed()
    }));
    setup.faux.set_responses(vec![
        write_call(),
        queue_then_answer,
        answer("The docs are updated."),
    ]);

    submit(&root, "do both steps").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    assert_eq!(
        (
            user_origins(&entries(&root).await),
            judge.asked(),
            setup.faux.get_pending_response_count(),
        ),
        (
            vec![InputOrigin::User, InputOrigin::User],
            Vec::<String>::new(),
            0
        )
    );
    harness.close(cx()).await.expect("close");
}

/// The progress check ends the chain: after `directors.stallSteps`
/// continuations in a row with no new tool result the run yields and its
/// final answer stands, unjudged.
#[tokio::test]
async fn the_chain_ends_after_stall_steps_continuations_without_new_work() {
    let WorkLeftSetup { setup, judge, .. } = work_left_setup(vec![
        verdict("FAIL\n- step 2"),
        verdict("FAIL\n- step 2"),
        verdict("FAIL\n- step 2"),
    ]);
    *setup.limits.lock().unwrap_or_else(PoisonError::into_inner) = DirectorLimits {
        stall_steps: 2,
        ..DirectorLimits::default()
    };
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let asks = "Step 1 is done. Shall I go on with step 2?";
    setup.faux.set_responses(vec![
        write_call(),
        answer(asks),
        answer(asks),
        answer(asks),
        answer("unused"),
    ]);

    submit(&root, "do both steps").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    assert_eq!(
        (
            user_origins(&entries(&root).await),
            judge.asked().len(),
            setup.faux.get_pending_response_count(),
        ),
        (
            vec![
                InputOrigin::User,
                InputOrigin::Director,
                InputOrigin::Director
            ],
            2,
            1
        )
    );
    harness.close(cx()).await.expect("close");
}

/// A rerun of a generation (a crash between the decision's commit and the
/// run's next step) repeats the decision recorded in `eukhe.directors`:
/// the judge is not asked again, whatever the answer now reads. The rerun
/// runs the step again in the generation the decision was recorded for.
#[tokio::test]
async fn a_rerun_repeats_the_recorded_decision() {
    let WorkLeftSetup {
        setup,
        judge,
        rerun,
        reruns,
    } = work_left_setup(vec![verdict("PASS"), verdict("FAIL\n- step 2")]);
    *rerun.lock().unwrap_or_else(PoisonError::into_inner) = Some(faux_assistant_message(
        "Should I continue with step 2?",
        FauxAssistantMessageOptions::default(),
    ));
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .faux
        .set_responses(vec![write_call(), answer("Step 1 is done.")]);

    submit(&root, "do step 1").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    assert_eq!(
        (
            reruns
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone(),
            judge.asked()
        ),
        (vec![None], vec!["Step 1 is done.".to_owned()])
    );
    harness.close(cx()).await.expect("close");
}

/// A call acts unless it only read: the read tools never act, a `bash`
/// call acts once a step has an effect other than reading (or its steps
/// are not recorded), every other tool acts.
#[test]
fn a_call_acts_unless_it_only_read() {
    let result = |tool: &str, details: Option<serde_json::Value>| ToolResultMessage {
        tool_call_id: "call-1".to_owned(),
        tool_name: tool.to_owned(),
        content: Vec::new(),
        details,
        usage: None,
        nested_calls: None,
        is_error: false,
        timestamp: 0,
        duration_ms: None,
    };
    let steps = |effects: &[&[&str]]| {
        Some(serde_json::json!({
            "steps": effects
                .iter()
                .map(|effects| serde_json::json!({ "effects": effects }))
                .collect::<Vec<_>>()
        }))
    };
    let acted: Vec<bool> = [
        result("read", None),
        result("grep", None),
        result("bash", steps(&[&["read"], &["read"]])),
        result("bash", steps(&[&["read"], &["read", "write"]])),
        result("bash", steps(&[&["exec"]])),
        result("bash", None),
        result("edit", None),
        result("python", None),
    ]
    .iter()
    .map(tool_acted)
    .collect();
    assert_eq!(acted, [false, false, false, true, true, true, true, true]);
}
