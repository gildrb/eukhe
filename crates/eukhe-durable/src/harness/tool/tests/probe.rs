//! A probed tool (a file write) cut by a restart: its probe says what the
//! world shows of the change the call was making, the compiled core
//! (`bend/once.bend`) what the restart does with it (evidence first, then
//! a repeat only for a repeat-safe tool, spec O13), and every call it
//! treats as not run enters the effects ledger in the same commit.

use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use eukhe_ai::providers::faux::RegisterFauxProviderOptions;
use eukhe_bend::rules::once::Seen;
use eukhe_chord::json::{from_json, JsonValue};
use futures::FutureExt;
use serde_json::json;

use super::nested_support::{
    call_with, codes, end_result, exec, hang, json, listen, lock, open_jsonl, results, settle,
    store_path, submit_go, text_result,
};
use super::support::{done, result_text, tool, tool_with};
use crate::harness::effects::{EffectKind, EffectsState, UnknownCause, UnknownEffect, EFFECTS_DOC};
use crate::harness::tests::chat_support::{all_entries, chat_setup, ChatSetup, OpenChat};
use crate::harness::tests::support::{add_tool, context};
use crate::harness::tests::task_support::{deferred, Deferred};
use crate::harness::types::{ToolProbe, ToolRegistration, ToolReplay};
use crate::harness::Harness;
use crate::types::{ConversationId, SubmissionStatus};

/// A probed `pwrite` tool and what it saw.
struct Probed {
    registration: Arc<ToolRegistration>,
    /// Resolves once the first run recorded its probe.
    started: Deferred,
    runs: Arc<AtomicUsize>,
    /// The records its probe was asked about.
    asked: Arc<Mutex<Vec<JsonValue>>>,
}

/// `pwrite` of replay `replay`: each run records `record` (none: nothing)
/// as its probe; the first then hangs until its invocation is cancelled, a
/// later one returns `written`. Its probe answers `seen`.
fn probed(record: Option<JsonValue>, seen: Seen, replay: ToolReplay) -> Probed {
    let started = deferred();
    let runs = Arc::new(AtomicUsize::new(0));
    let asked: Arc<Mutex<Vec<JsonValue>>> = Arc::default();
    let probe_asked = Arc::clone(&asked);
    let probe = ToolProbe {
        effect: EffectKind::Write,
        look: Arc::new(move |record: JsonValue| {
            lock(&probe_asked).push(record);
            futures::future::ready(seen).boxed()
        }),
    };
    let (gate, counter) = (started.clone(), Arc::clone(&runs));
    let registration = tool_with(
        "pwrite",
        move |_, api, cx| {
            let (gate, record) = (gate.clone(), record.clone());
            let run = counter.fetch_add(1, Ordering::SeqCst) + 1;
            async move {
                if let Some(record) = record {
                    api.probe(record, &cx).await?;
                }
                if run == 1 {
                    gate.resolve(());
                    return Err(hang(&cx).await);
                }
                Ok(text_result("written"))
            }
        },
        |tool| {
            tool.probe = Some(probe);
            tool.replay = Some(replay);
        },
    );
    Probed {
        registration,
        started,
        runs,
        asked,
    }
}

fn setup() -> ChatSetup {
    chat_setup(RegisterFauxProviderOptions::default())
}

/// Open the chat at `path` and start scheduling.
async fn open(path: &Path, setup: &ChatSetup) -> OpenChat {
    let opened = open_jsonl(path, setup).await;
    opened.harness.resume().unwrap();
    opened
}

/// The open unknown effects of `conversation`.
async fn ledger(harness: &Harness, conversation: ConversationId) -> Vec<UnknownEffect> {
    harness
        .snapshot(&EFFECTS_DOC, conversation, context())
        .await
        .unwrap()
        .map(|value| {
            from_json::<EffectsState>(&JsonValue::Object(value))
                .unwrap()
                .unknown
        })
        .unwrap_or_default()
}

/// What became of one `pwrite` call cut by a restart: its runs, its
/// result's error flag and text, the effects ledger, and the records its
/// probe was asked about.
struct Cut {
    runs: usize,
    is_error: bool,
    text: String,
    ledger: Vec<UnknownEffect>,
    asked: Vec<JsonValue>,
}

/// Run one `pwrite` call (`record` its probe, `seen` its probe's answer,
/// `replay` its tool's), close the Harness while it hangs, reopen, and let
/// the run settle.
async fn cut(record: Option<JsonValue>, seen: Seen, replay: ToolReplay) -> Cut {
    let (_directory, path) = store_path();
    let setup = setup();
    let pwrite = probed(record, seen, replay);
    add_tool(&setup.registry, Arc::clone(&pwrite.registration), None).unwrap();
    setup.faux.set_responses(vec![
        call_with("pwrite", json!({ "text": "a" }), "c1").into(),
        done().into(),
    ]);
    let opened = open(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    pwrite.started.wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open(&path, &setup).await;
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    let entries = all_entries(&opened.root, context()).await.unwrap();
    let all = results(&entries);
    let [result] = all.as_slice() else {
        panic!("one tool result: {all:?}");
    };
    let cut = Cut {
        runs: pwrite.runs.load(Ordering::SeqCst),
        is_error: result.is_error,
        text: result_text(result),
        ledger: ledger(&opened.harness, opened.root.id()).await,
        asked: lock(&pwrite.asked).clone(),
    };
    opened.harness.close(context()).await.unwrap();
    cut
}

fn record() -> JsonValue {
    json(r#"{"file":"a.txt"}"#)
}

/// The evidence decides before the policy: a landed change is adopted
/// even when the tool is safe to repeat.
#[tokio::test]
async fn adopts_a_call_whose_change_landed_without_running_it_again() {
    for replay in [ToolReplay::Unsafe, ToolReplay::Safe] {
        let cut = cut(Some(record()), Seen::Landed, replay).await;
        assert_eq!(
            (
                cut.runs,
                cut.is_error,
                cut.text.as_str(),
                cut.ledger,
                cut.asked
            ),
            (
                1,
                false,
                "Tool pwrite was cut by a restart after its change landed: what it wrote holds \
                 the new content. Its own result was lost; read what it changed for the details.",
                Vec::new(),
                vec![record()]
            )
        );
    }
}

#[tokio::test]
async fn runs_a_call_whose_change_never_landed_once_more() {
    let cut = cut(Some(record()), Seen::Clean, ToolReplay::Unsafe).await;
    assert_eq!(
        (
            cut.runs,
            cut.is_error,
            cut.text.as_str(),
            cut.ledger,
            cut.asked
        ),
        (2, false, "written", Vec::new(), vec![record()])
    );
}

/// A probe that cannot tell, and a call that recorded no probe before the
/// restart (its probe is never asked, whatever it would say), of a tool
/// whose repeat is not safe: treated as not run, never run again, and the
/// ledger notes the write under the run in flight.
#[tokio::test]
async fn treats_as_not_run_a_call_nobody_can_tell_of() {
    for (record, seen, asked) in [
        (Some(record()), Seen::Dark, vec![record()]),
        (None, Seen::Landed, Vec::new()),
    ] {
        let cut = cut(record, seen, ToolReplay::Unsafe).await;
        let at = cut.ledger.first().map_or(0.0, |effect| effect.at);
        assert_eq!(
            (cut.runs, cut.is_error, cut.text.as_str(), cut.ledger, cut.asked),
            (
                1,
                true,
                "<harness>\n[error] Tool pwrite was interrupted and may have partially run. Check \
                 the state it changes (files, processes, jobs) before you run it again.\n</harness>",
                vec![UnknownEffect {
                    id: "write:c1".to_owned(),
                    kind: EffectKind::Write,
                    what: "pwrite: a".to_owned(),
                    at,
                    cause: Some(UnknownCause::NotRepeatSafe),
                    settled_run: Some(0),
                    resolution: None,
                }],
                asked
            )
        );
    }
}

/// A write of a known content that nobody can tell of runs again: its
/// repeat leaves the file as one run does (spec O13 step 2), and nothing
/// enters the ledger.
#[tokio::test]
async fn runs_again_a_repeat_safe_call_nobody_can_tell_of() {
    for (record, seen, asked) in [
        (Some(record()), Seen::Dark, vec![record()]),
        (None, Seen::Landed, Vec::new()),
    ] {
        let cut = cut(record, seen, ToolReplay::Safe).await;
        assert_eq!(
            (
                cut.runs,
                cut.is_error,
                cut.text.as_str(),
                cut.ledger,
                cut.asked
            ),
            (2, false, "written", Vec::new(), asked)
        );
    }
}

/// A replay-unsafe caller's nested `pwrite` is abandoned by the restart (a
/// stopped run): its change certainly never landed, so it reports not
/// started, and only the caller, interrupted, enters the ledger.
#[tokio::test]
async fn a_stopped_call_whose_change_never_landed_did_not_run() {
    let (_directory, path) = store_path();
    let setup = setup();
    let pwrite = probed(Some(record()), Seen::Clean, ToolReplay::Unsafe);
    add_tool(&setup.registry, Arc::clone(&pwrite.registration), None).unwrap();
    add_tool(
        &setup.registry,
        tool("batch", |_, api, cx| async move {
            exec(&api, "pwrite", json!({}), &cx).await?;
            Ok(text_result("batched"))
        }),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        call_with("batch", json!({}), "c1").into(),
        done().into(),
    ]);
    let opened = open(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    pwrite.started.wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_jsonl(&path, &setup).await;
    let (stream, events) = listen(&opened.harness, opened.root.id()).await;
    opened.harness.resume().unwrap();
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    opened.harness.wait_for_idle(context()).await.unwrap();
    stream.stop().await;
    let nested = end_result(&events, "c1/1").expect("the nested call ends with a result");
    let ledger = ledger(&opened.harness, opened.root.id()).await;
    let at = ledger.first().map_or(0.0, |effect| effect.at);
    assert_eq!(
        (
            pwrite.runs.load(Ordering::SeqCst),
            codes(&nested.diagnostics),
            lock(&pwrite.asked).clone(),
            ledger
        ),
        (
            1,
            vec![Some("abandoned")],
            vec![record()],
            vec![UnknownEffect {
                id: "tool:c1".to_owned(),
                kind: EffectKind::Tool,
                what: "batch: {}".to_owned(),
                at,
                cause: Some(UnknownCause::NotRepeatSafe),
                settled_run: Some(0),
                resolution: None,
            }]
        )
    );
    opened.harness.close(context()).await.unwrap();
}
