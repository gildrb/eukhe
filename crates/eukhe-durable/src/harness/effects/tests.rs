use eukhe_ai::providers::faux::RegisterFauxProviderOptions;
use eukhe_chord::json::from_json;
use eukhe_types::effects::{EffectClass, RanKind};

use super::{
    begin_run, effects_state, note_unknown, read_effects_state, read_ran_effects, record_ran,
    run_report, EffectKind, EffectsState, RanEffect, RanEffectDraft, RunReport, UnknownCause,
    UnknownEffect,
};
use crate::harness::tests::chat_support::{chat_setup, open_chat, OpenChat};
use crate::harness::tests::support::context;
use crate::storage::test_support::{jsonl, store_path};

fn draft(key: &str, command: &str, agent: Option<&str>) -> RanEffectDraft {
    RanEffectDraft {
        key: key.to_owned(),
        kind: RanKind::ShellStep,
        command: command.to_owned(),
        classes: vec![EffectClass::Exec, EffectClass::Net],
        agent: agent.map(str::to_owned),
        session_id: "s1".to_owned(),
        at_ms: 7,
    }
}

async fn open(path: &std::path::Path) -> OpenChat {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    open_chat(jsonl(path).await, &setup, None).await.unwrap()
}

/// Start the run `key`, then record `drafts` in one commit: the run's
/// number and the effects as recorded.
async fn run_recording(
    chat: &OpenChat,
    key: &'static str,
    drafts: Vec<RanEffectDraft>,
) -> (u64, Vec<RanEffect>) {
    let id = chat.root.id();
    chat.harness
        .commit(
            move |tx| async move {
                let run = begin_run(&tx, id, key).await?;
                let mut recorded = Vec::new();
                for effect in drafts {
                    recorded.push(record_ran(&tx, id, effect, run).await?);
                }
                Ok((run, recorded))
            },
            context(),
        )
        .await
        .unwrap()
}

/// Ids follow on across runs, a replayed key records nothing new and
/// gives the effect as first recorded, a replayed run start numbers
/// nothing new, the ledger survives a reopen, and each run's report holds
/// exactly its effects and the steps it treated as not run.
#[tokio::test]
async fn each_effect_is_recorded_once_in_its_run_and_survives_a_reopen() {
    let (_dir, path) = store_path();
    let chat = open(&path).await;
    let first = run_recording(
        &chat,
        "in1",
        vec![
            draft("s1:c1:0", "git push", None),
            draft("s2:c1:0", "curl -X POST https://x", Some("fix-tests")),
        ],
    )
    .await;
    let second = run_recording(
        &chat,
        "in2",
        vec![
            draft("s1:c1:0", "git push", None),
            draft("s1:c2:3", "npm publish", None),
        ],
    )
    .await;
    let replayed = run_recording(&chat, "in2", Vec::new()).await;
    let cut = UnknownEffect {
        id: "tool:c3".to_owned(),
        kind: EffectKind::Tool,
        what: "bash: make deploy".to_owned(),
        at: 1.0,
        cause: Some(UnknownCause::NotRepeatSafe),
        settled_run: None,
        resolution: None,
    };
    let id = chat.root.id();
    chat.harness
        .commit(
            {
                let cut = cut.clone();
                move |tx| async move { note_unknown(&tx, id, &cut).await }
            },
            context(),
        )
        .await
        .unwrap();
    chat.harness.close(context()).await.unwrap();
    let reopened = open(&path).await;
    let state = read_effects_state(&reopened.harness, reopened.root.id(), context())
        .await
        .unwrap();
    let push = draft("s1:c1:0", "git push", None).recorded(1, 1);
    let curl = draft("s2:c1:0", "curl -X POST https://x", Some("fix-tests")).recorded(2, 1);
    let publish = draft("s1:c2:3", "npm publish", None).recorded(3, 2);
    let cut = UnknownEffect {
        settled_run: Some(2),
        ..cut
    };
    assert_eq!(
        (
            first,
            second,
            replayed,
            state.clone(),
            run_report(&state, 1).unwrap(),
            run_report(&state, 2).unwrap(),
            run_report(&state, 3).unwrap(),
        ),
        (
            (1, vec![push.clone(), curl.clone()]),
            (2, vec![push.clone(), publish.clone()]),
            (2, Vec::new()),
            EffectsState {
                run: 2,
                run_key: Some("in2".to_owned()),
                unknown: vec![cut.clone()],
                ran: vec![push.clone(), curl.clone(), publish.clone()],
            },
            RunReport {
                ran: vec![push, curl],
                unknown: Vec::new(),
            },
            RunReport {
                ran: vec![publish],
                unknown: vec![cut],
            },
            RunReport::default(),
        )
    );
    reopened.harness.close(context()).await.unwrap();
}

/// A ledger an earlier release wrote (no `run`, no `ran`) reads as empty
/// and records from `e1` in run 1.
#[tokio::test]
async fn a_ledger_written_before_runs_reads_none_and_records() {
    let old: EffectsState = from_json(&serde_json::json!({ "unknown": [] }).into()).unwrap();
    let (_dir, path) = store_path();
    let chat = open(&path).await;
    let id = chat.root.id();
    let before = read_ran_effects(&chat.harness, id, context())
        .await
        .unwrap();
    let recorded = run_recording(&chat, "in1", vec![draft("s1:c1:0", "git push", None)]).await;
    let in_flight = chat
        .harness
        .commit(
            move |tx| async move { effects_state(&tx, id).await },
            context(),
        )
        .await
        .unwrap();
    let push = draft("s1:c1:0", "git push", None).recorded(1, 1);
    assert_eq!(
        (old, before, recorded, in_flight),
        (
            EffectsState::default(),
            Vec::new(),
            (1, vec![push.clone()]),
            EffectsState {
                run: 1,
                run_key: Some("in1".to_owned()),
                unknown: Vec::new(),
                ran: vec![push],
            }
        )
    );
    chat.harness.close(context()).await.unwrap();
}
