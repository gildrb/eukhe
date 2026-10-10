//! Port of `test/harness-tools.test.ts` `describe("coding tools")`: the
//! built-in coding tools through the harness.

use std::sync::Arc;

use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;

use super::support::{calls, done, result_text, results};
use crate::entries::TOOL_RESULT_ENTRY;
use crate::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use crate::harness::define::define_extension;
use crate::harness::tests::chat_support::{all_entries, chat_setup, open_chat, ChatEnv, OpenChat};
use crate::harness::tests::support::{add_tool, context};
use crate::harness::types::{Extension, InputSubmissionDraft};
use crate::storage::MemoryStorage;
use crate::tools::{
    create_bash_tool, create_edit_tool, create_read_tool, BashToolOptions, ReadToolOptions,
};
use crate::types::SubmissionStatus;

fn temp_dir() -> tempfile::TempDir {
    tempfile::Builder::new()
        .prefix("pi-durable-coding-")
        .tempdir()
        .expect("temp dir")
}

fn env(directory: &tempfile::TempDir) -> ChatEnv {
    let env: Arc<dyn ExecutionEnv> = Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: directory.path().to_string_lossy().into_owned(),
        ..NativeExecutionEnvOptions::default()
    }));
    ChatEnv::One(env)
}

#[tokio::test]
async fn answers_a_failing_command_with_its_retained_tail_and_diagnostics_in_order() {
    let directory = temp_dir();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(
        &setup.registry,
        create_bash_tool(BashToolOptions::default()),
        None,
    )
    .unwrap();
    let command = "i=1; while [ $i -le 3000 ]; do echo line-$i; i=$((i + 1)); done; exit 7";
    setup.faux.set_responses(vec![
        calls(&[("bash", serde_json::json!({ "command": command }), "b")]).into(),
        done().into(),
    ]);
    let OpenChat { harness, root } = open_chat(
        Arc::new(MemoryStorage::new()),
        &setup,
        Some(env(&directory)),
    )
    .await
    .unwrap();
    root.submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let entry = all_entries(&root, context())
        .await
        .unwrap()
        .into_iter()
        .find(|candidate| TOOL_RESULT_ENTRY.is(Some(candidate)))
        .expect("a tool result entry");
    let result = &results(std::slice::from_ref(&entry))[0];
    assert!(result.is_error);
    let text = result_text(result);
    assert!(text.starts_with("line-1001\n"), "{text}");
    let data = entry.data.as_ref().expect("tool result data");
    let codes: Vec<&str> = data["diagnostics"]
        .as_array()
        .expect("diagnostics")
        .iter()
        .map(|diagnostic| diagnostic["code"].as_str().expect("code"))
        .collect();
    assert_eq!(codes, ["full_output", "exit_code", "truncated"]);
    assert!(
        text.contains("line-3000\n|<harness>\n[info] Full output: "),
        "{text}"
    );
    assert!(
        text.contains("\n[error] Command exited with code 7\n[warn] Output truncated to its end: 1000 lines, "),
        "{text}"
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reads_edits_and_runs_a_command_in_one_run_then_answers() {
    let directory = temp_dir();
    let notes = directory.path().join("notes.txt");
    std::fs::write(&notes, "hello world\n").unwrap();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup
        .registry
        .install(define_extension(Extension {
            tools: vec![
                create_read_tool(ReadToolOptions::default()),
                create_edit_tool(),
                create_bash_tool(BashToolOptions::default()),
            ],
            ..Extension::named("coding")
        }))
        .unwrap();
    setup.faux.set_responses(vec![
        calls(&[("read", serde_json::json!({ "path": "notes.txt" }), "r")]).into(),
        calls(&[(
            "edit",
            serde_json::json!({ "path": "notes.txt", "edits": [{ "oldText": "world", "newText": "durable" }] }),
            "e",
        )])
        .into(),
        calls(&[("bash", serde_json::json!({ "command": "cat notes.txt" }), "b")]).into(),
        done().into(),
    ]);
    let OpenChat { harness, root } = open_chat(
        Arc::new(MemoryStorage::new()),
        &setup,
        Some(env(&directory)),
    )
    .await
    .unwrap();
    let settled = root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_eq!(settled.state.status(), SubmissionStatus::Done);
    let entries = all_entries(&root, context()).await.unwrap();
    let summary: Vec<(String, bool, String)> = results(&entries)
        .iter()
        .map(|result| {
            (
                result.tool_name.clone(),
                result.is_error,
                result_text(result),
            )
        })
        .collect();
    assert_eq!(
        summary,
        [
            ("read".to_owned(), false, "hello world\n".to_owned()),
            (
                "edit".to_owned(),
                false,
                "Successfully replaced 1 block(s) in notes.txt.".to_owned()
            ),
            ("bash".to_owned(), false, "hello durable\n".to_owned()),
        ]
    );
    assert_eq!(entries.last().unwrap().kind, "pi.assistant");
    assert_eq!(std::fs::read_to_string(&notes).unwrap(), "hello durable\n");
    harness.close(context()).await.unwrap();
}
