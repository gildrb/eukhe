//! Tests of the code mode tool on a Harness with the faux model: scripts
//! calling the conversation's tools (`calls`), and scripts that survive a
//! crash or a close/reopen, or end with an error when they cannot (`replay`).

mod calls;
mod replay;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use eukhe_ai::providers::faux::RegisterFauxProviderOptions;
use eukhe_types::pi_ai::{JsonValue as PiJsonValue, ToolResultMessage, UserContentBlock};
use serde_json::json;

use super::sandbox::{CodemodeSandbox, CodemodeSandboxOptions};
use super::{create_codemode_extension, CodemodeModels, CodemodeNamespace, CodemodeToolOptions};
use crate::harness::tests::chat_support::{all_entries, chat_setup, ChatSetup, OpenChat};
use crate::harness::tests::support::context;
use crate::harness::tool::tests::nested_support::{call_with, lock, text_result};
use crate::harness::tool::tests::support::{done, results, submit_and_wait, tool_with};
use crate::harness::types::{ToolExecutionResult, ToolRegistration};
use crate::types::SubmissionStatus;

/// Runs of each test tool, by name.
#[derive(Clone, Default)]
pub(super) struct Runs(Arc<Mutex<Vec<String>>>);

impl Runs {
    fn push(&self, entry: String) {
        lock(&self.0).push(entry);
    }

    /// Every run, `<tool>:<arguments>`, in order.
    pub(super) fn all(&self) -> Vec<String> {
        lock(&self.0).clone()
    }
}

/// A faux chat with code mode and the test tools: `echo` (`echo <text>`),
/// `status` (a schema tool whose error result carries a value), and `fail`
/// (a schema-less tool that fails).
pub(super) struct Setup {
    pub(super) chat: ChatSetup,
    pub(super) runs: Runs,
}

pub(super) fn sandbox() -> CodemodeSandbox {
    CodemodeSandbox::new(CodemodeSandboxOptions::default())
}

pub(super) fn options(sandbox: CodemodeSandbox) -> CodemodeToolOptions {
    CodemodeToolOptions {
        namespaces: vec![CodemodeNamespace {
            name: "github".to_owned(),
            description: Some("GitHub issues".to_owned()),
            instructions: Some("Prefer search".to_owned()),
            prefix: "gh_".to_owned(),
        }],
        models: CodemodeModels::Excluded,
        ..CodemodeToolOptions::new(sandbox)
    }
}

/// Install a test tool that records its runs in `runs`.
pub(super) fn add_tool(
    chat: &ChatSetup,
    runs: &Runs,
    name: &str,
    result: impl Fn(&PiJsonValue) -> ToolExecutionResult + Send + Sync + 'static,
    extra: impl FnOnce(&mut ToolRegistration),
) {
    let (runs, label) = (runs.clone(), name.to_owned());
    let result = Arc::new(result);
    let tool = tool_with(
        name,
        move |args, _, _| {
            runs.push(format!("{label}:{args}"));
            let result = result(&args);
            async move { Ok(result) }
        },
        extra,
    );
    crate::harness::tests::support::add_tool(&chat.registry, tool, None).unwrap();
}

pub(super) fn setup_with(options: CodemodeToolOptions) -> Setup {
    let chat = chat_setup(RegisterFauxProviderOptions::default());
    chat.registry
        .install(create_codemode_extension(options))
        .unwrap();
    let runs = Runs::default();
    add_tool(
        &chat,
        &runs,
        "echo",
        |args| {
            text_result(&format!(
                "echo {}",
                args["text"].as_str().unwrap_or_default()
            ))
        },
        |_| {},
    );
    add_tool(
        &chat,
        &runs,
        "status",
        |args| ToolExecutionResult {
            structured_output: Some(
                eukhe_chord::json::to_json(&json!({ "code": args["code"].clone() })).unwrap(),
            ),
            is_error: Some(args["code"] != json!(0)),
            ..text_result("status")
        },
        |tool| {
            tool.structured_output_schema = Some(
                eukhe_ai::typebox::Type::object([("code", eukhe_ai::typebox::Type::number())])
                    .into(),
            );
        },
    );
    add_tool(
        &chat,
        &runs,
        "fail",
        |_| ToolExecutionResult {
            is_error: Some(true),
            ..text_result("it broke")
        },
        |_| {},
    );
    add_tool(
        &chat,
        &runs,
        "gh_search_issues",
        |_| text_result("issue 1"),
        |_| {},
    );
    Setup { chat, runs }
}

pub(super) fn setup() -> Setup {
    setup_with(options(sandbox()))
}

/// The faux answers: one code mode call of `code`, then `done`.
pub(super) fn queue_script(chat: &ChatSetup, code: &str) {
    chat.faux.set_responses(vec![
        call_with("codemode", json!({ "code": code }), "c1").into(),
        done().into(),
    ]);
}

/// The code mode call's result message in `chat`.
pub(super) async fn codemode_result(chat: &OpenChat) -> ToolResultMessage {
    let entries = all_entries(&chat.root, context()).await.unwrap();
    results(&entries)
        .into_iter()
        .find(|message| message.tool_name == "codemode")
        .expect("a code mode result")
}

/// Run `code` as one code mode call over fresh memory storage.
pub(super) async fn run_script(setup: &Setup, code: &str) -> ToolResultMessage {
    queue_script(&setup.chat, code);
    let chat = crate::harness::tests::chat_support::open_chat(
        Arc::new(crate::storage::MemoryStorage::new()),
        &setup.chat,
        None,
    )
    .await
    .unwrap();
    assert_eq!(
        submit_and_wait(&chat.root, "go").await,
        SubmissionStatus::Done
    );
    let result = codemode_result(&chat).await;
    chat.harness.close(context()).await.unwrap();
    result
}

/// The result's text, with the wall time line, which varies, replaced.
pub(super) fn text(message: &ToolResultMessage) -> String {
    message
        .content
        .iter()
        .map(|item| match item {
            UserContentBlock::Text(text) => text.text.clone(),
            UserContentBlock::Image(image) => format!("[image {}]", image.mime_type),
        })
        .collect::<String>()
        .lines()
        .map(|line| {
            if line.starts_with("Wall time ") {
                "Wall time <t> seconds"
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// A counter for tools that change behaviour on their second run.
pub(super) fn counter() -> Arc<AtomicUsize> {
    Arc::new(AtomicUsize::new(0))
}

pub(super) fn bump(counter: &AtomicUsize) -> usize {
    counter.fetch_add(1, Ordering::SeqCst) + 1
}
