//! The tool surface on an open session (docs/tools.md S7): every request
//! sends the roster the session opened with, while a host tool that joins
//! later is listed and run through `dyn`; `report_issue` stores a row the
//! user sees; every change of the roster is rejected.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::{create_models, CreateModelsOptions};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_ai::typebox::Type;
use eukhe_ai::utils::transcript::get_current_tools;
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::registry::{RosterChange, RosterFixed};
use eukhe_durable::harness::types::{
    AgentChange, Extension, FieldChange, InputSubmissionDraft, ModelRef, RegistryReader,
    ToolExecutionResult, ToolRegistration, ToolsChange,
};
use eukhe_durable::harness::ConversationEntryQuery;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::pi_ai::{
    AssistantMessage, JsonObject, Message, StopReason, TextContent, ToolSchema, UserContentBlock,
};
use serde_json::{json, Value};
use tempfile::TempDir;

use super::{DYN_TOOL_NAME, TOOL_ISSUE_CUSTOM_TYPE};
use crate::durable::tool_contract::build;
use crate::durable::{open_session, SessionConfig, SessionStorage};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// A tool call of `dyn` with `arguments`.
fn dyn_call(call_id: &str, arguments: &Value) -> AssistantMessage {
    let Value::Object(arguments) = arguments.clone() else {
        unreachable!("an object literal");
    };
    faux_assistant_message(
        vec![faux_tool_call(
            DYN_TOOL_NAME,
            arguments.into_iter().collect::<JsonObject>(),
            Some(call_id.to_owned()),
        )],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

#[test]
fn build_adds_the_intent_and_a_version_and_keeps_every_parameter() {
    let declared = ToolSchema::from(json!({
        "type": "object",
        "properties": { "code": { "type": "string" } },
        "required": ["code"],
    }));
    let versioned = ToolSchema::from(json!({
        "type": "object",
        "title": "v3",
        "properties": { "a": { "type": "string" }, "i": { "type": "string" } },
    }));
    let intent = json!({
        "type": "string",
        "description": "Short present-participle intent for this call.",
    });
    assert_eq!(
        (
            build(&declared).json().clone(),
            build(&versioned).json().clone(),
            build(&build(&declared)) == build(&declared),
        ),
        (
            json!({
                "type": "object",
                "properties": { "i": intent, "code": { "type": "string" } },
                "required": ["code"],
                "title": "v1",
            }),
            json!({
                "type": "object",
                "title": "v3",
                "properties": { "a": { "type": "string" }, "i": { "type": "string" } },
            }),
            true,
        )
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_roster_stays_fixed_while_a_late_tool_is_reached_through_dyn() {
    let dir = TempDir::new().expect("temp dir");
    for sub in ["agent", "work"] {
        std::fs::create_dir_all(dir.path().join(sub)).expect("fixture dir");
    }
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    // Each request records the roster it sends.
    let sent: Arc<Mutex<Vec<Vec<String>>>> = Arc::default();
    let step = |reply: AssistantMessage| {
        let sent = Arc::clone(&sent);
        FauxResponseStep::factory(move |context, _, _, _| {
            sent.lock().unwrap_or_else(PoisonError::into_inner).push(
                get_current_tools(context.messages())
                    .into_iter()
                    .map(|tool| tool.name)
                    .collect(),
            );
            Ok(reply.clone())
        })
    };
    let text = |reply: &str| {
        faux_assistant_message(
            vec![faux_text(reply)],
            FauxAssistantMessageOptions::default(),
        )
    };
    faux.set_responses(vec![
        step(dyn_call("c1", &json!({}))),
        step(text("listed")),
        step(dyn_call("c2", &json!({}))),
        step(dyn_call(
            "c3",
            &json!({ "name": "late_echo", "arguments": { "text": "hi" } }),
        )),
        step(dyn_call(
            "c4",
            &json!({
                "name": "report_issue",
                "arguments": { "tool": "late_echo", "description": "it echoes twice" },
            }),
        )),
        step(text("done")),
    ]);
    let mut config = SessionConfig::new(
        dir.path().join("agent"),
        dir.path().join("work"),
        "019a0000-0000-7000-8000-000000000001",
        SessionStorage::Jsonl {
            dir: dir.path().join("sessions").join("session-1"),
            fsync: false,
        },
    );
    config.models = Some(models.clone());
    config.model = Some(
        ModelRef {
            provider: "faux".to_owned(),
            model_id: "faux-1".to_owned(),
        }
        .into(),
    );
    let session = open_session(config, cx()).await.expect("session opens");
    let root = session.root().clone();
    root.submit(InputSubmissionDraft::new("list the tools"), cx())
        .await
        .expect("submitted");
    root.wait_for_idle(cx()).await.expect("idle");

    // A host tool joins after the first request: only `dyn` reaches it.
    let late = ToolRegistration::new(
        "late_echo",
        "Echoes text.",
        Type::object([("text", Type::string())]),
        |params, _api, _cx| async move {
            Ok(ToolExecutionResult {
                output: Some(vec![UserContentBlock::Text(TextContent::new(
                    params["text"].as_str().unwrap_or_default(),
                ))]),
                ..ToolExecutionResult::default()
            })
        },
    );
    session.deps().tool_surface.join(Arc::new(late.clone()));
    root.submit(InputSubmissionDraft::new("use the late tool"), cx())
        .await
        .expect("submitted");
    root.wait_for_idle(cx()).await.expect("idle");

    // Every change of the roster is rejected.
    let rejection = |result: SessionResult<()>| {
        let Err(SessionError::Other(error)) = result else {
            panic!("not rejected");
        };
        error.downcast_ref::<RosterFixed>().cloned()
    };
    let installed = session.registry().install(Arc::new(Extension {
        tools: vec![Arc::new(late)],
        ..Extension::named("late")
    }));
    let configured = root
        .configure(
            AgentChange {
                tools: FieldChange::Set(ToolsChange::Exactly(Vec::new())),
                ..AgentChange::default()
            },
            cx(),
        )
        .await;

    let entries = root
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .expect("entries")
        .items;
    let mut results: Vec<String> = Vec::new();
    let mut issues: Vec<Value> = Vec::new();
    for entry in entries.iter().rev() {
        if entry.kind == "pi.tool-result" {
            for message in entry.model.iter().flatten() {
                if let Message::ToolResult(result) = message {
                    for item in &result.content {
                        if let UserContentBlock::Text(text) = item {
                            results.push(text.text.clone());
                        }
                    }
                }
            }
        }
        let data = serde_json::to_value(&entry.data).expect("entry data");
        if data["customType"] == TOOL_ISSUE_CUSTOM_TYPE {
            issues.push(json!([data["content"], data["display"], data["details"]]));
        }
    }
    let roster: Vec<String> = session
        .registry()
        .snapshot()
        .roster()
        .expect("the roster is fixed")
        .iter()
        .map(|tool| tool.name.clone())
        .collect();
    let report = super::REPORT_ISSUE_DESCRIPTION;
    assert_eq!(
        (
            sent.lock().unwrap_or_else(PoisonError::into_inner).clone(),
            roster.contains(&DYN_TOOL_NAME.to_owned()),
            results,
            issues,
            rejection(installed),
            rejection(configured),
        ),
        (
            vec![roster.clone(); 6],
            true,
            vec![
                format!("report_issue: {report}"),
                format!(
                    "report_issue: {report}\nlate_echo: Echoes text. Arguments: {}",
                    json!({
                        "type": "object",
                        "required": ["text"],
                        "properties": { "text": { "type": "string" } },
                    })
                ),
                "hi".to_owned(),
                "Recorded the issue with late_echo; the user sees it in the session.".to_owned(),
            ],
            vec![json!([
                "Tool issue reported for late_echo: it echoes twice",
                true,
                { "tool": "late_echo", "description": "it echoes twice" },
            ])],
            Some(RosterFixed {
                change: RosterChange::Install("late".to_owned())
            }),
            Some(RosterFixed {
                change: RosterChange::Configure("tools")
            }),
        )
    );
    session.close(cx()).await.expect("closed");
}
