//! Port of `test/harness-callers.test.ts`: who may call a tool.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{from_json, JsonValue};
use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;
use eukhe_types::pi_ai::{JsonObject as PiJsonObject, TextContent, UserContentBlock};

use super::support::{calls, done, submit_and_wait};
use crate::harness::agent::AGENT_DOC;
use crate::harness::define::define_tool;
use crate::harness::tests::chat_support::{
    all_entries, chat_setup, open_chat, ChatSetup, OpenChat,
};
use crate::harness::tests::support::{add_tool, context, empty_object_schema};
use crate::harness::types::{
    AgentChange, AgentState, ExecuteToolOptions, FieldChange, NestedToolExecutionResult,
    ToolCaller, ToolControl, ToolExecutionResult, ToolFilter, ToolRegistration, ToolsChange,
};
use crate::harness::Conversation;
use crate::storage::MemoryStorage;

type Received = Arc<Mutex<HashMap<String, NestedToolExecutionResult>>>;

/// TS `tool(name, extra)`: answers `<name> ran`; `extra` sets the optional fields.
fn tool(name: &str, extra: impl FnOnce(&mut ToolRegistration)) -> Arc<ToolRegistration> {
    let text = format!("{name} ran");
    let mut registration =
        ToolRegistration::new(name, name, empty_object_schema(), move |_, _, _| {
            let text = text.clone();
            async move {
                Ok(ToolExecutionResult {
                    output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
                    ..ToolExecutionResult::default()
                })
            }
        });
    extra(&mut registration);
    define_tool(registration)
}

fn plain(name: &str) -> Arc<ToolRegistration> {
    tool(name, |_| {})
}

/// TS `prober(names)`: a tool that calls each of `names` as a nested call and
/// records what it got back.
fn prober(names: &[&str]) -> (Arc<ToolRegistration>, Received) {
    let received: Received = Arc::new(Mutex::new(HashMap::new()));
    let names: Vec<String> = names.iter().map(|name| (*name).to_owned()).collect();
    let sink = Arc::clone(&received);
    let registration = define_tool(ToolRegistration::new(
        "probe",
        "probe",
        empty_object_schema(),
        move |_, api, cx| {
            let (names, sink) = (names.clone(), Arc::clone(&sink));
            async move {
                for name in names {
                    let result = api
                        .execute_tool(
                            &name,
                            PiJsonObject::new(),
                            &cx,
                            ExecuteToolOptions::default(),
                        )
                        .await?;
                    sink.lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .insert(name, result);
                }
                Ok(ToolExecutionResult::default())
            }
        },
    ));
    (registration, received)
}

fn received(received: &Received, name: &str) -> NestedToolExecutionResult {
    received
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .get(name)
        .cloned()
        .unwrap_or_else(|| panic!("no result for {name}"))
}

fn first_code(result: &NestedToolExecutionResult) -> Option<&str> {
    result.diagnostics.first().and_then(|d| d.code.as_deref())
}

async fn offered(root: &Conversation) -> Vec<String> {
    let agent = root.agent(context()).await.unwrap();
    agent.tools.iter().map(|each| each.name.clone()).collect()
}

async fn callable(root: &Conversation) -> Vec<String> {
    let agent = root.agent(context()).await.unwrap();
    agent
        .callable
        .iter()
        .map(|each| each.name.clone())
        .collect()
}

fn setup_with(tools: &[&Arc<ToolRegistration>]) -> ChatSetup {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    for each in tools {
        add_tool(&setup.registry, Arc::clone(each), None).unwrap();
    }
    setup
}

async fn open(setup: &ChatSetup) -> OpenChat {
    open_chat(Arc::new(MemoryStorage::new()), setup, None)
        .await
        .unwrap()
}

async fn configure_model_tools(root: &Conversation, change: FieldChange<ToolsChange>) {
    root.configure(
        AgentChange {
            model_tools: change,
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
}

async fn stored_model_tools(chat: &OpenChat) -> Option<ToolFilter> {
    let state = chat
        .harness
        .snapshot(&AGENT_DOC, chat.root.id(), context())
        .await
        .unwrap()
        .expect("pi.agent exists");
    from_json::<AgentState>(&JsonValue::Object(state))
        .unwrap()
        .model_tools
}

fn names(list: &[&str]) -> Vec<String> {
    list.iter().map(|name| (*name).to_owned()).collect()
}

fn call(name: &str) -> eukhe_types::pi_ai::AssistantMessage {
    calls(&[(name, serde_json::json!({}), "c1")])
}

#[tokio::test]
async fn offers_the_model_only_tools_it_may_call_and_lets_tools_call_only_tools_they_may_call() {
    let script = tool("script", |tool| {
        tool.callers = Some(vec![ToolCaller::Model]);
    });
    let hidden = tool("hidden", |tool| {
        tool.callers = Some(vec![ToolCaller::Tools]);
    });
    let both = plain("both");
    let (probe, got) = prober(&["script", "hidden", "both"]);
    let setup = setup_with(&[&script, &hidden, &both, &probe]);
    setup
        .faux
        .set_responses(vec![call("probe").into(), done().into()]);
    let chat = open(&setup).await;
    assert_eq!(
        offered(&chat.root).await,
        names(&["script", "both", "probe"])
    );
    assert_eq!(
        callable(&chat.root).await,
        names(&["hidden", "both", "probe"])
    );
    submit_and_wait(&chat.root, "go").await;
    assert_eq!(
        first_code(&received(&got, "script")),
        Some("tool_unavailable")
    );
    for name in ["hidden", "both"] {
        let result = received(&got, name);
        assert!(!result.is_error);
        assert_eq!(
            result.structured_output,
            Some(JsonValue::from(format!("{name} ran")))
        );
    }
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn narrows_what_the_model_is_offered_with_model_tools_leaving_the_rest_callable_by_tools() {
    let read = plain("read");
    let bash = plain("bash");
    let (probe, got) = prober(&["read", "bash"]);
    let setup = setup_with(&[&read, &bash, &probe]);
    setup
        .faux
        .set_responses(vec![call("probe").into(), done().into()]);
    let chat = open(&setup).await;
    configure_model_tools(
        &chat.root,
        FieldChange::Set(ToolsChange::Exactly(vec![Arc::clone(&probe)])),
    )
    .await;
    assert_eq!(offered(&chat.root).await, names(&["probe"]));
    assert_eq!(
        callable(&chat.root).await,
        names(&["read", "bash", "probe"])
    );
    submit_and_wait(&chat.root, "go").await;
    assert!(!received(&got, "read").is_error);
    assert!(!received(&got, "bash").is_error);

    configure_model_tools(
        &chat.root,
        FieldChange::Set(ToolsChange::Remove(vec![Arc::clone(&bash)])),
    )
    .await;
    assert_eq!(offered(&chat.root).await, names(&["read", "probe"]));
    assert_eq!(
        stored_model_tools(&chat).await,
        Some(ToolFilter::Remove {
            remove: names(&["bash"])
        })
    );
    configure_model_tools(&chat.root, FieldChange::Clear).await;
    assert_eq!(offered(&chat.root).await, names(&["read", "bash", "probe"]));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn never_offers_a_tool_that_is_not_enabled_nor_lets_tools_call_it() {
    let read = plain("read");
    let bash = plain("bash");
    let (probe, got) = prober(&["bash"]);
    let setup = setup_with(&[&read, &bash, &probe]);
    setup
        .faux
        .set_responses(vec![call("probe").into(), done().into()]);
    let chat = open(&setup).await;
    // model_tools cannot bring back what tools disabled.
    chat.root
        .configure(
            AgentChange {
                tools: FieldChange::Set(ToolsChange::Remove(vec![Arc::clone(&bash)])),
                model_tools: FieldChange::Set(ToolsChange::Exactly(vec![
                    Arc::clone(&bash),
                    Arc::clone(&probe),
                ])),
                ..AgentChange::default()
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(offered(&chat.root).await, names(&["probe"]));
    assert_eq!(callable(&chat.root).await, names(&["read", "probe"]));
    submit_and_wait(&chat.root, "go").await;
    assert_eq!(
        first_code(&received(&got, "bash")),
        Some("tool_unavailable")
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn answers_a_model_issued_call_of_a_tool_it_was_not_offered_as_unavailable() {
    let read = plain("read");
    let bash = plain("bash");
    let setup = setup_with(&[&read, &bash]);
    setup
        .faux
        .set_responses(vec![call("bash").into(), done().into()]);
    let chat = open(&setup).await;
    configure_model_tools(
        &chat.root,
        FieldChange::Set(ToolsChange::Exactly(vec![Arc::clone(&read)])),
    )
    .await;
    submit_and_wait(&chat.root, "go").await;
    let entries = all_entries(&chat.root, context()).await.unwrap();
    let result = entries
        .iter()
        .find(|entry| entry.kind == "pi.tool-result")
        .expect("a tool result");
    let model = serde_json::to_string(&result.model).unwrap();
    assert!(model.contains("Tool bash is not available"), "{model}");
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn applies_add_tools_to_model_tools_too_so_the_model_is_offered_the_added_tools() {
    let extra = plain("extra");
    let grow = define_tool(ToolRegistration::new(
        "grow",
        "grow",
        empty_object_schema(),
        |_, _, _| async {
            Ok(ToolExecutionResult {
                output: Some(Vec::new()),
                control: Some(ToolControl {
                    add_tools: Some(vec!["extra".to_owned()]),
                    ..ToolControl::default()
                }),
                ..ToolExecutionResult::default()
            })
        },
    ));
    let setup = setup_with(&[&extra, &grow]);
    setup
        .faux
        .set_responses(vec![call("grow").into(), done().into()]);
    let chat = open(&setup).await;
    configure_model_tools(
        &chat.root,
        FieldChange::Set(ToolsChange::Exactly(vec![Arc::clone(&grow)])),
    )
    .await;
    submit_and_wait(&chat.root, "go").await;
    assert_eq!(
        stored_model_tools(&chat).await,
        Some(ToolFilter::Exactly(names(&["grow", "extra"])))
    );
    assert_eq!(offered(&chat.root).await, names(&["grow", "extra"]));
    chat.harness.close(context()).await.unwrap();
}
