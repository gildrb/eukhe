//! A background task that owns a child conversation.
//! Run: `cargo run -p eukhe-durable --example 03-owned-conversations`
use std::collections::BTreeMap;
use std::io::Write;
use std::sync::{Arc, LazyLock};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{to_json, JsonValue};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::session::create_session;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tasks::{define_task, Task, TaskDefinition};
use eukhe_durable::types::{
    ConversationId, ConversationOwnership, LatestFork, TaskOptions, TaskOwnership,
};
use serde::{Deserialize, Serialize};

type BoxError = Box<dyn std::error::Error + Send + Sync>;

// A typical agent setup: a background task supervises a helper conversation,
// and the main conversation keeps a registry that maps agent names to their
// conversations. All three are created in one commit, so after a crash either
// all of them exist or none do.

/// The supervisor's checkpoint: `{ phase: "ready" }`.
#[derive(Debug, Serialize, Deserialize)]
struct Ready {
    phase: String,
}

// A task definition needs a name, a version, the task's starting state, a
// handler for every phase, and an abort handler (12-tasks.rs runs a task).
// This example only creates the task record; a plain Session never runs it.
static SUPERVISOR: LazyLock<Task<JsonValue, Ready, JsonValue, ()>> = LazyLock::new(|| {
    define_task(
        TaskDefinition::new(
            "example.supervisor",
            1,
            |_: &JsonValue| {
                Ok(Ready {
                    phase: "ready".to_owned(),
                })
            },
            |_, _, _| async { Ok(()) },
        )
        .phase("ready", |_, _, _| async { Ok(()) }),
    )
});

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AgentLink {
    conversation_id: ConversationId,
    request_id: String,
}

#[derive(Debug, Default, Serialize, Deserialize)]
struct AgentRegistry {
    agents: BTreeMap<String, AgentLink>,
}

// "latest" keeps only the current value. `Initial` means forks of this
// conversation start without a registry, so a child doesn't inherit its
// parent's list of agents.
static AGENT_REGISTRY: ConversationDoc<AgentRegistry> = match ConversationDoc::define(
    DocDefinition {
        kind: "example.agent-registry",
        version: 1,
        initial: AgentRegistry::default,
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

/// Runs the example, writing what the TS example prints to `out`.
///
/// # Errors
/// Session and output failures.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    let session = create_session(
        Arc::new(MemoryStorage::new()),
        eukhe_durable::session::SessionOptions::default(),
    );

    let main = session
        .commit(
            |tx| async move {
                tx.create_conversation(ConversationOwnership::Ownerless)
                    .await
            },
            context,
        )
        .await?;

    let (supervisor_id, child) = session
        .commit(
            move |tx| async move {
                // `background: true` means the task is side work: waiting for the main
                // conversation to finish does not wait for it.
                let supervisor_id = tx
                    .create_task(
                        SUPERVISOR.as_definition_ref(),
                        JsonValue::Null,
                        TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: Some(main.id),
                            background: Some(true),
                            abandon_on_restart: None,
                        },
                    )
                    .await?;

                // The child records that it belongs to the supervisor task. The task was
                // created a few lines above in this same commit, which is allowed.
                let child = tx
                    .create_conversation(ConversationOwnership::Task {
                        task_id: supervisor_id,
                    })
                    .await?;

                // request_id is a fixed name for the child's first message. Later code
                // sends that message using this request_id, so a retry after a crash
                // cannot deliver it twice.
                let link = to_json(&AgentLink {
                    conversation_id: child.id,
                    request_id: format!("researcher:first-message:{supervisor_id}"),
                })?;
                tx.doc(&AGENT_REGISTRY, main.id)
                    .await?
                    .child("agents")?
                    .set("researcher", link)?;
                Ok((supervisor_id, child))
            },
            context,
        )
        .await?;

    writeln!(out, "supervisor task: {supervisor_id}")?;
    writeln!(out, "child conversation: {}", to_json(&child)?)?;
    let registry = session.snapshot(&AGENT_REGISTRY, main.id, context).await?;
    writeln!(
        out,
        "registry: {}",
        registry.map_or_else(
            || "undefined".to_owned(),
            |value| JsonValue::Object(value).to_string()
        )
    )?;

    session.close(context).await?;
    Ok(())
}
