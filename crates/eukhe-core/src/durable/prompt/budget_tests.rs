//! The prompt budget: what eukhe itself sends with every request of a
//! default root session (its system prompt and its tool schemas, with no
//! user skills, no `AGENTS.md` and no MCP server) stays within
//! [`PROMPT_BUDGET_BYTES`]. A change that grows eukhe's own prompt or a
//! tool's schema past it fails this test, so the growth is a decision (lower
//! the prompt elsewhere, or raise the budget in the same change), never a
//! drift. The 56 KB system prompt plus 23.5 KB of tools of 2026-11-01 was
//! such a drift.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::{create_models, CreateModelsOptions};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, FauxResponseStep,
    RegisterFauxProviderOptions,
};
use eukhe_ai::utils::text::get_system_message_text;
use eukhe_ai::utils::transcript::{get_current_system_message, get_current_tools};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::types::{InputSubmissionDraft, ModelRef};
use eukhe_types::pi_ai::Tool;

use crate::durable::{open_session, SessionConfig, SessionStorage};
use crate::memory::{Memory, ResponseStarted, Summarizer, SummarizerFuture};

/// The most bytes eukhe's own system prompt and tool schemas may take in
/// one request of a default root session (chat memory on, as the daemon
/// and headless runs open it): the 58,174 bytes measured after the prompt
/// trim of e440c7d91 (system prompt 35,055, tool schemas 23,119), plus 5%.
const PROMPT_BUDGET_BYTES: usize = 61_000;

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// A chat-memory compactor that is never asked: the one message is short.
struct NoSummarizer;

impl Summarizer for NoSummarizer {
    fn complete(
        &self,
        _context: eukhe_types::pi_ai::Context,
        _started: ResponseStarted,
    ) -> SummarizerFuture {
        Box::pin(async { Err(anyhow::anyhow!("no model in this test")) })
    }
}

/// The captured request: its system prompt text and the tools it offers.
type Sent = Arc<Mutex<Option<(String, Vec<Tool>)>>>;

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_default_root_request_stays_within_the_prompt_budget() {
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    let cwd = dir.path().join("project");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&cwd).expect("cwd");
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let sent: Sent = Arc::default();
    let capture = Arc::clone(&sent);
    faux.set_responses(vec![FauxResponseStep::factory(move |context, _, _, _| {
        let messages = context.messages();
        let system = get_current_system_message(messages).expect("a system prompt");
        *capture.lock().unwrap_or_else(PoisonError::into_inner) = Some((
            get_system_message_text(&system),
            get_current_tools(messages),
        ));
        Ok(faux_assistant_message(
            "ok",
            FauxAssistantMessageOptions::default(),
        ))
    })]);
    let model = faux.get_model();
    let mut config = SessionConfig::new(
        &agent_dir,
        &cwd,
        "0192a000-0000-7000-8000-0000000000b1",
        SessionStorage::Memory,
    );
    config.models = Some(models);
    config.model = Some(
        ModelRef {
            provider: model.provider,
            model_id: model.id,
        }
        .into(),
    );
    config.memory = Some(
        Memory::open(agent_dir.join("chat"), Arc::new(NoSummarizer))
            .await
            .expect("memory"),
    );
    let session = open_session(config, cx()).await.expect("open");
    session
        .root()
        .submit(InputSubmissionDraft::new("hi"), cx())
        .await
        .expect("submitted");
    session.root().wait_for_idle(cx()).await.expect("idle");
    session.close(cx()).await.expect("close");
    let (system, tools) = sent
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .expect("the request was captured");
    // Each tool's schema as the transcript declares it to the provider:
    // name, description, parameters.
    let schemas: Vec<(String, usize)> = tools
        .iter()
        .map(|tool| {
            let bytes = serde_json::to_vec(tool).expect("a tool schema serializes");
            (tool.name.clone(), bytes.len())
        })
        .collect();
    let total = system.len() + schemas.iter().map(|(_, bytes)| bytes).sum::<usize>();
    assert!(
        total <= PROMPT_BUDGET_BYTES,
        "a default root request sends {total} bytes of eukhe's own prompt, past the budget of \
         {PROMPT_BUDGET_BYTES}: system prompt {}, tool schemas {schemas:?}",
        system.len()
    );
}
