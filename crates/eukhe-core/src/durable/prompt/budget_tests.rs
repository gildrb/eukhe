//! The prompt budget: what eukhe itself sends with every request of a
//! default root session (its system prompt and its tool schemas, with no
//! user skills, no `AGENTS.md` and no MCP server) stays within
//! [`PROMPT_BUDGET_BYTES`]. A change that grows eukhe's own prompt or a
//! tool's schema past it fails this test, so the growth is a decision (lower
//! the prompt elsewhere, or raise the budget in the same change), never a
//! drift. The 56 KB system prompt plus 23.5 KB of tools of 2026-11-01 was
//! such a drift. The user's own skills (`~/.agents/skills` of the HOME the
//! tests run in) are left out of the count; eukhe's bundled skills count.

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
use crate::packages::get_bundled_skills_dir;

/// The most bytes eukhe's own system prompt and tool schemas may take in
/// one request of a default root session (chat memory on, as the daemon
/// and headless runs open it): what release v0.10.67 (f58acb642) sends,
/// its bundled skills counted: 21,926 bytes (system prompt 9,490, tool
/// schemas 12,436). No headroom: the prompt does not grow past the
/// release unless a change decides it.
const PROMPT_BUDGET_BYTES: usize = 21_926;

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
    let (total, report) = default_root_request(Kernel::Available).await;
    eprintln!("{report}");
    assert!(
        total <= PROMPT_BUDGET_BYTES,
        "a default root request sends {total} bytes of eukhe's own prompt, past the budget of \
         {PROMPT_BUDGET_BYTES}: {report}"
    );
}

/// A session whose kernel cannot start (its Python is not fetched and the
/// machine is offline) sends no larger a
/// prompt than one whose kernel can: it drops the `ipython` schema and the
/// kernel's package list, and says it has no Python REPL.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_unavailable_kernel_does_not_grow_the_prompt() {
    let _env_lock = crate::kernel::bootstrap::KERNEL_ENV_LOCK.lock().await;
    let (available, available_report) = default_root_request(Kernel::Available).await;
    let (unavailable, unavailable_report) = default_root_request(Kernel::Unavailable).await;
    eprintln!("available: {available_report}\nunavailable: {unavailable_report}");
    assert!(
        unavailable <= available,
        "an unavailable kernel grows the prompt from {available} to {unavailable} bytes: \
         {unavailable_report}"
    );
}

/// Whether the session's kernel can start.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kernel {
    /// The tests' kernel interpreter.
    Available,
    /// No interpreter named, no fetched Python, offline.
    Unavailable,
}

/// Puts an env variable back when dropped.
struct EnvVar(&'static str, Option<std::ffi::OsString>);

impl EnvVar {
    fn set(name: &'static str, value: Option<&std::ffi::OsStr>) -> Self {
        let old = std::env::var_os(name);
        match value {
            Some(value) => std::env::set_var(name, value),
            None => std::env::remove_var(name),
        }
        Self(name, old)
    }
}

impl Drop for EnvVar {
    fn drop(&mut self) {
        match &self.1 {
            Some(value) => std::env::set_var(self.0, value),
            None => std::env::remove_var(self.0),
        }
    }
}

/// The bytes of eukhe's own system prompt and tool schemas in the first
/// request of a default root session, and their breakdown.
async fn default_root_request(kernel: Kernel) -> (usize, String) {
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
    let _env = (kernel == Kernel::Unavailable).then(|| {
        config.kernel_python = None;
        let kernel_dir = dir.path().join("no-kernel");
        let checkout = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        [
            EnvVar::set("EUKHE_KERNEL_DIR", Some(kernel_dir.as_os_str())),
            EnvVar::set("EUKHE_OFFLINE", Some(std::ffi::OsStr::new("1"))),
            EnvVar::set("EUKHE_PACKAGE_DIR", Some(checkout.as_os_str())),
            EnvVar::set("EUKHE_KERNEL_PYTHON", None),
        ]
    });
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
    assert_eq!(
        tools.iter().any(|tool| tool.name == "ipython"),
        kernel == Kernel::Available
    );
    // Each tool's schema as the transcript declares it to the provider:
    // name, description, parameters.
    let schemas: Vec<(String, usize)> = tools
        .iter()
        .map(|tool| {
            let bytes = serde_json::to_vec(tool).expect("a tool schema serializes");
            (tool.name.clone(), bytes.len())
        })
        .collect();
    let system = without_user_skills(&system);
    let total = system.len() + schemas.iter().map(|(_, bytes)| bytes).sum::<usize>();
    let report = format!(
        "system prompt {}, tool schemas {schemas:?}, total {total}",
        system.len()
    );
    (total, report)
}

/// The system prompt without the user's skills: the inventory groups under
/// the HOME the tests run in (`~/.agents/skills/<name>/SKILL.md:`) differ
/// from machine to machine. eukhe's own bundled skills
/// (`get_bundled_skills_dir`) stay, wherever the checkout lives (also
/// under HOME), with their directory written `skills/`: every user gets
/// their inventory, and only the checkout's path differs.
fn without_user_skills(system: &str) -> String {
    let bundled = format!("{}/", get_bundled_skills_dir().display());
    let home = std::env::var_os("HOME").map(|home| home.to_string_lossy().into_owned());
    let mut skipping = false;
    let kept: Vec<&str> = system
        .split('\n')
        .filter(|line| {
            if line.starts_with('/') && line.ends_with("SKILL.md:") {
                skipping = home
                    .as_deref()
                    .is_some_and(|home| line.starts_with(home) && !line.starts_with(&bundled));
            } else if *line == "</skills>" {
                skipping = false;
            }
            !skipping
        })
        .collect();
    kept.join("\n")
        .replace("\n\n<skills>\n</skills>", "")
        .replace(&bundled, "skills/")
}
