//! Interactive agent session over the daemon: attach to a live session, send
//! prompts, render streamed assistant output, and switch sessions. This is
//! the interactive product surface of `crates/eukhe-tui` (the port of the
//! interactive mode's daemon-attach path); the session loop itself keeps
//! running in the daemon worker, so closing the UI detaches instead of
//! stopping the session.
//!
//! Two UI sources drive the same loop: a crossterm terminal (raw mode, alt
//! screen) and a headless plan (programmatic input, captured frames). The
//! headless source is the verifier seam: it exercises the identical
//! attach/submit/stream/render path without a TTY.

use std::collections::VecDeque;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::Result;
use serde_json::{json, Value};

use crate::daemon_client::DaemonClient;
use crate::daemon_client::DaemonClientEvent;
use crate::daemon_reconnect::RecoveryKind;
use crate::exit_guard::ExitGuard;
use crate::keybindings::KeybindingsManager;
use crate::session_ui::SessionUi;
use crate::view::AgentView;

// The first-run onboarding concern (the sink and readiness seams, the flow
// task, the pane drive, and the phase that runs before the session screen)
// moved to the child module at the same tree position
// (interactive::onboarding); the facade re-exports keep the composition
// root's paths stable, and the phase binding keeps the run loop's bare
// call in scope.
mod onboarding;

use onboarding::{run_onboarding_phase, PaneDrive};

// The headless source (the scripted plan's vocabulary and the exit gate's
// settle) moved to the child module at the same tree position
// (interactive::headless); the facade re-exports keep the verifier seam's
// paths stable (the e2e harnesses), and the settle binding keeps the run
// loop's gate and the unit battery in scope.
mod headless;

use headless::HeadlessSettle;

// The render sink concern (the inline-terminal/headless renderer, the
// startup chrome seeding, the tmux keyboard check, the suspend-cycle
// terminal handoff) lives in interactive::render; the facade bindings keep
// the run loop's and the onboarding pane's bare paths in scope.
mod render;

pub use headless::{HeadlessPlan, HeadlessStep, UiMode};
pub use onboarding::{ModelReadiness, OnboardingSink, OnboardingTask};
use render::{apply_startup_chrome, check_tmux_keyboard_setup, Renderer, SurfaceExit};

// The reconnect machinery (the unexpected-loss hiccup loop and the
// announced shutdown's bounded
// recovery) moved to the child module at the same tree position
// (interactive::reconnect); the facade bindings keep the run loop's and
// the unit battery's bare paths in scope.
mod reconnect;

use reconnect::{arm_shutdown_recovery, ReconnectConnect, ReconnectLoop, SessionReconnect};
#[cfg(test)]
use reconnect::{DAEMON_SHUTDOWN_RECONNECT_WINDOW, SHUTDOWN_RECONNECT_RETRY};

// The run concern (the entry points and open routes, the terminal/headless
// surface loop with the reconnect and settle gates) moved to the child
// module at the same tree position (interactive::run); the facade
// re-exports keep the composition root's entry paths stable.
mod run;

// The startup open's failure routes (the agents-view fallback or the
// fatal return).
mod open_failure;

pub use run::run_interactive;

use crossterm::event::KeyEvent;
use crossterm::terminal;
use tokio::sync::mpsc;

// The inline unit battery moved to the child module at the same tree
// position (interactive::tests); its use-super glob keeps resolving
// through the facade's bindings and the pub contract.
#[cfg(test)]
mod tests;

/// Which session the interactive run opens.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SessionSelection {
    /// Create a fresh session (`create`, then `attach`).
    New,
    /// Create a fresh session bound under a parent session (the scoped
    /// agents view's new action): the create records `parent_session_file`
    /// as the session's `parentSessionPath` and runs it at `rlm_depth`
    /// (one below the parent), so every roster surface nests it under the
    /// parent.
    NewChild {
        parent_session_file: PathBuf,
        rlm_depth: u32,
    },
    /// Attach an existing live session by active session id.
    Attach(String),
    /// Create with `sessionPath`: reopen a saved session file (`--resume`).
    Resume(PathBuf),
}

/// Explicit model selection carried into every `create` config: the CLI
/// `--provider`/`--model`/`--api-key`/`--thinking` flags. Explicit flags are
/// authoritative end-to-end -- the daemon worker resolves its session model
/// and thinking level from this selection instead of a process-wide fallback.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ModelSelection {
    pub provider: Option<String>,
    pub model: Option<String>,
    pub api_key: Option<String>,
    /// The requested thinking level (`--thinking`). The worker clamps it to
    /// the model's supported levels and records the effective level.
    pub thinking: Option<eukhe_types::ai::ModelThinkingLevel>,
}

/// Options for one interactive run. `Debug` skips the opaque service
/// handles (the trait objects are not `Debug`).
#[derive(Clone)]
pub struct InteractiveOptions {
    pub socket_path: PathBuf,
    pub cwd: PathBuf,
    /// The model catalog for the `/model` picker (a startup snapshot
    /// resolved by the composition root; eukhe-tui stays eukhe-types only, so
    /// the registry itself lives above this crate). Each entry carries the
    /// levels and tiers the model offers, as the daemon serves them. The
    /// daemon's `get_model_catalog` refresh replaces it once it lands.
    pub model_catalog: Vec<eukhe_types::ai::CatalogModel>,
    /// Providers with configured auth for the picker's sign-in marking.
    pub model_configured_providers: std::collections::HashSet<String>,
    /// The settings recent-model list (`provider/id` keys, newest first).
    pub model_recent_models: Vec<String>,
    /// The settings default thinking level (the picker's effort seed for
    /// non-reasoning current models).
    pub default_thinking_level: Option<String>,
    /// Persistence directory for new sessions (`sessionDir` in the create
    /// config; defaults to the daemon's sessions dir when `None`).
    pub session_dir: Option<PathBuf>,
    /// Scripted faux-engine script path. Verification seam only; the product
    /// never sets it.
    pub script_path: Option<PathBuf>,
    /// Model flags to carry into the create config.
    pub model_selection: ModelSelection,
    /// The `--models` scope patterns (TS `parsed.models`): raw strings --
    /// `provider/id`, globs, `:thinking` suffixes -- that ride the create
    /// config's `models` field; the daemon resolves them against its
    /// registry into the session's scoped list (Alt+M cycling, the
    /// picker's scoped view). `None` leaves the scope unset.
    pub models: Option<Vec<String>>,
    /// Create without a session file (`--no-session`).
    pub no_session: bool,
    pub session: SessionSelection,
    /// Prompt sent immediately after attach (CLI message arguments).
    pub initial_message: Option<String>,
    /// The `terminal.showImages` setting, default true (TS `getShowImages`):
    /// whether image blocks render their metadata rows or the
    /// `[Image: ...]` placeholders.
    pub show_images: bool,
    /// Inline or fullscreen (`terminal.fullscreen`), resolved by the
    /// composition root; `/settings` can switch it while the chat runs.
    pub screen_mode: crate::screen_mode::ScreenMode,
    pub theme: String,
    /// The chat markdown fenced-code indent, resolved by the composition
    /// root from `markdown.codeBlockIndent` (TS `getCodeBlockIndent`;
    /// default two spaces).
    pub code_block_indent: String,
    /// The `/tree` selector's initial filter mode, resolved by the
    /// composition root from the `treeFilterMode` setting (default view).
    pub tree_filter_mode: String,
    /// The `branchSummary.skipPrompt` setting: `/tree` navigation skips the
    /// "Summarize branch?" question and navigates with no summary.
    pub branch_summary_skip_prompt: bool,
    /// Product version for the brand splash.
    pub version: String,
    /// Run the first-run onboarding flow before the session screen.
    pub onboarding: Option<OnboardingTask>,
    /// `/mcp login` / `/mcp logout`: the client-side auth flows the
    /// composition root provides (they drive the inline auth panel).
    /// `None` reports the commands as unavailable.
    pub client_auth: Option<crate::client_auth::ClientAuthCommandsHandle>,
    /// `/login` + `/logout`: the provider auth flows (credential storage,
    /// OAuth, the provider catalog) the composition root owns. `None`
    /// reports the commands as unavailable.
    pub provider_auth: Option<crate::provider_auth::ProviderAuthCommandsHandle>,
    /// The effective key binds (the user's `binds.cfg` over the default
    /// binds, loaded by the composition root; TS
    /// `KeybindingsManager.create()`): every hint and key handler renders
    /// and dispatches through this set.
    pub keybindings: KeybindingsManager,
    /// The client-owned prompt stash store shared across the chat views of
    /// this TUI process (TS `ClientPromptStashStore`): an editor draft
    /// left behind on a session switch returns when the session's chat
    /// reopens. The composition root owns one store per process, so the
    /// agents-view loop (view -> chat -> view) keeps every stashed draft.
    pub prompt_stash: std::sync::Arc<std::sync::Mutex<crate::prompt_stash::PromptStashStore>>,
    /// The attached session's persisted RLM depth (TS `sessionDepth`):
    /// the agents view passes it when it opens a row, and a subagent
    /// session renders its `depth N` tray label.
    pub session_rlm_depth: Option<u32>,
    /// Whether the opened session had direct children (TS
    /// `sessionHasChildren`).
    pub session_has_children: bool,
    /// The agents view handed the pane back from the dock's scoped panel
    /// (TS `scope_back`: the parent key and escape both reopen the scope
    /// root's chat): the reopened chat starts with the dock focused on
    /// the panel's own group -- the Subagents item -- at its first paint
    /// after the attach, instead of the prompt bar.
    pub restore_dock_focus: bool,
    /// The client-process settings the interactive commands read and
    /// persist (`/settings`). The
    /// composition root implements the seam over the real store; `None`
    /// reports the commands' persistence as unavailable.
    pub client_settings: Option<std::sync::Arc<dyn crate::client_settings::ClientSettings>>,
    /// Dictation into the editor draft (`app.stt.pushToTalk`,
    /// `app.stt.toggle`): the recorder and the `dictation` role the
    /// composition root gives. `None` reports dictation as not available.
    pub dictation: Option<crate::dictation::Dictation>,
    /// The background launcher of a daemon of this client's build: after an
    /// unexpected daemon loss, the recovery relaunches the daemon through
    /// it after the first failed reconnect. It starts a daemon only when
    /// none listens and never replaces one. `None` only reconnects (a test
    /// harness that owns its daemon).
    pub daemon_launcher: Option<crate::saved_sessions::SharedDaemonLauncher>,
}

// The opaque service handles (provider_auth,
// prompt_stash, client_settings) have no Debug surface;
// the launch-config rows above are the debug surface.
#[allow(clippy::missing_fields_in_debug)]
impl std::fmt::Debug for InteractiveOptions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InteractiveOptions")
            .field("socket_path", &self.socket_path)
            .field("cwd", &self.cwd)
            .field("session_dir", &self.session_dir)
            .field("script_path", &self.script_path)
            .field("model_selection", &self.model_selection)
            .field("models", &self.models)
            .field("model_catalog", &self.model_catalog)
            .field("no_session", &self.no_session)
            .field("session", &self.session)
            .field("initial_message", &self.initial_message)
            .field("theme", &self.theme)
            .field("screen_mode", &self.screen_mode)
            .field("code_block_indent", &self.code_block_indent)
            .field("version", &self.version)
            .field("onboarding", &self.onboarding)
            .field("client_auth", &self.client_auth)
            .field("keybindings", &self.keybindings.get_effective_config())
            .finish()
    }
}

impl InteractiveOptions {
    /// The `create` config carried on every new-session request (the
    /// agents view reuses it as the base of a resume's config -- TS's
    /// `AgentsViewModeOptions.config`).
    #[must_use]
    pub fn create_config(&self) -> Value {
        let mut config = json!({ "cwd": self.cwd.display().to_string() });
        if let Some(session_dir) = &self.session_dir {
            config["sessionDir"] = json!(session_dir.display().to_string());
        }
        if let Some(script) = &self.script_path {
            config["script"] = json!(script.display().to_string());
        }
        if let Some(provider) = &self.model_selection.provider {
            config["provider"] = json!(provider);
        }
        if let Some(model) = &self.model_selection.model {
            config["model"] = json!(model);
        }
        if let Some(api_key) = &self.model_selection.api_key {
            config["apiKey"] = json!(api_key);
        }
        if let Some(thinking) = self.model_selection.thinking {
            config["thinking"] = json!(thinking.wire_name());
        }
        // TS `runtimeConfigFromArgs` carries the raw `--models` patterns:
        // the daemon resolves them once per create (main.ts:838-851).
        if let Some(models) = &self.models {
            config["models"] = json!(models);
        }
        if let SessionSelection::NewChild {
            parent_session_file,
            rlm_depth,
        } = &self.session
        {
            config["parentSessionPath"] = json!(parent_session_file.to_string_lossy());
            config["rlmDepth"] = json!(rlm_depth);
        }
        config
    }
}

/// Result of an interactive run: session identity plus, in headless mode, the
/// rendered frames.
#[derive(Debug, Clone, Default)]
pub struct InteractiveOutcome {
    pub active_session_id: String,
    pub session_id: String,
    /// The TS `formatResumeHint` line (a resumable, flushed session), for
    /// the composition root to print after the terminal is restored.
    pub resume_hint: Option<String>,
    pub last_assistant_text: Option<String>,
    pub frames: Vec<String>,
    /// OSC 52 clipboard sequences emitted during the run (headless capture
    /// only; terminal runs write them to stdout directly).
    pub clipboard_emissions: Vec<String>,
    /// `/resume` requested the agents view next (return-to-session flow).
    pub return_to_agents_view: bool,
    /// The subagent summary line opened the agents view scoped to this
    /// session's subtree; `None` with `return_to_agents_view` means the
    /// plain view.
    pub agents_view_scope: Option<crate::agents_view::AgentsViewScope>,
    /// `/resume <selector>` requested this session next.
    pub selection_request: Option<SessionSelection>,
    /// A startup attach failed on a session that is truly gone: the run
    /// hands off to the agents view (`return_to_agents_view`) and this
    /// notice seeds the view's status line instead of the pane dying to
    /// the shell.
    pub agents_view_notice: Option<String>,
}

/// Inputs consumed by the UI loop. Terminal keys arrive one event at a time;
/// headless steps arrive as whole submissions.
enum UiInput {
    Key(KeyEvent),
    Paste(String),
    Submit(String),
    /// The headless `SubmitAndSettle` step (see [`HeadlessStep`]).
    SubmitAndSettle {
        text: String,
        timeout_ms: u64,
    },
    /// One materialized input-idle tick (the headless `SettleIdle` step).
    SettleIdle,
    WaitIdle {
        timeout_ms: u64,
    },
    /// The headless `WaitRender` barrier's condition: a frame rendered
    /// after arming must contain `needle`.
    WaitRender {
        needle: String,
        timeout_ms: u64,
    },
    /// The headless `WaitGone` barrier's condition: the newest frame must
    /// no longer contain `needle`.
    WaitGone {
        needle: String,
        timeout_ms: u64,
    },
    /// The terminal was resized: the next draw replays the history at
    /// the new geometry.
    Resize,
    /// A wheel notch over a fullscreen surface: scrolls the transcript
    /// window (inline, nothing scrolls).
    Scroll(crate::view::ScrollRequest),
    HeadlessDone,
}
