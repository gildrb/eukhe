//! eukhe settings as the Harness settings source: the global
//! `<agent_dir>/settings.json` merged with the project
//! `<cwd>/.eukhe/settings.json`, then the cfg layers (docs/control.md S4):
//! config.cfg (global, then project), the family this session inherited,
//! its profile (`agents/main.cfg`, or `subagent.cfg` and
//! `agents/<name>.cfg`), and its own sets. Re-read when any of those files
//! changes or the session's own state changes.

use std::collections::HashSet;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::SystemTime;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::{
    BackgroundMargin, ConversationStreamOptions, Extension, HarnessSettings, HarnessSettingsSource,
    PartialCompactionPolicy, PartialRetryPolicy, QueueMode, SubmissionDraft, ThresholdTokens,
    WriteSubmissionDraft,
};
use eukhe_durable::harness::Conversation;
use eukhe_durable::session::SessionResult;
use eukhe_types::cvar::{Aliases, Binds, Command};
use eukhe_types::pi_ai::{ModelThinkingLevel, Transport};
use futures::future::BoxFuture;
use futures::FutureExt;

use super::cvar_agent::{AgentState, CvarAgent};
use super::deps::{HostDeps, OpenedSession, ServiceStop};
use super::rlm::CustomNotice;
use crate::settings::cvar::{AgentLayer, CvarError, CvarWriteError, Target};
use crate::settings::types::{QueueModeSetting, ThinkingLevelSetting, TransportSetting};
use crate::settings::{SettingsError, SettingsManager, SettingsScope, CONFIG_DIR_NAME};

/// What a settings file looked like at the last load: `None` when absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FileStamp {
    modified: Option<SystemTime>,
    len: u64,
}

fn stamp(path: &Path) -> Option<FileStamp> {
    let metadata = std::fs::metadata(path).ok()?;
    Some(FileStamp {
        modified: metadata.modified().ok(),
        len: metadata.len(),
    })
}

struct Loaded {
    stamps: Vec<Option<FileStamp>>,
    manager: Arc<SettingsManager>,
    harness: Arc<HarnessSettings>,
    /// The aliases a command of this session runs: config.cfg's, then its
    /// profile's, then its own.
    aliases: Aliases,
}

/// The session's agent and its own state.
#[derive(Clone)]
struct Agent {
    agent: CvarAgent,
    state: AgentState,
}

struct State {
    agent: Agent,
    loaded: Loaded,
    notices: Notices,
}

/// The settings errors this session queued for the user (each distinct
/// error once), and the ones not shown yet.
#[derive(Default)]
struct Notices {
    queued: HashSet<(SettingsScope, String)>,
    unshown: Vec<SettingsError>,
}

impl Notices {
    /// Queue the errors of `manager` not queued before; `true` when one is
    /// new.
    fn note(&mut self, manager: &SettingsManager) -> bool {
        let before = self.unshown.len();
        for error in manager.errors() {
            if self.queued.insert((error.scope, error.message.clone())) {
                self.unshown.push(error.clone());
            }
        }
        self.unshown.len() > before
    }
}

/// eukhe settings of one session, re-read when a settings file changes
/// (modification time or length). Every read is a `stat` of each file.
/// Each load's errors (settings files, config.cfg, the profile, the
/// agent's aliases) are queued once for the `eukhe.settings` service,
/// which shows them as a row.
pub struct EukheSettings {
    cwd: PathBuf,
    agent_dir: PathBuf,
    paths: Vec<PathBuf>,
    /// Every queued follow-up joins the next run, whatever `followUpMode`
    /// says ([`EukheSettings::chat_memory_root`]).
    follow_ups_at_once: bool,
    state: Mutex<State>,
    /// Notified when a load queues a new error.
    unshown_ready: Arc<tokio::sync::Notify>,
}

impl EukheSettings {
    /// Settings of a root session working in `cwd`.
    #[must_use]
    pub fn new(cwd: impl Into<PathBuf>, agent_dir: impl Into<PathBuf>) -> Self {
        Self::open(cwd.into(), agent_dir.into(), CvarAgent::Root, false)
    }

    /// Settings of a root session with chat memory: a root call is a run,
    /// and a fresh call takes every queued message at once, joined into its
    /// one request (`OptChat` §6), so the follow-up queue mode is `all`
    /// whatever `followUpMode` says. The steering mode stays the setting's:
    /// it also decides the steers a running call takes at a tool boundary.
    #[must_use]
    pub fn chat_memory_root(cwd: impl Into<PathBuf>, agent_dir: impl Into<PathBuf>) -> Self {
        Self::open(cwd.into(), agent_dir.into(), CvarAgent::Root, true)
    }

    /// Settings of a session that is `agent` (its inherited family and
    /// profile files) working in `cwd`.
    #[must_use]
    pub fn with_agent(
        cwd: impl Into<PathBuf>,
        agent_dir: impl Into<PathBuf>,
        agent: CvarAgent,
    ) -> Self {
        Self::open(cwd.into(), agent_dir.into(), agent, false)
    }

    fn open(cwd: PathBuf, agent_dir: PathBuf, agent: CvarAgent, follow_ups_at_once: bool) -> Self {
        let mut paths = vec![
            agent_dir.join("settings.json"),
            cwd.join(CONFIG_DIR_NAME).join("settings.json"),
            agent_dir.join("config.cfg"),
            cwd.join(CONFIG_DIR_NAME).join("config.cfg"),
        ];
        paths.extend(
            agent
                .profile_files()
                .iter()
                .map(|file| agent_dir.join(file)),
        );
        let agent = Agent {
            agent,
            state: AgentState::default(),
        };
        let loaded = load(&cwd, &agent_dir, &paths, &agent, follow_ups_at_once);
        let mut notices = Notices::default();
        notices.note(&loaded.manager);
        Self {
            cwd,
            agent_dir,
            paths,
            follow_ups_at_once,
            state: Mutex::new(State {
                agent,
                loaded,
                notices,
            }),
            unshown_ready: Arc::new(tokio::sync::Notify::new()),
        }
    }

    #[must_use]
    pub fn cwd(&self) -> &Path {
        &self.cwd
    }

    #[must_use]
    pub fn agent_dir(&self) -> &Path {
        &self.agent_dir
    }

    /// The current settings (reloaded first when a file changed), with the
    /// session's family applied.
    #[must_use]
    pub fn manager(&self) -> Arc<SettingsManager> {
        Arc::clone(&self.refresh().loaded.manager)
    }

    /// The current settings as Harness settings.
    #[must_use]
    pub fn harness(&self) -> Arc<HarnessSettings> {
        Arc::clone(&self.refresh().loaded.harness)
    }

    /// Which agent this session is.
    #[must_use]
    pub fn agent(&self) -> CvarAgent {
        self.lock().agent.agent.clone()
    }

    /// The session's own sets and aliases.
    #[must_use]
    pub fn agent_state(&self) -> AgentState {
        self.lock().agent.state.clone()
    }

    /// Install the session's own state (read from or committed to its
    /// main conversation) and reload.
    pub fn set_agent_state(&self, state: AgentState) {
        let mut guard = self.lock();
        guard.agent.state = state;
        let loaded = load(
            &self.cwd,
            &self.agent_dir,
            &self.paths,
            &guard.agent,
            self.follow_ups_at_once,
        );
        self.install(&mut guard, loaded);
    }

    /// The agent state after `commands` run into the session's own sets
    /// (with its aliases); `None` when they change nothing. Nothing is
    /// installed: the caller commits the state first.
    ///
    /// # Errors
    ///
    /// The first command that does not apply (then none applies).
    pub fn plan(&self, commands: &[Command]) -> Result<Option<AgentState>, CvarError> {
        let guard = self.refresh();
        let mut cvars = guard.loaded.manager.cvars().clone();
        let mut aliases = guard.loaded.aliases.clone();
        // Binds belong to a client's binds.cfg: a session keeps none.
        let mut binds = Binds::default();
        if let Some(error) = cvars
            .execute(Target::Sets, commands, &mut aliases, &mut binds)
            .into_iter()
            .next()
        {
            return Err(error);
        }
        // The session's own aliases: the ones it had, then every alias the
        // commands defined or redefined.
        // A body that does not parse is in the manager's errors (`load`).
        let (mut own, _in_manager_errors) = guard.agent.state.alias_table();
        for (name, body) in aliases.iter() {
            if guard.loaded.aliases.body(name) != Some(body) {
                own.define(name.to_string(), body.to_vec());
            }
        }
        let state = AgentState::new(&cvars.agent().sets, &own);
        Ok((state != guard.agent.state).then_some(state))
    }

    /// Write each `set` / `toggle` of `commands` to the global config.cfg
    /// (the explicit global command, [`SettingsManager::run_global`]),
    /// then reload. The file I/O holds no lock of this session's state:
    /// readers keep the loaded settings until the reload swaps them in.
    ///
    /// # Errors
    ///
    /// The first command that does not apply (then none is written), or a
    /// failed write.
    pub fn run_global(&self, commands: &[Command]) -> Result<(), CvarWriteError> {
        let written = SettingsManager::create(&self.cwd, &self.agent_dir).run_global(commands);
        let agent = self.lock().agent.clone();
        let loaded = load(
            &self.cwd,
            &self.agent_dir,
            &self.paths,
            &agent,
            self.follow_ups_at_once,
        );
        let mut guard = self.lock();
        // A state installed meanwhile loaded after the write: it stays.
        if guard.agent.state == agent.state {
            self.install(&mut guard, loaded);
        }
        written
    }

    /// The settings errors queued since the last call (each distinct error
    /// of this session once), for the user.
    #[must_use]
    pub fn take_unshown_errors(&self) -> Vec<SettingsError> {
        std::mem::take(&mut self.lock().notices.unshown)
    }

    /// Notified when a load queues a new error
    /// ([`Self::take_unshown_errors`]).
    #[must_use]
    pub fn unshown_ready(&self) -> Arc<tokio::sync::Notify> {
        Arc::clone(&self.unshown_ready)
    }

    /// Install `loaded`, queueing its new errors.
    fn install(&self, state: &mut State, loaded: Loaded) {
        if state.notices.note(&loaded.manager) {
            self.unshown_ready.notify_one();
        }
        state.loaded = loaded;
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn refresh(&self) -> std::sync::MutexGuard<'_, State> {
        let mut guard = self.lock();
        let stamps: Vec<_> = self.paths.iter().map(|path| stamp(path)).collect();
        if stamps != guard.loaded.stamps {
            let loaded = load(
                &self.cwd,
                &self.agent_dir,
                &self.paths,
                &guard.agent,
                self.follow_ups_at_once,
            );
            self.install(&mut guard, loaded);
        }
        guard
    }
}

impl HarnessSettingsSource for EukheSettings {
    fn current(&self) -> Arc<HarnessSettings> {
        self.harness()
    }
}

/// The extension name.
pub const SETTINGS_EXTENSION: &str = "eukhe.settings";

/// The custom type of the row that shows settings errors (display-only).
pub const SETTINGS_ERROR_CUSTOM_TYPE: &str = "eukhe.settings_error";

/// The `eukhe.settings` extension of a session: no hooks, only the service
/// started at open that shows the session's settings errors (at open and
/// after each reload that finds a new one) as a row of its main
/// conversation.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    deps.add_service(Box::new(start));
    define_extension(Extension::named(SETTINGS_EXTENSION))
}

/// Start the error rows on the opened session; the stop ends the task.
/// Rows are submitted from the task, never from the service start (a
/// submission resumes scheduling, which a service start must not do).
fn start(opened: OpenedSession) -> BoxFuture<'static, SessionResult<Option<ServiceStop>>> {
    async move {
        let settings = Arc::clone(&opened.deps.settings);
        let ready = settings.unshown_ready();
        let close = Arc::new(tokio::sync::Notify::new());
        let close_signal = Arc::clone(&close);
        let subscription = opened.harness.subscribe_close(Arc::new(move || {
            close_signal.notify_one();
        }))?;
        let main = opened.main.clone();
        let task_close = Arc::clone(&close);
        let task = tokio::spawn(async move {
            loop {
                show_errors(&main, settings.take_unshown_errors()).await;
                tokio::select! {
                    () = ready.notified() => {}
                    () = task_close.notified() => break,
                }
            }
        });
        let stop: ServiceStop = Box::new(move || {
            async move {
                drop(subscription);
                close.notify_one();
                let _ = task.await;
            }
            .boxed()
        });
        Ok(Some(stop))
    }
    .boxed()
}

/// The row text of `errors`: one line each, with its scope.
fn settings_error_text(errors: &[SettingsError]) -> String {
    let mut text = "Settings errors (the rest of the settings apply):".to_string();
    for error in errors {
        let scope = match error.scope {
            SettingsScope::Global => "global",
            SettingsScope::Project => "project",
        };
        let _ = write!(text, "\n- {scope}: {}", error.message);
    }
    text
}

/// Submit the row of `errors` to `main` (none when empty). A row that
/// cannot be submitted is logged: it has no other place to go.
#[tracing::instrument(skip_all, fields(errors = errors.len()))]
async fn show_errors(main: &Conversation, errors: Vec<SettingsError>) {
    if errors.is_empty() {
        return;
    }
    let notice = CustomNotice::new(
        SETTINGS_ERROR_CUSTOM_TYPE,
        settings_error_text(&errors),
        true,
        None,
    );
    let submitted = match notice.draft() {
        Ok(entry) => main
            .submit(
                SubmissionDraft::Write(WriteSubmissionDraft {
                    request_id: None,
                    entry,
                }),
                &BACKGROUND_CONTEXT,
            )
            .await
            .map(drop)
            .map_err(anyhow::Error::from),
        Err(error) => Err(anyhow::Error::from(error)),
    };
    if let Err(error) = submitted {
        tracing::warn!(%error, "settings error row not delivered");
    }
}

fn load(
    cwd: &Path,
    agent_dir: &Path,
    paths: &[PathBuf],
    agent: &Agent,
    follow_ups_at_once: bool,
) -> Loaded {
    // Stamps are taken before the read: a write racing the read changes
    // the stamp again, and the next read reloads.
    let stamps = paths.iter().map(|path| stamp(path)).collect();
    let mut manager = SettingsManager::create(cwd, agent_dir);
    let (profile, profile_aliases, errors) = manager.read_profile(&agent.agent.profile_files());
    manager.push_errors(errors);
    let (own_aliases, alias_errors) = agent.state.alias_table();
    manager.push_errors(alias_errors);
    let mut aliases = manager.aliases().clone();
    for (name, body) in profile_aliases.iter().chain(own_aliases.iter()) {
        aliases.define(name.to_string(), body.to_vec());
    }
    let mut family: Vec<AgentLayer> = agent.agent.inherited().to_vec();
    family.push(AgentLayer {
        profile,
        sets: agent.state.sets.clone(),
    });
    manager.set_family(family);
    let mut harness = harness_settings(&manager);
    if follow_ups_at_once {
        harness.follow_up_mode = Some(QueueMode::All);
    }
    Loaded {
        stamps,
        manager: Arc::new(manager),
        harness: Arc::new(harness),
        aliases,
    }
}

/// eukhe settings in Harness terms, each through its getter (the cvar
/// table holds the defaults, equal to the Harness's own):
/// - `retry.{enabled, maxRetries, baseDelayMs}` -> the generation retry
///   policy; `retry.provider.maxRetryDelayMs` caps a server-requested delay
///   (`maxAgentDelayMs`).
/// - `retry.provider.timeoutMs` -> the request timeout;
///   `retry.provider.streamIdleTimeoutMs` -> the stream-idle deadline;
///   `retry.provider.streamRepeatLimit` -> the repetition guard (unset or
///   `0`: the pi-ai default, 64); `transport` -> the stream transport. A
///   stream option no layer sets stays absent: it is pinned with each
///   request, and the provider reads an absent transport differently from
///   an explicit `auto`.
/// - `compaction.{enabled, reserveTokens, keepRecentTokens}` -> the
///   compaction policy; `compaction.providerTokenCount` -> where its
///   threshold check gets the input tokens (the provider's own counter when
///   on, else the local estimate).
/// - `steeringMode` / `followUpMode` -> the queue modes.
/// - `maxToolRounds` -> the tool rounds one run may make (`0`: the
///   Harness default).
///
/// eukhe has no tool-execution setting: the Harness default applies (each
/// tool's own execution mode still serializes `ipython`).
#[must_use]
pub fn harness_settings(manager: &SettingsManager) -> HarnessSettings {
    let stream = ConversationStreamOptions {
        transport: manager.get_stream_transport().map(transport),
        timeout_ms: manager.get_provider_timeout_ms().map(u64_to_f64),
        stream_idle_timeout_ms: manager.get_stream_idle_timeout_ms().map(u64_to_f64),
        stream_repeat_limit: manager.get_stream_repeat_limit(),
        ..ConversationStreamOptions::default()
    };
    HarnessSettings {
        extensions: None,
        stream: Some(stream),
        retry: Some(PartialRetryPolicy {
            enabled: Some(manager.get_retry_enabled()),
            max_retries: Some(u32::try_from(manager.get_retry_max_retries()).unwrap_or(u32::MAX)),
            base_delay_ms: Some(u64_to_f64(manager.get_retry_base_delay_ms())),
            max_agent_delay_ms: Some(u64_to_f64(manager.get_max_retry_delay_ms())),
        }),
        compaction: Some(PartialCompactionPolicy {
            enabled: Some(manager.get_compaction_enabled()),
            reserve_tokens: Some(u64_to_f64(manager.get_compaction_reserve_tokens())),
            keep_recent_tokens: Some(u64_to_f64(manager.get_compaction_keep_recent_tokens())),
            // Early compaction: a background compaction starts a tenth of
            // the model's context window below the blocking threshold
            // (`contextWindow - reserveTokens`), so a turn that grows the
            // context by up to that much starts one before the context
            // crosses the blocking threshold (`bend/infer.bend` §5); the
            // blocking threshold and the overflow arm stay the safety nets.
            background: Some(BackgroundMargin::WindowPercent(10.0)),
            token_count: Some(if manager.get_compaction_provider_token_count() {
                ThresholdTokens::Provider
            } else {
                ThresholdTokens::Estimate
            }),
        }),
        progress: None,
        tool_execution: None,
        steering_mode: Some(queue_mode(manager.get_steering_mode())),
        follow_up_mode: Some(queue_mode(manager.get_follow_up_mode())),
        context_retention_ms: None,
        document_retention_ms: None,
        max_tool_rounds: Some(manager.get_max_tool_rounds()),
    }
}

#[allow(clippy::cast_precision_loss)] // Reason: settings values are JS numbers (far below 2^53).
fn u64_to_f64(value: u64) -> f64 {
    value as f64
}

fn queue_mode(mode: QueueModeSetting) -> QueueMode {
    match mode {
        QueueModeSetting::All => QueueMode::All,
        QueueModeSetting::OneAtATime => QueueMode::OneAtATime,
    }
}

fn transport(setting: TransportSetting) -> Transport {
    match setting {
        TransportSetting::Auto => Transport::Auto,
        TransportSetting::Sse => Transport::Sse,
        TransportSetting::WebSocket => Transport::Websocket,
        TransportSetting::WebSocketCached => Transport::WebsocketCached,
    }
}

/// A settings thinking level in the pi-ai vocabulary.
#[must_use]
pub fn thinking_level(setting: ThinkingLevelSetting) -> ModelThinkingLevel {
    match setting {
        ThinkingLevelSetting::Off => ModelThinkingLevel::Off,
        ThinkingLevelSetting::Minimal => ModelThinkingLevel::Minimal,
        ThinkingLevelSetting::Low => ModelThinkingLevel::Low,
        ThinkingLevelSetting::Medium => ModelThinkingLevel::Medium,
        ThinkingLevelSetting::High => ModelThinkingLevel::High,
        ThinkingLevelSetting::Xhigh => ModelThinkingLevel::Xhigh,
        ThinkingLevelSetting::Max => ModelThinkingLevel::Max,
    }
}

/// The level a session runs at when nothing requests one: the settings
/// default, else `medium` (TS `DEFAULT_THINKING_LEVEL`). Callers clamp it
/// to the model's ladder.
#[must_use]
pub fn default_thinking_level(manager: &SettingsManager) -> ModelThinkingLevel {
    manager
        .get_default_thinking_level()
        .map_or(ModelThinkingLevel::Medium, thinking_level)
}

#[cfg(test)]
mod tests {
    use eukhe_durable::harness::agent::resolve_settings;
    use eukhe_durable::harness::types::{CompactionPolicy, ConversationRetryPolicy, QueueMode};

    use super::*;

    fn write(path: &Path, text: &str) {
        std::fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
        std::fs::write(path, text).expect("write");
    }

    #[test]
    fn defaults_follow_eukhe_settings_defaults() {
        let dir = tempfile::tempdir().expect("tempdir");
        let settings = EukheSettings::new(dir.path().join("cwd"), dir.path().join("agent"));
        let resolved = resolve_settings(Some(&settings.current()));
        assert_eq!(
            resolved.retry,
            ConversationRetryPolicy {
                enabled: true,
                max_retries: 3,
                base_delay_ms: 2000.0,
                max_agent_delay_ms: Some(60000.0),
            }
        );
        assert_eq!(resolved.steering_mode, QueueMode::All);
        assert_eq!(resolved.follow_up_mode, QueueMode::OneAtATime);
        assert_eq!(resolved.stream, ConversationStreamOptions::default());
        assert_eq!(resolved.compaction.token_count, ThresholdTokens::Estimate);
    }

    /// The default keep window is 40,000 tokens, and with every catalog
    /// model it stays under the context size where automatic compaction
    /// starts, so a compaction there always has history to cut.
    #[test]
    #[allow(clippy::cast_precision_loss)] // Reason: token counts are JS numbers.
    fn the_default_keep_window_stays_under_every_catalog_compaction_start() {
        use eukhe_ai::models::CreateModelsOptions;
        use eukhe_ai::providers::all::builtin_models;

        let dir = tempfile::tempdir().expect("tempdir");
        let settings = EukheSettings::new(dir.path().join("cwd"), dir.path().join("agent"));
        let policy = resolve_settings(Some(&settings.current())).compaction;
        assert!((policy.keep_recent_tokens - 40_000.0).abs() < 0.5);
        let models = builtin_models(CreateModelsOptions::default()).get_models(None);
        assert!(!models.is_empty());
        for model in models {
            let window = model.context_window;
            if window == 0 {
                continue;
            }
            let start =
                window as f64 - policy.reserve_tokens - policy.background.tokens(window as f64);
            let keep = policy.keep_window(window);
            assert!(
                keep <= start.max(0.0) / 2.0 && keep <= policy.keep_recent_tokens,
                "{}/{}: window {window}, keep {keep}, start {start}",
                model.provider,
                model.id
            );
            // From a ~107k window on, the configured 40,000 applies whole.
            if start >= 2.0 * policy.keep_recent_tokens {
                assert!((keep - policy.keep_recent_tokens).abs() < 0.5);
            }
        }
    }

    #[test]
    fn settings_changes_are_reflected_on_the_next_read() {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent = dir.path().join("agent");
        let cwd = dir.path().join("cwd");
        std::fs::create_dir_all(&cwd).expect("cwd");
        write(
            &agent.join("settings.json"),
            r#"{"retry":{"maxRetries":7,"baseDelayMs":500,"provider":{"timeoutMs":9000,"maxRetryDelayMs":1000,"streamIdleTimeoutMs":45000,"streamRepeatLimit":12}},"compaction":{"enabled":false,"reserveTokens":1000,"keepRecentTokens":2000,"providerTokenCount":true},"steeringMode":"one-at-a-time","followUpMode":"all","transport":"sse"}"#,
        );
        let settings = EukheSettings::new(&cwd, &agent);
        let resolved = resolve_settings(Some(&settings.current()));
        assert_eq!(
            resolved.retry,
            ConversationRetryPolicy {
                enabled: true,
                max_retries: 7,
                base_delay_ms: 500.0,
                max_agent_delay_ms: Some(1000.0),
            }
        );
        assert_eq!(
            resolved.compaction,
            CompactionPolicy {
                enabled: false,
                reserve_tokens: 1000.0,
                keep_recent_tokens: 2000.0,
                background: BackgroundMargin::WindowPercent(10.0),
                token_count: ThresholdTokens::Provider,
            }
        );
        assert_eq!(resolved.steering_mode, QueueMode::OneAtATime);
        assert_eq!(resolved.follow_up_mode, QueueMode::All);
        assert_eq!(
            resolved.stream,
            ConversationStreamOptions {
                transport: Some(Transport::Sse),
                timeout_ms: Some(9000.0),
                stream_idle_timeout_ms: Some(45000.0),
                stream_repeat_limit: Some(12),
                ..ConversationStreamOptions::default()
            }
        );

        // A longer document is a different stamp even within the mtime
        // granularity.
        write(
            &agent.join("settings.json"),
            r#"{"retry":{"enabled":false},  "steeringMode":"all"}"#,
        );
        let resolved = resolve_settings(Some(&settings.current()));
        assert!(!resolved.retry.enabled);
        assert_eq!(resolved.steering_mode, QueueMode::All);

        // The project scope is read too.
        write(
            &cwd.join(".eukhe").join("settings.json"),
            r#"{"followUpMode":"all"}"#,
        );
        let resolved = resolve_settings(Some(&settings.current()));
        assert_eq!(resolved.follow_up_mode, QueueMode::All);
    }

    /// A chat-memory root takes every queued follow-up into its next run
    /// (`OptChat` §6) whatever `followUpMode` says, also after a reload;
    /// the steering mode stays the setting's.
    #[test]
    fn a_chat_memory_root_takes_every_follow_up_at_once() {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent = dir.path().join("agent");
        let cwd = dir.path().join("cwd");
        let settings = EukheSettings::chat_memory_root(&cwd, &agent);
        let resolved = resolve_settings(Some(&settings.current()));
        assert_eq!(resolved.steering_mode, QueueMode::All);
        assert_eq!(resolved.follow_up_mode, QueueMode::All);

        write(
            &agent.join("settings.json"),
            r#"{"steeringMode":"one-at-a-time","followUpMode":"one-at-a-time"}"#,
        );
        let resolved = resolve_settings(Some(&settings.current()));
        assert_eq!(resolved.steering_mode, QueueMode::OneAtATime);
        assert_eq!(resolved.follow_up_mode, QueueMode::All);
        assert_eq!(
            settings.manager().get_follow_up_mode(),
            QueueModeSetting::OneAtATime,
            "the setting itself reads back unchanged"
        );
    }

    #[test]
    fn unchanged_files_reuse_the_loaded_settings() {
        let dir = tempfile::tempdir().expect("tempdir");
        let settings = EukheSettings::new(dir.path().join("cwd"), dir.path().join("agent"));
        assert!(Arc::ptr_eq(&settings.current(), &settings.current()));
        assert!(Arc::ptr_eq(&settings.manager(), &settings.manager()));
    }

    /// Regression: a bad line of the agent's profile and an alias of its
    /// state that does not parse were only logged (or dropped without a
    /// word); they are now in the manager's errors with the config files'.
    #[test]
    fn profile_and_agent_alias_errors_reach_the_manager() {
        use crate::durable::cvar_agent::AliasEntry;
        use crate::settings::SettingsScope;

        let dir = tempfile::tempdir().expect("tempdir");
        let agent = dir.path().join("agent");
        write(&agent.join("agents/main.cfg"), "set nope on\n");
        let settings = EukheSettings::new(dir.path().join("cwd"), &agent);
        settings.set_agent_state(AgentState {
            sets: crate::settings::cvar::Sets::default(),
            aliases: vec![AliasEntry {
                name: "broken".to_string(),
                body: "set \"open".to_string(),
            }],
        });
        assert_eq!(
            settings
                .manager()
                .errors()
                .iter()
                .map(|error| (error.scope, error.message.clone()))
                .collect::<Vec<_>>(),
            vec![
                (
                    SettingsScope::Global,
                    "agents/main.cfg: no cvar `nope`".to_string()
                ),
                (
                    SettingsScope::Global,
                    "agent state: alias `broken` does not parse: line 1: a quote is not closed"
                        .to_string()
                ),
            ]
        );
    }
}
