//! eukhe settings as the Harness settings source: the global
//! `<agent_dir>/settings.json` merged with the project
//! `<cwd>/.eukhe/settings.json`, re-read when either file changes.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::SystemTime;

use eukhe_durable::harness::types::{
    ConversationStreamOptions, HarnessSettings, HarnessSettingsSource, PartialCompactionPolicy,
    PartialRetryPolicy, QueueMode,
};
use eukhe_types::pi_ai::{ModelThinkingLevel, Transport};

use crate::settings::types::{QueueModeSetting, ThinkingLevelSetting, TransportSetting};
use crate::settings::{SettingsManager, CONFIG_DIR_NAME};

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
    stamps: [Option<FileStamp>; 2],
    manager: Arc<SettingsManager>,
    harness: Arc<HarnessSettings>,
}

/// eukhe settings of one session, re-read when a settings file changes
/// (modification time or length). Every read is two `stat` calls.
pub struct EukheSettings {
    cwd: PathBuf,
    agent_dir: PathBuf,
    paths: [PathBuf; 2],
    /// Every queued follow-up joins the next run, whatever `followUpMode`
    /// says ([`EukheSettings::chat_memory_root`]).
    follow_ups_at_once: bool,
    loaded: Mutex<Loaded>,
}

impl EukheSettings {
    /// Settings of a session working in `cwd`.
    #[must_use]
    pub fn new(cwd: impl Into<PathBuf>, agent_dir: impl Into<PathBuf>) -> Self {
        Self::open(cwd.into(), agent_dir.into(), false)
    }

    /// Settings of a root session with chat memory: a root call is a run,
    /// and a fresh call takes every queued message at once, joined into its
    /// one request (`OptChat` §7), so the follow-up queue mode is `all`
    /// whatever `followUpMode` says. The steering mode stays the setting's:
    /// it also decides the steers a running call takes at a tool boundary.
    #[must_use]
    pub fn chat_memory_root(cwd: impl Into<PathBuf>, agent_dir: impl Into<PathBuf>) -> Self {
        Self::open(cwd.into(), agent_dir.into(), true)
    }

    fn open(cwd: PathBuf, agent_dir: PathBuf, follow_ups_at_once: bool) -> Self {
        let paths = [
            agent_dir.join("settings.json"),
            cwd.join(CONFIG_DIR_NAME).join("settings.json"),
        ];
        let loaded = load(&cwd, &agent_dir, &paths, follow_ups_at_once);
        Self {
            cwd,
            agent_dir,
            paths,
            follow_ups_at_once,
            loaded: Mutex::new(loaded),
        }
    }

    /// The current settings (reloaded first when a file changed).
    #[must_use]
    pub fn manager(&self) -> Arc<SettingsManager> {
        Arc::clone(&self.refresh().manager)
    }

    /// The current settings as Harness settings.
    #[must_use]
    pub fn harness(&self) -> Arc<HarnessSettings> {
        Arc::clone(&self.refresh().harness)
    }

    fn refresh(&self) -> std::sync::MutexGuard<'_, Loaded> {
        let mut loaded = self.loaded.lock().unwrap_or_else(PoisonError::into_inner);
        let stamps = [stamp(&self.paths[0]), stamp(&self.paths[1])];
        if stamps != loaded.stamps {
            *loaded = load(
                &self.cwd,
                &self.agent_dir,
                &self.paths,
                self.follow_ups_at_once,
            );
        }
        loaded
    }
}

impl HarnessSettingsSource for EukheSettings {
    fn current(&self) -> Arc<HarnessSettings> {
        self.harness()
    }
}

fn load(cwd: &Path, agent_dir: &Path, paths: &[PathBuf; 2], follow_ups_at_once: bool) -> Loaded {
    // Stamps are taken before the read: a write racing the read changes
    // the stamp again, and the next read reloads.
    let stamps = [stamp(&paths[0]), stamp(&paths[1])];
    let manager = SettingsManager::create(cwd, agent_dir);
    let mut harness = harness_settings(&manager);
    if follow_ups_at_once {
        harness.follow_up_mode = Some(QueueMode::All);
    }
    let harness = Arc::new(harness);
    Loaded {
        stamps,
        manager: Arc::new(manager),
        harness,
    }
}

/// eukhe settings in Harness terms:
/// - `retry.{enabled, maxRetries, baseDelayMs}` -> the generation retry
///   policy; `retry.provider.maxRetryDelayMs` caps a server-requested delay
///   (`maxAgentDelayMs`).
/// - `retry.provider.timeoutMs` -> the request timeout; `transport` -> the
///   stream transport.
/// - `compaction.{enabled, reserveTokens, keepRecentTokens}` -> the
///   compaction policy.
/// - `steeringMode` / `followUpMode` -> the queue modes (eukhe defaults:
///   `all` / `one-at-a-time`).
///
/// eukhe has no tool-execution setting: the Harness default applies (each
/// tool's own execution mode still serializes `ipython`).
#[must_use]
pub fn harness_settings(manager: &SettingsManager) -> HarnessSettings {
    let settings = manager.settings();
    let retry = settings.retry.as_ref();
    let provider = retry.and_then(|retry| retry.provider.as_ref());
    let compaction = settings.compaction.as_ref();
    let stream = ConversationStreamOptions {
        transport: settings.transport.map(transport),
        timeout_ms: provider
            .and_then(|provider| provider.timeout_ms)
            .map(u64_to_f64),
        ..ConversationStreamOptions::default()
    };
    HarnessSettings {
        extensions: None,
        stream: Some(stream),
        retry: Some(PartialRetryPolicy {
            enabled: retry.and_then(|retry| retry.enabled),
            max_retries: retry
                .and_then(|retry| retry.max_retries)
                .map(|retries| u32::try_from(retries).unwrap_or(u32::MAX)),
            base_delay_ms: retry.and_then(|retry| retry.base_delay_ms).map(u64_to_f64),
            max_agent_delay_ms: provider
                .and_then(|provider| provider.max_retry_delay_ms)
                .map(u64_to_f64),
        }),
        compaction: Some(PartialCompactionPolicy {
            enabled: compaction.and_then(|compaction| compaction.enabled),
            reserve_tokens: compaction
                .and_then(|compaction| compaction.reserve_tokens)
                .map(u64_to_f64),
            keep_recent_tokens: compaction
                .and_then(|compaction| compaction.keep_recent_tokens)
                .map(u64_to_f64),
            // The old engine had no background compaction: its threshold
            // arm fired at turn boundaries only, and the durable overflow
            // arm is the safety net. `0` keeps that behavior (the durable
            // default would start mid-run compactions 32768 tokens below
            // the blocking threshold).
            background_tokens: Some(0.0),
        }),
        progress: None,
        tool_execution: None,
        steering_mode: Some(queue_mode(manager.get_steering_mode())),
        follow_up_mode: Some(queue_mode(manager.get_follow_up_mode())),
        context_retention_ms: None,
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
    }

    #[test]
    fn settings_changes_are_reflected_on_the_next_read() {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent = dir.path().join("agent");
        let cwd = dir.path().join("cwd");
        std::fs::create_dir_all(&cwd).expect("cwd");
        write(
            &agent.join("settings.json"),
            r#"{"retry":{"maxRetries":7,"baseDelayMs":500,"provider":{"timeoutMs":9000,"maxRetryDelayMs":1000}},"compaction":{"enabled":false,"reserveTokens":1000,"keepRecentTokens":2000},"steeringMode":"one-at-a-time","followUpMode":"all","transport":"sse"}"#,
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
                background_tokens: 0.0,
            }
        );
        assert_eq!(resolved.steering_mode, QueueMode::OneAtATime);
        assert_eq!(resolved.follow_up_mode, QueueMode::All);
        assert_eq!(
            resolved.stream,
            ConversationStreamOptions {
                transport: Some(Transport::Sse),
                timeout_ms: Some(9000.0),
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
    /// (`OptChat` §7) whatever `followUpMode` says, also after a reload;
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
}
