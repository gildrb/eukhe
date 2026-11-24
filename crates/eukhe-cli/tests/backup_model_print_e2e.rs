//! `model.backups` failover in print mode: the session's primary
//! (`mock-anthropic/claude-mock`) fails its send with a dead end, the run
//! switches to the chain's first entry (`mock-openai/gpt-mock`), finishes
//! the interrupted turn there (tool call and answer), and writes one
//! `eukhe.model_backup_switch` row per switch; a fresh run of the same
//! session re-derives the switch from the still-dead primary; with every
//! entry dead the run ends once on the original error.

use std::path::Path;
use std::process::Output;

#[path = "support/durable_store.rs"]
mod durable_store;
#[path = "support/eukhe.rs"]
mod eukhe;
#[path = "support/provider_mock.rs"]
mod provider_mock;

use durable_store::{read_transcript, session_dirs};
use eukhe::{eukhe_command, scrub_provider_keys};
use provider_mock::{answer, Dialect, ProviderMock};

/// The anthropic error body of an organization that may not use its OAuth
/// login (the owner's `oauth_not_allowed_for_organization` rejection).
const OAUTH_REJECTED: &str = r#"{"type":"error","error":{"type":"permission_error","message":"403 oauth_not_allowed_for_organization: this organization may not use OAuth sign-in"}}"#;

/// The anthropic error body of a spent usage window (a known dead-end
/// text: `insufficient_quota`, `quota exceeded`).
const QUOTA_SPENT: &str = r#"{"type":"error","error":{"type":"insufficient_quota","message":"insufficient_quota: You have exceeded your quota"}}"#;

/// One `eukhe` run under `home`; its stdout. The run must succeed.
fn run(home: &Path, args: &[&str]) -> String {
    let output = run_raw(home, args);
    assert!(
        output.status.success(),
        "eukhe {args:?} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// One `eukhe` run under `home`, failures included.
fn run_raw(home: &Path, args: &[&str]) -> Output {
    let mut command = eukhe_command();
    scrub_provider_keys(&mut command);
    command
        .args(args)
        .env("HOME", home)
        .env("TMPDIR", home)
        .env("EUKHE_CODING_AGENT_DIR", home.join("agent"))
        .env("EUKHE_DAEMON_SOCKET", home.join("daemon.sock"))
        .env_remove("EUKHE_FAUX_SCRIPT")
        .env_remove("RLM_DEPTH")
        .current_dir(home)
        .output()
        .expect("the eukhe binary runs")
}

/// A home whose mock answers `fail_status` + `fail_body` on the
/// anthropic dialect and whose session model carries `backups`.
fn home_with(fail_status: u16, fail_body: &str, backups: &str) -> (tempfile::TempDir, ProviderMock) {
    let home = tempfile::TempDir::new().expect("temp home");
    let mock = ProviderMock::start();
    mock.fail_dialect(Dialect::AnthropicMessages, fail_status, fail_body);
    std::fs::create_dir_all(home.path().join("agent")).expect("agent dir");
    std::fs::write(
        home.path().join("agent/models.json"),
        mock.models_json().to_string(),
    )
    .expect("write models.json");
    std::fs::write(
        home.path().join("agent/settings.json"),
        format!(r#"{{"model":{{"backups":[{backups}]}}}}"#),
    )
    .expect("write settings.json");
    (home, mock)
}

/// How many logged requests a dialect saw.
fn count(log: &[provider_mock::Logged], dialect: Dialect) -> usize {
    log.iter()
        .filter(|logged| logged.dialect == dialect)
        .count()
}

/// A dead primary hands the session to its first backup: the interrupted
/// turn finishes there (tool call and answer), the notice lands once per
/// switch, and the next run of the session fails over the same way.
#[test]
fn an_auth_rejected_primary_switches_to_its_backup() {
    let (home, mock) = home_with(403, OAUTH_REJECTED, r#""mock-openai/gpt-mock""#);

    let first = run(
        home.path(),
        &[
            "-p",
            "--provider",
            "mock-anthropic",
            "--model",
            "claude-mock",
            "List the files.",
        ],
    );
    let second = run(home.path(), &["-c", "-p", "List them again."]);

    // Each run: the primary's one dead send (logged first), then the
    // backup's tool call and answer (log indexes 2-3 and 5-6).
    assert_eq!(first, format!("{}\n", answer(3)));
    assert_eq!(second, format!("{}\n", answer(6)));
    let log = mock.log();
    assert_eq!(
        count(&log, Dialect::AnthropicMessages),
        2,
        "one dead send per run"
    );
    assert_eq!(
        count(&log, Dialect::OpenAiResponses),
        4,
        "the backup served both turns"
    );

    let sessions = home.path().join("agent/sessions");
    let storage = session_dirs(&sessions)
        .into_iter()
        .next()
        .expect("the session's durable storage");
    let transcript = read_transcript(&storage);
    let notices = transcript.custom_rows("eukhe.model_backup_switch");
    assert_eq!(notices.len(), 2, "one notice per switch");
    for notice in notices {
        let content = serde_json::to_string(&notice["content"]).expect("notice content");
        assert!(
            content.contains(
                "switched to gpt-mock (mock-openai) because the provider rejected the sign-in"
            ),
            "the switch notice names the backup and the reason: {content}"
        );
    }
}

/// A usage-limit dead end fails over the same way, on the chain's own
/// trigger.
#[test]
fn a_usage_limited_primary_switches_to_its_backup() {
    let (home, mock) = home_with(429, QUOTA_SPENT, r#""mock-openai/gpt-mock""#);

    let first = run(
        home.path(),
        &[
            "-p",
            "--provider",
            "mock-anthropic",
            "--model",
            "claude-mock",
            "List the files.",
        ],
    );

    assert_eq!(first, format!("{}\n", answer(3)));
    let log = mock.log();
    assert_eq!(count(&log, Dialect::AnthropicMessages), 1);
    assert_eq!(count(&log, Dialect::OpenAiResponses), 2);
    let sessions = home.path().join("agent/sessions");
    let storage = session_dirs(&sessions)
        .into_iter()
        .next()
        .expect("the session's durable storage");
    let transcript = read_transcript(&storage);
    let notices = transcript.custom_rows("eukhe.model_backup_switch");
    assert_eq!(notices.len(), 1);
    let content = serde_json::to_string(&notices[0]["content"]).expect("notice content");
    assert!(
        content.contains(
            "switched to gpt-mock (mock-openai) because its usage limit was exhausted"
        ),
        "the switch notice names the backup and the reason: {content}"
    );
}

/// With the backup dead too, the run ends once on the failure: the
/// original error surfaces, no model is asked again.
#[test]
fn an_all_dead_chain_ends_once_on_the_original_error() {
    let (home, mock) = home_with(429, QUOTA_SPENT, r#""mock-openai/gpt-mock""#);
    mock.fail_dialect(Dialect::OpenAiResponses, 429, QUOTA_SPENT);

    let output = run_raw(
        home.path(),
        &[
            "-p",
            "--provider",
            "mock-anthropic",
            "--model",
            "claude-mock",
            "List the files.",
        ],
    );

    assert!(
        !output.status.success(),
        "an all-dead chain surfaces the failure"
    );
    // One send per model, then the end: no retry loop over the chain.
    let log = mock.log();
    assert_eq!(count(&log, Dialect::AnthropicMessages), 1);
    assert_eq!(count(&log, Dialect::OpenAiResponses), 1);
    let printed = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        printed.contains("insufficient_quota"),
        "the original error is surfaced: {printed}"
    );
}
