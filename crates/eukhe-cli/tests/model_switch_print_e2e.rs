//! Changing models mid-session in print mode: three `-p` runs continue one
//! session (`--continue`) on Anthropic Messages, then `OpenAI` Responses,
//! then Anthropic Messages again, each run with a `bash` tool call and its
//! result, against a loopback provider serving both APIs. Every request is
//! held to its API's rules (tool ids and their pairing, only the target's
//! own reasoning replayed natively), and the continued runs carry the
//! session's thinking level to the new model.

use std::path::Path;

#[path = "support/eukhe.rs"]
mod eukhe;
#[path = "support/provider_mock.rs"]
mod provider_mock;

use eukhe::{eukhe_command, scrub_provider_keys};
use provider_mock::{answer, replay, switched_session_replays, ProviderMock, Replay};

/// One `eukhe` run under `home`; its stdout.
fn run(home: &Path, args: &[&str]) -> String {
    let mut command = eukhe_command();
    scrub_provider_keys(&mut command);
    let output = command
        .args(args)
        .env("HOME", home)
        .env("TMPDIR", home)
        .env("EUKHE_CODING_AGENT_DIR", home.join("agent"))
        .env("EUKHE_DAEMON_SOCKET", home.join("daemon.sock"))
        .env_remove("EUKHE_FAUX_SCRIPT")
        .env_remove("RLM_DEPTH")
        .current_dir(home)
        .output()
        .expect("the eukhe binary runs");
    assert!(
        output.status.success(),
        "eukhe {args:?} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
fn continued_print_runs_switch_api_with_tool_calls_and_keep_the_thinking_level() {
    let home = tempfile::TempDir::new().expect("temp home");
    let mock = ProviderMock::start();
    std::fs::create_dir_all(home.path().join("agent")).expect("agent dir");
    std::fs::write(
        home.path().join("agent/models.json"),
        mock.models_json().to_string(),
    )
    .expect("write models.json");

    let anthropic = ["--provider", "mock-anthropic", "--model", "claude-mock"];
    let openai = ["--provider", "mock-openai", "--model", "gpt-mock"];
    let outputs = [
        run(
            home.path(),
            &[
                &["-p", "--thinking", "low"],
                &anthropic[..],
                &["List the files."],
            ]
            .concat(),
        ),
        run(
            home.path(),
            &[&["-c", "-p"], &openai[..], &["List them again."]].concat(),
        ),
        run(
            home.path(),
            &[&["-c", "-p"], &anthropic[..], &["Once more."]].concat(),
        ),
    ];

    assert_eq!(
        outputs,
        [answer(2), answer(4), answer(6)].map(|text| format!("{text}\n"))
    );
    assert_eq!(
        mock.log().iter().map(replay).collect::<Vec<Replay>>(),
        switched_session_replays()
    );
}
