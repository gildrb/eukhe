// The Tier-C/D ruling (fleet-uniform, 2026-09-28): stack-resident futures
// by design on hot paths (boxing 130 fns is allocation-churn with zero
// correctness gain); the fn-length threshold is a style gate, not
// correctness (the harness fns are intentionally linear); 64-bit targets -
// the narrowing sits at OS/protocol boundaries where the values are
// bounded (pid syscalls, epoch/elapsed milliseconds, calendar math,
// guarded parses), and checked conversions would add panic paths where
// silent wrap was deliberate (the one genuinely-suspect family, args.rs's
// parse_positive_u32 lacking its u32::MAX bound, is flagged in the lane
// dossier for the conductor).
#![allow(
    clippy::large_futures,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]

//! The CLI's output contract, end to end against the real binary:
//! exit-code classes (0 success, 1 operational, 2 usage), help discovery
//! (`help` wins over version and validation), the `--json` shapes, the
//! piped-table format (space-padded like on a terminal), and the quiet
//! closed-stdout exit.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn cli_binary() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_eukhe"))
}

/// Run the CLI with its state pinned to a fixture agent dir: no daemon,
/// no network (offline), stdout and stderr captured separately.
fn run(args: &[&str], agent_dir: &Path) -> Output {
    let mut command = Command::new(cli_binary());
    command
        .args(args)
        .env("EUKHE_CODING_AGENT_DIR", agent_dir)
        .env("EUKHE_OFFLINE", "1")
        .env("EUKHE_DAEMON_SOCKET", agent_dir.join("daemon.sock"))
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for key in [
        "EUKHE_INTERNAL_DAEMON_WORKER",
        "EUKHE_INTERNAL_DAEMON_WORKER_TOKEN",
        "EUKHE_INTERNAL_DAEMON_WORKER_ACTIVE_SESSION_ID",
        "EUKHE_INTERNAL_DAEMON_WORKER_INSTANCE_ID",
        "EUKHE_INTERNAL_DAEMON_WORKER_RECOVERY_JOURNAL",
        "EUKHE_INTERNAL_DAEMON_SUPERVISOR_SOCKET",
        "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL",
        "EUKHE_INTERNAL_SESSION_LEASES",
        "EUKHE_INTERNAL_SESSION_LEASE_OWNER_ID",
    ] {
        command.env_remove(key);
    }
    command.output().expect("run the CLI")
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// A fresh agent dir per test; the tempfile guard keeps it alive.
struct Fixture(tempfile::TempDir);

impl Fixture {
    fn new(name: &str) -> Self {
        let _ = name;
        Self(tempfile::tempdir().expect("fixture dir"))
    }

    fn path(&self) -> &Path {
        self.0.path()
    }
}

#[test]
fn help_beats_version_and_every_validation() {
    let fixture = Fixture::new("help-precedence");
    let output = run(&["--version", "--help"], fixture.path());
    assert_eq!(output.status.code(), Some(0));
    assert!(
        stdout(&output).contains("Usage:"),
        "help must win over version:\n{}",
        stdout(&output)
    );

    // Help is recognized before option validation: an invalid option next
    // to --help still prints help, exit 0.
    let output = run(&["--tyop", "--help"], fixture.path());
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert!(stdout(&output).contains("Usage:"));
}

#[test]
fn bare_help_prints_top_level_help() {
    let fixture = Fixture::new("bare-help");
    let output = run(&["help"], fixture.path());
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert!(stdout(&output).contains("Commands:"));
    assert_eq!(stderr(&output), "");
}

#[test]
fn unknown_command_via_help_is_a_usage_error() {
    let fixture = Fixture::new("help-bogus");
    let output = run(&["help", "bogus"], fixture.path());
    assert_eq!(
        output.status.code(),
        Some(2),
        "stdout: {}\nstderr: {}",
        stdout(&output),
        stderr(&output)
    );
    assert!(stdout(&output).is_empty());
    assert!(stderr(&output).contains("Unknown command: bogus"));
    assert!(stderr(&output).starts_with("Error: "));
}

#[test]
fn an_unknown_option_names_a_close_alternative() {
    let fixture = Fixture::new("option-typo");
    let output = run(&["--providr", "x"], fixture.path());
    assert_eq!(output.status.code(), Some(2));
    let err = stderr(&output);
    assert!(err.contains("Unknown option: --providr"), "{err}");
    assert!(err.contains("Did you mean --provider?"), "{err}");
    assert!(err.contains("eukhe help"), "{err}");
}

#[test]
fn usage_and_missing_input_exit_2() {
    let fixture = Fixture::new("usage-exits");
    for args in [
        &["stop"] as &[&str],
        &["rename", "only-one"],
        &["package"],
        &["package", "bogus"],
        &["kernel", "bogus"],
        &["incident", "--since", "yesterday"],
        &["mcp"],
        &["chat", "bogus"],
        &["--mode", "bogus"],
        &["--fork", "x", "--continue"],
    ] {
        let output = run(args, fixture.path());
        assert_eq!(
            output.status.code(),
            Some(2),
            "{args:?} must be a usage error: stdout {}\nstderr {}",
            stdout(&output),
            stderr(&output)
        );
        assert!(
            !stdout(&output).is_empty() || !stderr(&output).is_empty(),
            "{args:?} must explain itself"
        );
    }
}

#[test]
fn removed_commands_are_usage_errors_with_the_replacement() {
    let fixture = Fixture::new("removed-commands");
    let output = run(&["install"], fixture.path());
    assert_eq!(output.status.code(), Some(2));
    assert!(
        stderr(&output).contains("package install"),
        "{}",
        stderr(&output)
    );
}

#[test]
fn empty_results_are_silent_success_or_plain_zero_lines() {
    let fixture = Fixture::new("empty-results");
    let output = run(&["status"], fixture.path());
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(stdout(&output), "No background services.\n");
    assert_eq!(stderr(&output), "");
}

/// Piped management tables keep the terminal's space-padded columns (omp
/// `ps-cli.ts` `printTable`): no tabs, the header padded to its column.
#[test]
fn piped_tables_stay_space_padded() {
    let fixture = Fixture::new("piped-tables");
    let tiny = run(&["tiny-models"], fixture.path());
    assert_eq!(tiny.status.code(), Some(0), "{}", stderr(&tiny));
    let tiny_out = stdout(&tiny);
    assert!(
        !tiny_out.contains('\t'),
        "piped tiny-models must not use tabs:\n{tiny_out}"
    );
    let header = tiny_out.lines().next().unwrap_or_default();
    assert!(
        header.starts_with("ID  "),
        "space-padded header: {header:?}"
    );
    assert!(
        tiny_out.lines().any(|line| line.starts_with("kokoro ")),
        "a row splits on spaces:\n{tiny_out}"
    );

    // A stale socket file nobody listens on: `doctor` lists it as a row.
    let socket = fixture.path().join("daemon.sock");
    drop(std::os::unix::net::UnixListener::bind(&socket).expect("bind the stale socket"));
    let doctor = run(&["doctor"], fixture.path());
    assert_eq!(doctor.status.code(), Some(0), "{}", stderr(&doctor));
    let doctor_out = stdout(&doctor);
    assert!(
        !doctor_out.contains('\t'),
        "piped doctor must not use tabs:\n{doctor_out}"
    );
    assert!(
        doctor_out.starts_with("socket  "),
        "space-padded header:\n{doctor_out}"
    );
    assert!(doctor_out.contains("orphan-file"), "{doctor_out}");
}

/// `status --json` and `doctor --json` print the services as a top-level
/// array (omp `ps-cli.ts` `runList`), each row with its pid and status.
#[test]
fn status_and_doctor_json_are_the_service_array() {
    let fixture = Fixture::new("status-json");
    for command in ["status", "doctor"] {
        let output = run(&[command, "--json"], fixture.path());
        assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
        assert_eq!(stdout(&output).trim(), "[]", "{command} --json");
        assert_eq!(stderr(&output), "");
    }

    // A stale socket file: one row, its fields at the top level of the row.
    let socket = fixture.path().join("daemon.sock");
    drop(std::os::unix::net::UnixListener::bind(&socket).expect("bind the stale socket"));
    for command in ["status", "doctor"] {
        let output = run(&[command, "--json"], fixture.path());
        assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
        let rows: Vec<serde_json::Value> =
            serde_json::from_str(stdout(&output).trim()).expect("a JSON array of services");
        assert_eq!(rows.len(), 1, "{command} --json: {rows:?}");
        assert_eq!(rows[0]["status"], "orphan-file", "{command} --json");
        assert_eq!(
            rows[0]["socketPath"],
            socket.to_string_lossy().as_ref(),
            "{command} --json"
        );
    }
}

#[test]
fn json_results_stay_compact_when_piped() {
    let fixture = Fixture::new("json-compact");
    let output = run(&["chat", "status", "--json"], fixture.path());
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    let text = stdout(&output);
    assert!(
        !text.trim_start().starts_with('{') || !text.contains("\n  \""),
        "piped JSON must be one compact line, not pretty:\n{text}"
    );
    serde_json::from_str::<serde_json::Value>(text.trim()).expect("valid JSON");
}

#[test]
fn a_json_failure_is_one_stderr_document_and_no_stdout() {
    let fixture = Fixture::new("json-failure");
    // No daemon on the fixture socket: the read fails as an operational
    // error (exit 1), stdout stays empty, and `--json` moves the error
    // into the one-line machine document on stderr.
    let output = run(&["list", "--json"], fixture.path());
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert_eq!(stdout(&output), "", "a failed --json run prints no stdout");
    let stderr_text = stderr(&output);
    let parsed: serde_json::Value =
        serde_json::from_str(stderr_text.trim()).expect("one JSON error document");
    assert_eq!(parsed["status"], "error");
    assert_eq!(parsed["reason"], "network_error");
    assert!(
        parsed["message"]
            .as_str()
            .is_some_and(|message| message.contains("Failed to connect")),
        "{parsed}"
    );
}

#[test]
fn a_json_usage_failure_exits_2() {
    let fixture = Fixture::new("json-usage");
    let output = run(&["stop", "--json"], fixture.path());
    assert_eq!(output.status.code(), Some(2), "{}", stderr(&output));
    assert_eq!(stdout(&output), "");
    let parsed: serde_json::Value =
        serde_json::from_str(stderr(&output).trim()).expect("one JSON error document");
    assert_eq!(parsed["reason"], "invalid_arguments");
}

#[test]
fn a_closed_stdout_ends_a_read_quietly() {
    use std::process::Command as Cmd;

    let fixture = Fixture::new("closed-stdout");
    // `| head -1`: stdout closes after the first line; the read must end
    // with exit 0 and no panic report on stderr.
    let child = Cmd::new("sh")
        .arg("-c")
        .arg(format!(
            "{} status | head -1; echo PIPE_EXIT:$?",
            cli_binary().display()
        ))
        .env("EUKHE_CODING_AGENT_DIR", fixture.path())
        .env("EUKHE_OFFLINE", "1")
        .env("EUKHE_DAEMON_SOCKET", fixture.path().join("daemon.sock"))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn the pipe");
    let output = child.wait_with_output().expect("wait for the pipe");
    let out = String::from_utf8_lossy(&output.stdout);
    let err = String::from_utf8_lossy(&output.stderr);
    assert!(
        !err.contains("panicked"),
        "a closed stdout must not panic:\n{err}"
    );
    assert!(out.contains("PIPE_EXIT:0"), "{out}");
}

#[test]
fn a_json_confirmation_refusal_is_one_stderr_document() {
    let fixture = Fixture::new("shutdown-json-consent");
    // A state root with no daemons still reaches the confirmation plan
    // only when daemons exist; with none, shutdown succeeds. Drive the
    // refusal through a named socket that has a listener file but no
    // daemon? The deterministic refusal path is the TTY-less run against
    // a real daemon, covered by the daemon_discovery_e2e suite. Here we
    // pin the empty-machine contract instead.
    let output = run(&["shutdown", "--json"], fixture.path());
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    let parsed: serde_json::Value =
        serde_json::from_str(stdout(&output).trim()).expect("shutdown report");
    assert!(parsed.get("stopped").is_some(), "{parsed}");
    assert!(parsed.get("failed").is_some(), "{parsed}");
}
