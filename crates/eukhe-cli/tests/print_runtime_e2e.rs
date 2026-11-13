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

//! End-to-end print-runtime verification: the real binary, an isolated HOME,
//! and the scripted faux provider (`EUKHE_FAUX_SCRIPT`) drive the complete
//! pipeline — CLI parse, session assembly, agent loop, tool bridge seam, event
//! emission, headless terminal selection — deterministically.

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

#[path = "support/durable_store.rs"]
mod durable_store;

use durable_store::{read_transcript, session_dirs};

fn run(args: &[&str], script: &serde_json::Value) -> (String, String, i32) {
    let home = tempfile::TempDir::new().unwrap();
    let output = eukhe_command()
        .args(args)
        .env("HOME", home.path())
        .env("EUKHE_AGENT_DIR", home.path().join("agent"))
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        .env_remove("RLM_DEPTH")
        .current_dir(home.path())
        .output()
        .expect("binary present");
    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
        output.status.code().unwrap_or(-1),
    )
}

#[test]
fn print_mode_text_output_matches_the_scripted_response() {
    let script = serde_json::json!({ "responses": ["first answer"] });
    let (stdout, stderr, code) = run(&["-p", "say something"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "first answer\n");
    assert_eq!(stderr, "");
}

#[test]
fn print_mode_multi_prompt_consumes_responses_in_order() {
    let script = serde_json::json!({ "responses": ["first answer", "second answer"] });
    let (stdout, _, code) = run(&["-p", "one", "two"], &script);
    assert_eq!(code, 0);
    // The terminal result is the final response.
    assert_eq!(stdout, "second answer\n");
}

#[test]
fn print_mode_json_streams_ts_shaped_events() {
    let script = serde_json::json!({ "responses": ["json answer"] });
    let (stdout, stderr, code) = run(&["--mode", "json", "-p", "hi"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    let lines: Vec<serde_json::Value> = stdout
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()
        .unwrap();
    // Header first, then the loop lifecycle.
    assert_eq!(lines[0]["type"], "session");
    assert_eq!(lines[0]["version"], 3);
    assert!(lines[0]["timestamp"].is_string());
    assert_eq!(lines[0]["rlmDepth"], 0);
    let types: Vec<&str> = lines
        .iter()
        .map(|line| line["type"].as_str().unwrap_or_default())
        .collect();
    assert_eq!(types[1], "agent_start");
    assert!(types.contains(&"turn_start"));
    assert!(types.contains(&"message_start"));
    assert!(types.contains(&"message_end"));
    assert!(types.contains(&"turn_end"));
    // The user message carries the prompt; the assistant carries the response.
    let user = lines
        .iter()
        .find(|line| line["type"] == "message_start" && line["message"]["role"] == "user")
        .unwrap();
    assert_eq!(user["message"]["content"][0]["text"], "hi");
    let assistant = lines
        .iter()
        .find(|line| line["type"] == "message_end" && line["message"]["role"] == "assistant")
        .unwrap();
    assert_eq!(assistant["message"]["content"][0]["text"], "json answer");
    assert_eq!(assistant["message"]["stopReason"], "stop");
    // The agent ends after the turn.
    assert_eq!(*types.last().unwrap(), "agent_end");
}

/// `--no-skills` and `--no-prompt-templates` stop discovery for print mode:
/// an agent-dir skill or template no longer expands its `/skill:<name>` or
/// `/<template>` prompt (TS resource loader `noSkills`/
/// `noPromptTemplates`); without them both expand.
#[test]
fn print_mode_no_discovery_flags_stop_skill_and_template_expansion() {
    let home = isolated_home();
    let agent = home.path().join(".eukhe");
    std::fs::create_dir_all(agent.join("skills/agent-skill")).unwrap();
    std::fs::write(
        agent.join("skills/agent-skill/SKILL.md"),
        "---\nname: agent-skill\ndescription: A test skill.\n---\n# agent-skill\nSay KIWI.\n",
    )
    .unwrap();
    std::fs::create_dir_all(agent.join("prompts")).unwrap();
    std::fs::write(
        agent.join("prompts/agent-tpl.md"),
        "---\ndescription: A test template\n---\nAgent template body.\n",
    )
    .unwrap();
    let user_text = |args: &[&str]| {
        let script = serde_json::json!({ "responses": ["ok"] });
        let (stdout, stderr, code) = run_in_home(home.path(), args, &script);
        assert_eq!(code, 0, "stderr: {stderr}");
        stdout
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .find(|line| line["type"] == "message_start" && line["message"]["role"] == "user")
            .map(|line| line["message"]["content"][0]["text"].clone())
            .expect("the user message")
    };
    let expanded = |text: &serde_json::Value, needle: &str| {
        text.as_str().is_some_and(|text| text.contains(needle))
    };
    let skill = user_text(&["--mode", "json", "-p", "/skill:agent-skill"]);
    assert!(expanded(&skill, "Say KIWI."), "{skill}");
    let template = user_text(&["--mode", "json", "-p", "/agent-tpl"]);
    assert!(expanded(&template, "Agent template body."), "{template}");
    let skill = user_text(&["--mode", "json", "--no-skills", "-p", "/skill:agent-skill"]);
    assert_eq!(skill, "/skill:agent-skill");
    let template = user_text(&[
        "--mode",
        "json",
        "--no-prompt-templates",
        "-p",
        "/agent-tpl",
    ]);
    assert_eq!(template, "/agent-tpl");
}

/// A `codemode` script's nested calls are part of the `codemode` call: the
/// json stream carries one tool start/end pair, the model's call, which
/// succeeds with the script's result. Its nested `read`s never show as
/// model calls, let alone failed ones ("Tool execution ended without a
/// result").
#[test]
fn print_mode_json_streams_only_the_model_call_of_a_codemode_script() {
    let home = isolated_home();
    std::fs::write(home.path().join("a.txt"), "alpha\n").unwrap();
    std::fs::write(home.path().join("b.txt"), "beta\n").unwrap();
    let code = concat!(
        "const a = await tools.read({ i: \"Reading a\", path: \"a.txt\" });\n",
        "const b = await tools.read({ i: \"Reading b\", path: \"b.txt\" });\n",
        "return (a.includes(\"alpha\") ? \"alpha\" : \"?\") + \"+\" + (b.includes(\"beta\") ? \"beta\" : \"?\");",
    );
    let script = serde_json::json!({ "responses": [
        { "content": [{ "type": "toolCall", "name": "codemode", "arguments": { "code": code } }] },
        "done",
    ] });
    let (stdout, stderr, status) = run_in_home(
        home.path(),
        &["--mode", "json", "-p", "run the script"],
        &script,
    );
    assert_eq!(status, 0, "stderr: {stderr}");
    let events: Vec<serde_json::Value> = stdout
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()
        .unwrap();
    let tool_frames: Vec<&serde_json::Value> = events
        .iter()
        .filter(|event| {
            event["type"]
                .as_str()
                .is_some_and(|kind| kind.starts_with("tool_execution_"))
        })
        .collect();
    let starts_and_ends: Vec<(&str, &str)> = tool_frames
        .iter()
        .filter(|event| event["type"] != "tool_execution_update")
        .map(|event| {
            (
                event["type"].as_str().unwrap(),
                event["toolName"].as_str().unwrap(),
            )
        })
        .collect();
    assert_eq!(
        starts_and_ends,
        [
            ("tool_execution_start", "codemode"),
            ("tool_execution_end", "codemode")
        ],
        "{tool_frames:#?}"
    );
    let call_id = &tool_frames[0]["toolCallId"];
    assert!(
        tool_frames
            .iter()
            .all(|event| event["toolCallId"] == *call_id),
        "{tool_frames:#?}"
    );
    let end = tool_frames.last().unwrap();
    assert_eq!(end["isError"], false, "{end:#}");
    let text = end["result"]["content"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|block| block["text"].as_str())
        .collect::<String>();
    assert!(text.contains("alpha+beta"), "{end:#}");
}

#[test]
fn print_mode_reports_provider_errors_as_exit_one() {
    // No responses queued: the faux provider returns an error stop reason.
    let script = serde_json::json!({ "responses": [] });
    let (stdout, stderr, code) = run(&["-p", "hi"], &script);
    assert_eq!(code, 1);
    assert_eq!(stdout, "");
    assert_ne!(stderr, "");
}

// ---------------------------------------------------------------------------
// Session persistence (headless print sessions must land on disk)
// ---------------------------------------------------------------------------

fn isolated_home() -> tempfile::TempDir {
    tempfile::TempDir::new().unwrap()
}

fn run_in_home(
    home: &std::path::Path,
    args: &[&str],
    script: &serde_json::Value,
) -> (String, String, i32) {
    let output = eukhe_command()
        .args(args)
        .env("HOME", home)
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        // Keep the isolated HOME authoritative: ambient agent/session dir
        // overrides from the test environment must not leak in.
        .env_remove("EUKHE_CODING_AGENT_DIR")
        .env_remove("EUKHE_SESSION_DIR")
        .env_remove("EUKHE_CODING_AGENT_SESSION_DIR")
        .env_remove("RLM_DEPTH")
        .current_dir(home)
        .output()
        .expect("binary present");
    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
        output.status.code().unwrap_or(-1),
    )
}

/// The durable session storages a run left (`<sessions>/<id>/`).
fn session_files(home: &std::path::Path) -> Vec<std::path::PathBuf> {
    session_dirs(&home.join(".eukhe/sessions"))
}

fn storage_id(dir: &std::path::Path) -> String {
    dir.file_name().unwrap().to_string_lossy().into_owned()
}

/// The session paths holding a runtime lease right now (the owner records
/// under the agent dir's `session-leases`).
fn leased_session_files(home: &std::path::Path) -> Vec<String> {
    let mut leased = Vec::new();
    let Ok(entries) = std::fs::read_dir(home.join(".eukhe/session-leases")) else {
        return leased;
    };
    for entry in entries.flatten() {
        let Ok(text) = std::fs::read_to_string(entry.path().join("owner.json")) else {
            continue;
        };
        let Ok(owner) = serde_json::from_str::<serde_json::Value>(&text) else {
            continue;
        };
        if let Some(path) = owner.get("sessionPath").and_then(serde_json::Value::as_str) {
            leased.push(path.to_string());
        }
    }
    leased
}

#[test]
fn print_mode_persists_a_session_file_by_default() {
    let home = isolated_home();
    let script = serde_json::json!({ "responses": ["persisted answer"] });
    let (stdout, stderr, code) = run_in_home(home.path(), &["-p", "hello there"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "persisted answer\n");

    let files = session_files(home.path());
    assert_eq!(files.len(), 1, "one session storage, got {files:?}");
    let transcript = read_transcript(&files[0]);

    // The main conversation's agent: the run's model, thinking, and cwd
    // (the isolated HOME, as the process sees it: canonical, so `/var`
    // reads `/private/var` on macOS).
    assert_eq!(transcript.agent["model"]["provider"], "faux");
    assert!(transcript.agent["thinkingLevel"].is_string());
    let cwd = home.path().canonicalize().expect("canonical home");
    assert_eq!(transcript.agent["cwd"], cwd.display().to_string());
    // The user prompt, then the assistant answer.
    let texts = transcript.message_texts();
    let user_at = texts.iter().position(|text| text == "hello there");
    let answer_at = texts.iter().position(|text| text == "persisted answer");
    assert!(user_at.is_some() && user_at < answer_at, "{texts:?}");
    assert_eq!(transcript.of_kind("pi.user").len(), 1);
    assert_eq!(transcript.of_kind("pi.assistant").len(), 1);
}

#[test]
fn print_mode_no_session_writes_nothing() {
    let home = isolated_home();
    let script = serde_json::json!({ "responses": ["gone"] });
    let (stdout, stderr, code) = run_in_home(home.path(), &["-p", "hi", "--no-session"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "gone\n");
    assert_eq!(session_files(home.path()), [] as [std::path::PathBuf; 0]);
}

#[test]
fn print_mode_resume_appends_to_the_same_session_file() {
    let home = isolated_home();
    let script = serde_json::json!({ "responses": ["first answer"] });
    let (stdout, stderr, code) = run_in_home(home.path(), &["-p", "first"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "first answer\n");
    let files = session_files(home.path());
    assert_eq!(files.len(), 1);

    let session_id = storage_id(&files[0]);
    let before = read_transcript(&files[0]).entries.len();

    // A uuid-v7 prefix selects the saved session; the run continues it.
    let selector = &session_id[..8];
    let script = serde_json::json!({ "responses": ["second answer"] });
    let (stdout, stderr, code) = run_in_home(
        home.path(),
        &["--resume", selector, "-p", "second"],
        &script,
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "second answer\n");

    let after_files = session_files(home.path());
    assert_eq!(after_files.len(), 1, "resume reuses the saved session");
    let transcript = read_transcript(&after_files[0]);
    assert!(
        transcript.entries.len() > before,
        "new entries were appended"
    );
    assert!(transcript.message_texts().contains(&"second".to_owned()));
}

#[test]
fn print_mode_continue_recent_reuses_the_latest_session() {
    let home = isolated_home();
    let script = serde_json::json!({ "responses": ["one"] });
    let (_, _, code) = run_in_home(home.path(), &["-p", "one"], &script);
    assert_eq!(code, 0);
    assert_eq!(session_files(home.path()).len(), 1);

    let script = serde_json::json!({ "responses": ["two"] });
    let (stdout, stderr, code) = run_in_home(home.path(), &["--continue", "-p", "two"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "two\n");
    assert_eq!(
        session_files(home.path()).len(),
        1,
        "continue reuses the saved session"
    );
}

/// A finished print run releases the session's runtime lease: the run
/// exits and no owner record survives under `session-leases`.
#[test]
fn print_mode_releases_the_session_lease_when_the_run_ends() {
    let home = isolated_home();
    let script = serde_json::json!({ "responses": ["leased answer"] });
    let (stdout, stderr, code) = run_in_home(home.path(), &["-p", "hi"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "leased answer\n");
    let files = session_files(home.path());
    assert_eq!(files.len(), 1, "one session file, got {files:?}");
    assert!(
        leased_session_files(home.path()).is_empty(),
        "the ended run left a lease owner behind"
    );
}

#[test]
fn print_mode_resume_unknown_selector_fails_with_browse_hint() {
    let home = isolated_home();
    let script = serde_json::json!({ "responses": [] });
    let (stdout, stderr, code) =
        run_in_home(home.path(), &["--resume", "deadbeef", "-p", "hi"], &script);
    assert_eq!(code, 1);
    assert_eq!(stdout, "");
    assert!(
        stderr.contains("No session found matching 'deadbeef'"),
        "stderr: {stderr}"
    );
    assert!(
        stderr.contains("Open eukhe and press left-arrow to browse sessions."),
        "stderr: {stderr}"
    );
}

/// Headless regression for thinking-level resolution: `--thinking max` on a
/// reasoning faux model (supported levels `off`..`high`) must persist the
/// clamped effective level in the session JSONL — the same clamp the
/// interactive daemon path now applies.
#[test]
fn print_mode_thinking_max_persists_the_clamped_high_level() {
    let home = isolated_home();
    // `reasoning: true` without a thinkingLevelMap: supported levels are
    // off/minimal/low/medium/high, so max clamps up-to-down to high.
    let script = serde_json::json!({ "reasoning": true, "responses": ["clamped answer"] });
    let (stdout, stderr, code) =
        run_in_home(home.path(), &["-p", "--thinking", "max", "hello"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "clamped answer\n");

    let files = session_files(home.path());
    assert_eq!(files.len(), 1, "one session storage, got {files:?}");
    assert_eq!(read_transcript(&files[0]).agent["thinkingLevel"], "high");
}

/// The clamp also applies on the way down: a non-reasoning faux model maps
/// any requested level to off.
#[test]
fn print_mode_thinking_clamps_to_off_for_non_reasoning_models() {
    let home = isolated_home();
    let script = serde_json::json!({ "responses": ["plain answer"] });
    let (stdout, stderr, code) =
        run_in_home(home.path(), &["-p", "--thinking", "high", "hello"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "plain answer\n");

    let files = session_files(home.path());
    assert_eq!(files.len(), 1, "one session storage, got {files:?}");
    assert_eq!(read_transcript(&files[0]).agent["thinkingLevel"], "off");
}

// ---------------------------------------------------------------------------
// Overflow compact-and-retry (TS `_checkCompaction` Case 1 in print mode)
// ---------------------------------------------------------------------------

/// Compaction settings into the isolated home's agent dir, resolved by the
/// session engine at assembly time.
fn write_compaction_settings(home: &std::path::Path, settings: &serde_json::Value) {
    let agent = home.join(".eukhe");
    std::fs::create_dir_all(&agent).unwrap();
    std::fs::write(agent.join("settings.json"), settings.to_string()).unwrap();
}

/// The TS overflow error shape as a faux response entry (the `content`
/// form carries the stop reason and error message through the print
/// harness's script parser; `delayMs` paces the retried turn's timestamp
/// past the compaction boundary, like a real provider round-trip).
fn overflow_error(delay_ms: u64) -> serde_json::Value {
    let mut entry = serde_json::json!({
        "content": [{ "type": "text", "text": "" }],
        "stopReason": "error",
        "errorMessage": "prompt is too long: 213462 tokens > 200000 maximum",
    });
    if delay_ms > 0 {
        entry["delayMs"] = serde_json::json!(delay_ms);
    }
    entry
}

/// The compactable settings: the `keepRecentTokens` cut keeps ~10 tokens,
/// so an overflow recovery with pre-cut history summarizes it.
fn compactable_settings() -> serde_json::Value {
    serde_json::json!({
        "compaction": { "enabled": true, "reserveTokens": 1, "keepRecentTokens": 10 }
    })
}

/// The reported-overflow failure text (TS `_checkCompaction` verbatim).
const OVERFLOW_RECOVERY_FAILED: &str = "Context overflow recovery failed after one compact-and-retry attempt. Try reducing context or switching to a larger-context model.";

/// The full compact-and-retry cycle (verified against the TS binary with
/// the same scripted provider): an overflow error drops the failed turn,
/// runs one compaction, re-issues the turn, and the second overflow ends
/// the run with the assistant error plus the reported failure row on
/// stderr, exit 1.
#[test]
fn print_mode_overflow_compacts_retries_once_then_reports() {
    let home = isolated_home();
    write_compaction_settings(home.path(), &compactable_settings());
    let script = serde_json::json!({
        "responses": [
            {"text": "seed reply"},
            overflow_error(0),
            {"text": "the summary"},
            overflow_error(50),
        ]
    });
    let seed = format!("seed turn {}", "x".repeat(48_000));
    let probe = format!("overflow probe {}", "x".repeat(48_000));
    let (stdout, stderr, code) = run_in_home(home.path(), &["-p", &seed, &probe], &script);
    assert_eq!(code, 1, "stderr: {stderr}");
    assert!(stdout.is_empty(), "stdout: {stdout}");
    let error_at = stderr
        .find("prompt is too long: 213462 tokens > 200000 maximum")
        .expect("the overflow error surfaces");
    let reported_at = stderr
        .find(OVERFLOW_RECOVERY_FAILED)
        .expect("the reported failure row surfaces");
    assert!(
        error_at < reported_at,
        "the primary error precedes the reported outcome row: {stderr}"
    );
    // The durable surface: one compaction entry, one failed outcome row,
    // and no re-added user message for the retried turn.
    let files = session_files(home.path());
    assert_eq!(files.len(), 1);
    let transcript = read_transcript(&files[0]);
    assert_eq!(
        transcript.of_kind("pi.compaction").len(),
        1,
        "one compaction entry"
    );
    let outcomes = transcript.custom_rows("compaction_outcome");
    let outcome = outcomes.first().expect("the durable outcome row");
    let outcome_content = serde_json::to_string(&outcome["content"]).unwrap();
    assert!(outcome_content.contains(OVERFLOW_RECOVERY_FAILED));
    assert_eq!(outcome["details"]["reason"], "overflow");
    assert_eq!(outcome["details"]["outcome"], "failed");
    assert_eq!(
        transcript.of_kind("pi.user").len(),
        2,
        "the retry re-issued without re-adding the prompt"
    );
}

/// The retry on the compacted context recovers the turn: the final answer
/// prints normally, exit 0, and the compaction entry is durable.
#[test]
fn print_mode_overflow_retry_recovers_the_turn() {
    let home = isolated_home();
    write_compaction_settings(home.path(), &compactable_settings());
    let script = serde_json::json!({
        "responses": [
            {"text": "seed reply"},
            overflow_error(0),
            {"text": "the summary"},
            {"text": "recovered reply"},
        ]
    });
    let seed = format!("seed turn {}", "x".repeat(48_000));
    let probe = format!("overflow probe {}", "x".repeat(48_000));
    let (stdout, stderr, code) = run_in_home(home.path(), &["-p", &seed, &probe], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "recovered reply\n");
    assert!(stderr.is_empty(), "stderr: {stderr}");
    let files = session_files(home.path());
    let transcript = read_transcript(&files[0]);
    assert_eq!(transcript.of_kind("pi.compaction").len(), 1);
    assert!(
        transcript.custom_rows("compaction_outcome").is_empty(),
        "no failure rows on a recovered retry"
    );
}

/// A provider failure the retry recovers: the answer prints, exit 0 (TS
/// print mode prints the last assistant message). The episode's
/// `provider_retry_outcome` row trails the answer in the transcript; it is
/// a disclosure, never the terminal result.
#[test]
fn print_mode_provider_retry_recovers_the_answer() {
    let home = isolated_home();
    write_compaction_settings(
        home.path(),
        &serde_json::json!({
            "retry": { "enabled": true, "maxRetries": 1, "baseDelayMs": 1 },
            "titles": { "generate": false }
        }),
    );
    let script = serde_json::json!({
        "responses": [
            {
                "content": [{ "type": "text", "text": "" }],
                "stopReason": "error",
                "errorMessage": "overloaded",
            },
            {"text": "recovered answer"},
        ]
    });
    let (stdout, stderr, code) = run_in_home(home.path(), &["-p", "hi"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "recovered answer\n", "stderr: {stderr}");
    let files = session_files(home.path());
    let transcript = read_transcript(&files[0]);
    let outcomes = transcript.custom_rows("provider_retry_outcome");
    assert_eq!(outcomes.len(), 1, "the episode's disclosure row");
    assert_eq!(outcomes[0]["details"]["success"], true);
}

/// An overflow with nothing compactable ends the run on the provider error
/// (pi-durable keeps the error turn): stderr carries the error, then the
/// skip warning row that names the oversized turn and its remedies (the
/// compaction dead-end warning), exit 1.
#[test]
fn print_mode_overflow_skip_surfaces_the_warning_row() {
    let home = isolated_home();
    write_compaction_settings(
        home.path(),
        &serde_json::json!({
            "compaction": { "enabled": true, "reserveTokens": 1, "keepRecentTokens": 100_000 }
        }),
    );
    let script = serde_json::json!({ "responses": [overflow_error(0)] });
    let (stdout, stderr, code) = run_in_home(home.path(), &["-p", "overflow probe"], &script);
    assert_eq!(code, 1, "stderr: {stderr}");
    assert!(stdout.is_empty(), "stdout: {stdout}");
    assert_eq!(
        stderr,
        "prompt is too long: 213462 tokens > 200000 maximum\nAuto-compaction skipped: The most recent turn alone is too large to reduce further; shrink it (e.g. clear large tool output) or switch to a larger-context model.\n"
    );
}

/// The json-mode event stream for the compact-and-retry cycle (verified
/// against the TS binary's session events): the `compaction_start` /
/// `compaction_end` pair with `reason: "overflow"` and `willRetry: true`,
/// the retried turn without a new user message, and the reported failure
/// surface — the outcome row's message pair, then the `compaction_end`
/// failure. json mode exits non-zero on the failed run like text mode
/// (`headless_exit`: a provider error is never a final answer).
#[test]
fn print_mode_overflow_json_streams_the_compaction_events() {
    let home = isolated_home();
    write_compaction_settings(home.path(), &compactable_settings());
    let script = serde_json::json!({
        "responses": [
            {"text": "seed reply"},
            overflow_error(0),
            {"text": "the summary"},
            overflow_error(50),
        ]
    });
    let seed = format!("seed turn {}", "x".repeat(48_000));
    let probe = format!("overflow probe {}", "x".repeat(48_000));
    let (stdout, stderr, code) = run_in_home(
        home.path(),
        &["--mode", "json", "-p", &seed, &probe],
        &script,
    );
    assert_eq!(code, 1, "stderr: {stderr}");
    let events: Vec<serde_json::Value> = stdout
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()
        .unwrap();
    // The pair before the retried turn: start, then end with willRetry.
    let start_at = events
        .iter()
        .position(|event| event["type"] == "compaction_start" && event["reason"] == "overflow")
        .expect("the compaction_start event");
    let success_at = events
        .iter()
        .position(|event| {
            event["type"] == "compaction_end"
                && event["reason"] == "overflow"
                && event["willRetry"] == true
        })
        .expect("the successful compaction_end event");
    assert!(start_at < success_at);
    assert_eq!(events[success_at]["result"]["summary"], "the summary");
    assert_eq!(events[success_at]["aborted"], false);
    // The retried turn's overflow error settles after the compaction.
    let retried_error_at = events
        .iter()
        .rposition(|event| {
            event["type"] == "message_end"
                && event["message"]["role"] == "assistant"
                && event["message"]["stopReason"] == "error"
        })
        .expect("the retried overflow error");
    assert!(
        success_at < retried_error_at,
        "the retried turn follows the compaction"
    );
    // No user message was re-added for the retry.
    let users = events
        .iter()
        .filter(|event| event["type"] == "message_start" && event["message"]["role"] == "user")
        .count();
    assert_eq!(users, 2);
    // The reported failure surface: the durable row's message pair, then
    // the `compaction_end` failure with the TS text and no severity.
    let row_at = events
        .iter()
        .position(|event| {
            event["type"] == "message_end"
                && event["message"]["customType"] == "compaction_outcome"
                && event["message"]["details"]["outcome"] == "failed"
        })
        .expect("the reported outcome row");
    let row_content = serde_json::to_string(&events[row_at]["message"]["content"]).unwrap();
    assert!(row_content.contains(OVERFLOW_RECOVERY_FAILED));
    assert_eq!(events[row_at]["message"]["details"]["reason"], "overflow");
    let reported_at = events
        .iter()
        .position(|event| {
            event["type"] == "compaction_end"
                && event["reason"] == "overflow"
                && event["willRetry"] == false
        })
        .expect("the reported compaction_end event");
    assert!(
        retried_error_at < row_at && row_at < reported_at,
        "the reported row pair precedes the end event"
    );
    assert_eq!(
        events[reported_at]["errorMessage"],
        OVERFLOW_RECOVERY_FAILED
    );
    assert!(
        events[reported_at].get("errorSeverity").is_none(),
        "automatic failures carry no error severity"
    );
    assert_eq!(
        events[start_at],
        serde_json::json!({"type": "compaction_start", "reason": "overflow"}),
        "the start event carries the TS shape"
    );
}

/// The overflow recovery across runs (the `--continue` shape): a run with
/// compaction disabled leaves the overflow error in the session; in the
/// resumed run the prompt's request overflows again, the one overflow
/// compaction runs, and the retried request answers normally.
#[test]
fn print_mode_stale_overflow_recovers_before_the_next_prompt_after_a_resume() {
    let home = isolated_home();
    // Run one: compaction disabled, the probe overflows.
    write_compaction_settings(
        home.path(),
        &serde_json::json!({
            "compaction": { "enabled": false, "reserveTokens": 1, "keepRecentTokens": 10 }
        }),
    );
    let script = serde_json::json!({
        "responses": [{"text": "seed reply"}, overflow_error(0)]
    });
    let seed = format!("seed turn {}", "x".repeat(48_000));
    let probe = format!("overflow probe {}", "x".repeat(48_000));
    let (stdout, stderr, code) = run_in_home(home.path(), &["-p", &seed, &probe], &script);
    assert_eq!(code, 1, "stderr: {stderr}");
    assert_eq!(stdout, "");

    // Run two: the resumed session with compaction enabled: the request
    // overflows, compacts, and retries.
    write_compaction_settings(home.path(), &compactable_settings());
    let script = serde_json::json!({
        "responses": [
            overflow_error(0),
            {"text": "the stale recovery summary"},
            {"text": "recovered after the resume"},
        ]
    });
    let (stdout, stderr, code) =
        run_in_home(home.path(), &["--continue", "-p", "next prompt"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "recovered after the resume\n");
    assert!(stderr.is_empty(), "stderr: {stderr}");
    // The recovery compaction is durable in the resumed session file.
    let files = session_files(home.path());
    assert_eq!(files.len(), 1, "the resume reuses the session file");
    assert_eq!(
        read_transcript(&files[0]).of_kind("pi.compaction").len(),
        1,
        "the overflow recovery compacted"
    );
}

// ---------------------------------------------------------------------------
// The json event stream's parity surface (message_update deltas: the omp
// `printableEvent` shape; threshold compaction: verified against the TS
// binary's print json stream over the same scripted faux provider).
// ---------------------------------------------------------------------------

/// The streaming deltas: pi-durable commits the in-flight partial at most
/// every 100 ms (TS `streamResponse`'s throttle), so between the
/// assistant's `message_start` (the first committed partial) and its
/// `message_end`, each `message_update` carries only the change since the
/// previous frame (omp `printableEvent`): never the accumulated partial,
/// which would re-serialize the whole message per frame and grow the
/// stream quadratically. The settled message rides `message_end` whole.
/// A slow stream makes the throttle publish.
#[test]
fn print_mode_json_streams_the_message_update_deltas() {
    const ANSWER: &str = "a streamed answer that takes a while to arrive in many small pieces";
    let home = isolated_home();
    let script = serde_json::json!({ "tokensPerSecond": 20, "responses": [ANSWER] });
    let (stdout, stderr, code) = run_in_home(home.path(), &["--mode", "json", "-p", "hi"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    let events: Vec<serde_json::Value> = stdout
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()
        .unwrap();
    let start_at = events
        .iter()
        .position(|event| {
            event["type"] == "message_start" && event["message"]["role"] == "assistant"
        })
        .expect("the assistant message_start");
    let end_at = events
        .iter()
        .position(|event| event["type"] == "message_end" && event["message"]["role"] == "assistant")
        .expect("the assistant message_end");
    let updates: Vec<&serde_json::Value> = events[start_at..end_at]
        .iter()
        .filter(|event| event["type"] == "message_update")
        .collect();
    assert!(
        updates
            .iter()
            .any(|update| update["assistantMessageEvent"]["type"] == "text_delta"),
        "the stream carries the deltas: {updates:?}"
    );
    let text = |event: &serde_json::Value| {
        event["message"]["content"][0]["text"]
            .as_str()
            .unwrap_or_default()
            .to_owned()
    };
    // The deltas extend the start's partial toward the settled answer.
    let mut rebuilt = text(&events[start_at]);
    for update in &updates {
        // The frame is the change alone, in the omp field order (`type`,
        // `assistantMessageEvent`; the JSON map preserves insertion order,
        // so this is the wire byte order).
        let keys: Vec<&str> = update
            .as_object()
            .unwrap()
            .keys()
            .map(String::as_str)
            .collect();
        assert_eq!(keys, ["type", "assistantMessageEvent"], "{update}");
        if update["assistantMessageEvent"]["type"] == "text_delta" {
            rebuilt.push_str(update["assistantMessageEvent"]["delta"].as_str().unwrap());
        }
        assert!(
            ANSWER.starts_with(&rebuilt),
            "a prefix of the answer: {rebuilt:?}"
        );
    }
    assert!(
        rebuilt.len() > text(&events[start_at]).len(),
        "the deltas add text"
    );
    assert_eq!(rebuilt, ANSWER, "the deltas complete the answer");
    assert_eq!(text(&events[end_at]), ANSWER);
}

/// An answer that settles before the 100 ms partial throttle commits its
/// last changes still streams to its end (print json emits every
/// `message_update`): the `message_start` partial plus the `text_delta`s
/// rebuild the answer, a `text_end` closes the block, then the settled
/// `message_end`.
#[test]
fn print_mode_json_streams_a_fast_answer_start_to_end() {
    let script = serde_json::json!({ "responses": ["fast answer"] });
    let (stdout, stderr, code) = run(&["--mode", "json", "-p", "hi"], &script);
    assert_eq!(code, 0, "stderr: {stderr}");
    let events: Vec<serde_json::Value> = stdout
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()
        .unwrap();
    let start_at = events
        .iter()
        .position(|event| {
            event["type"] == "message_start" && event["message"]["role"] == "assistant"
        })
        .expect("the assistant message_start");
    let end_at = events
        .iter()
        .position(|event| event["type"] == "message_end" && event["message"]["role"] == "assistant")
        .expect("the assistant message_end");
    let streamed: String = events[start_at]["message"]["content"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|block| block["text"].as_str())
        .collect();
    let updates: Vec<&serde_json::Value> = events[start_at..end_at]
        .iter()
        .filter(|event| event["type"] == "message_update")
        .collect();
    let kinds: Vec<&str> = updates
        .iter()
        .map(|update| update["assistantMessageEvent"]["type"].as_str().unwrap())
        .collect();
    assert!(!updates.is_empty(), "the stream carries updates");
    assert_eq!(kinds.last(), Some(&"text_end"), "{kinds:?}");
    let rebuilt = updates
        .iter()
        .filter(|update| update["assistantMessageEvent"]["type"] == "text_delta")
        .fold(streamed, |mut text, update| {
            text.push_str(update["assistantMessageEvent"]["delta"].as_str().unwrap());
            text
        });
    assert_eq!(rebuilt, "fast answer");
    assert_eq!(
        events[end_at]["message"]["content"][0]["text"],
        "fast answer"
    );
}

/// The threshold compaction (the pre-request check): once a turn's
/// context crossed the reserve headroom, the next run compacts before its
/// first request, so the `compaction_start`/`compaction_end` pair with the
/// `threshold` reason, the client-facing result, and `willRetry: false`
/// streams inside that run, between its user message and the answer.
#[test]
fn print_mode_json_streams_the_threshold_compaction_pair() {
    let home = isolated_home();
    write_compaction_settings(
        home.path(),
        &serde_json::json!({
            "compaction": { "enabled": true, "reserveTokens": 10_000, "keepRecentTokens": 10 }
        }),
    );
    // A small context window so the crossing turn crosses the blocking
    // threshold while its own request stays inside the window: the
    // blocking threshold is 24k window - 10k reserve = 14k tokens. The
    // thresholds read the context the last turn reached, as the provider
    // counted it (the faux provider counts the serialized context with
    // o200k_base): the seed turn stays below it, the ~12k-token crossing
    // message (one token per " history") takes the crossing turn past it
    // without putting its request past the window (which would compact
    // inside the crossing run), and the next run compacts before its
    // first request. That window's summarizer input budget is its floor
    // (3k tokens), so the summary runs one call per window: the seed turn,
    // the crossing message alone (clamped to the budget), and the crossing
    // reply.
    let script = serde_json::json!({
        "contextWindow": 24000,
        "responses": [
            {"text": "seed reply"},
            {"text": "crossing reply"},
            {"text": "the compaction summary"},
            {"text": "the compaction summary"},
            {"text": "the compaction summary"},
            {"text": "after reply"},
        ]
    });
    let first = "seed turn".to_string();
    let second = format!("crossing turn {}", "history ".repeat(12_000));
    let third = "after the crossing".to_string();
    let (stdout, stderr, code) = run_in_home(
        home.path(),
        &["--mode", "json", "-p", &first, &second, &third],
        &script,
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    let events: Vec<serde_json::Value> = stdout
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()
        .unwrap();
    let start_at = events
        .iter()
        .position(|event| event["type"] == "compaction_start")
        .expect("the compaction_start event");
    assert_eq!(
        events[start_at],
        serde_json::json!({ "type": "compaction_start", "reason": "threshold" })
    );
    // The pair runs inside the run after the crossing turn, the only
    // compaction: after that run's user message, before its answer.
    let last_user_end = events
        .iter()
        .rposition(|event| event["type"] == "message_end" && event["message"]["role"] == "user")
        .expect("the last user message");
    let answer_at = events
        .iter()
        .rposition(|event| {
            event["type"] == "message_start" && event["message"]["role"] == "assistant"
        })
        .expect("the last answer");
    assert!(last_user_end < start_at);
    assert_eq!(
        events
            .iter()
            .filter(|event| event["type"] == "compaction_start")
            .count(),
        1,
        "one compaction"
    );
    assert_eq!(
        events
            .iter()
            .filter(|event| event["type"] == "turn_start")
            .count(),
        3,
        "exactly three runs"
    );
    let end_at = events
        .iter()
        .position(|event| event["type"] == "compaction_end")
        .expect("the compaction_end event");
    assert!(start_at < end_at && end_at < answer_at);
    assert_eq!(events[end_at]["reason"], "threshold");
    assert_eq!(
        events[end_at]["result"]["summary"],
        "the compaction summary"
    );
    assert_eq!(events[end_at]["aborted"], false);
    assert_eq!(events[end_at]["willRetry"], false);
    assert!(events[end_at].get("errorMessage").is_none());
    // The compaction entry is durable.
    let files = session_files(home.path());
    assert_eq!(files.len(), 1);
    assert!(
        !read_transcript(&files[0])
            .of_kind("pi.compaction")
            .is_empty(),
        "the compaction persisted"
    );
}

/// Run the binary in the isolated HOME but a different working directory
/// (a "different project" for session-cwd resolution).
fn run_in_home_cwd(
    home: &std::path::Path,
    cwd: &std::path::Path,
    args: &[&str],
    script: &serde_json::Value,
) -> (String, String, i32) {
    let output = eukhe_command()
        .args(args)
        .env("HOME", home)
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        .env_remove("EUKHE_CODING_AGENT_DIR")
        .env_remove("EUKHE_SESSION_DIR")
        .env_remove("EUKHE_CODING_AGENT_SESSION_DIR")
        .env_remove("RLM_DEPTH")
        .current_dir(cwd)
        .output()
        .expect("binary present");
    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
        output.status.code().unwrap_or(-1),
    )
}

/// TS `createSessionManager`'s fork arm: `--fork <selector>` copies the
/// source session into a NEW session storage, and the run continues the
/// copy — the source keeps its entries untouched. (The fork's lineage is
/// the copied history; durable storages carry no `parentSession` header —
/// the json stream's session line reports it.)
#[test]
fn print_mode_fork_copies_the_session_into_a_new_file() {
    let home = isolated_home();
    let script = serde_json::json!({ "responses": ["first answer"] });
    let (stdout, _, code) = run_in_home(home.path(), &["-p", "first"], &script);
    assert_eq!(code, 0);
    assert_eq!(stdout, "first answer\n");
    let files = session_files(home.path());
    assert_eq!(files.len(), 1);
    let source = &files[0];
    let session_id = storage_id(source);

    // Fork by the same prefix selector shape resume uses.
    let selector = session_id[..8].to_string();
    let script = serde_json::json!({ "responses": ["second answer"] });
    let (stdout, stderr, code) = run_in_home(
        home.path(),
        &["--fork", selector.as_str(), "-p", "second"],
        &script,
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "second answer\n");

    // A new session storage; the source is untouched.
    let after = session_files(home.path());
    assert_eq!(after.len(), 2, "fork creates a new session storage");
    let fork = after
        .iter()
        .find(|path| path.as_path() != source.as_path())
        .expect("the fork storage");
    assert!(
        !read_transcript(source)
            .message_texts()
            .contains(&"second".to_owned()),
        "the source keeps its entries untouched"
    );
    // A fresh session id; the copied history answers the follow-up.
    assert_ne!(storage_id(fork), session_id);
    let texts = read_transcript(fork).message_texts();
    assert!(texts.contains(&"first".to_owned()), "{texts:?}");
    assert!(texts.contains(&"second".to_owned()), "{texts:?}");
    assert!(texts.contains(&"second answer".to_owned()), "{texts:?}");
}

/// `--fork` is the cross-project path: a session saved under another
/// project's cwd forks into the CURRENT one (the TS GLOBAL resolution
/// arm), while `--resume` still refuses it with the fork hint.
#[test]
fn print_mode_fork_imports_a_global_session_into_this_cwd() {
    let home = isolated_home();
    let project = home.path().join("other-project");
    std::fs::create_dir_all(&project).expect("project dir");
    // The cwd as the process sees it: canonical (`/private/var` on macOS).
    let project = project.canonicalize().expect("canonical project dir");
    let script = serde_json::json!({ "responses": ["global answer"] });
    let (stdout, _, code) = run_in_home(home.path(), &["-p", "origin"], &script);
    assert_eq!(code, 0);
    assert_eq!(stdout, "global answer\n");
    let files = session_files(home.path());
    assert_eq!(files.len(), 1);
    let session_id = storage_id(&files[0]);
    let selector = session_id[..8].to_string();

    // The same session is GLOBAL for the other project: resume refuses.
    let script = serde_json::json!({ "responses": ["no"] });
    let (stdout, stderr, code) = run_in_home_cwd(
        home.path(),
        &project,
        &["--resume", selector.as_str(), "-p", "refused"],
        &script,
    );
    assert_eq!(code, 1);
    assert_eq!(stdout, "");
    assert!(
        stderr.contains(&format!(
            "session {selector} belongs to a different project"
        )),
        "stderr: {stderr}"
    );
    assert!(stderr.contains(&format!("Pass --fork {selector}")));

    // ...and --fork imports it into this cwd.
    let script = serde_json::json!({ "responses": ["forked into the project"] });
    let (stdout, stderr, code) = run_in_home_cwd(
        home.path(),
        &project,
        &["--fork", selector.as_str(), "-p", "continue here"],
        &script,
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, "forked into the project\n");
    let after = session_files(home.path());
    assert_eq!(after.len(), 2);
    let fork = after
        .iter()
        .find(|path| path.as_path() != files[0].as_path())
        .expect("the fork file");
    let transcript = read_transcript(fork);
    assert_eq!(
        transcript.agent["cwd"],
        project.display().to_string(),
        "the fork adopts the TARGET cwd"
    );
    let texts = transcript.message_texts();
    assert!(texts.contains(&"origin".to_owned()), "{texts:?}");
    assert!(texts.contains(&"continue here".to_owned()), "{texts:?}");
}

/// TS `forkFrom`'s failure contract on the CLI: an empty source file
/// errors with the TS message instead of silently starting fresh, and
/// `--fork` still refuses its conflicting flags.
#[test]
fn print_mode_fork_rejects_empty_sources_and_conflicting_flags() {
    let home = isolated_home();
    // An empty session file, addressed by path (TS forkFrom's empty
    // source error).
    let sessions = home.path().join(".eukhe/sessions");
    std::fs::create_dir_all(&sessions).expect("sessions dir");
    let empty = sessions.join("empty-session.jsonl");
    std::fs::write(&empty, "").expect("empty session");
    let script = serde_json::json!({ "responses": ["never"] });
    let (stdout, stderr, code) = run_in_home(
        home.path(),
        &["--fork", empty.display().to_string().as_str(), "-p", "hi"],
        &script,
    );
    assert_eq!(code, 1);
    assert_eq!(stdout, "");
    assert!(
        stderr.contains("Cannot fork: source session file is empty or invalid:"),
        "stderr: {stderr}"
    );

    // The flag conflicts still refuse (TS validateForkFlags), as a usage
    // error (exit 2).
    let (stdout, stderr, code) = run_in_home(
        home.path(),
        &[
            "--fork",
            "empty-session",
            "--resume",
            "empty-session",
            "-p",
            "hi",
        ],
        &script,
    );
    assert_eq!(code, 2);
    assert_eq!(stdout, "");
    assert!(
        stderr.contains("--fork cannot be combined with --resume"),
        "stderr: {stderr}"
    );
    // No fork file materialized for the refused runs.
    assert!(
        session_files(home.path()).is_empty() || {
            let files = session_files(home.path());
            files.iter().all(|path| *path == empty)
        }
    );
}
