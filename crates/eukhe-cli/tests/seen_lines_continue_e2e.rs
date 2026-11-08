//! The lines the model saw outlive the process (regression: each headless
//! `-p -c` turn starts an empty edit store, so the first edit of every
//! turn was refused as anchoring to lines "never displayed" although the
//! previous turn's edit had shown them). The real binary, an isolated
//! HOME and the scripted faux provider: turn 1 (`-p`) reads and edits a
//! file; turn 2 (`-p -c`) edits lines that edit showed, without a read,
//! and the edit lands. A file changed on disk between the turns is refused
//! as before.

use std::path::Path;

use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

#[path = "support/durable_store.rs"]
mod durable_store;
use durable_store::{read_transcript, session_dirs};

/// Run the binary in `home` on `script`; panics unless it exits 0.
fn run_turn(home: &Path, args: &[&str], script: &Value) {
    let output = eukhe_command()
        .args(args)
        .env("HOME", home)
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        .env("EUKHE_OFFLINE", "1")
        .env_remove("EUKHE_CODING_AGENT_DIR")
        .env_remove("EUKHE_SESSION_DIR")
        .env_remove("EUKHE_CODING_AGENT_SESSION_DIR")
        .env_remove("EUKHE_DAEMON_SOCKET")
        .env_remove("RLM_DEPTH")
        .current_dir(home)
        .output()
        .expect("binary present");
    assert_eq!(
        output.status.code(),
        Some(0),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn call(name: &str, arguments: &Value, id: &str) -> Value {
    json!({
        "content": [{ "type": "toolCall", "name": name, "arguments": arguments, "id": id }],
        "stopReason": "toolUse",
    })
}

/// `(isError, text)` of the session's last tool result.
fn last_tool_result(home: &Path) -> (bool, String) {
    let dirs = session_dirs(&home.join(".eukhe/sessions"));
    assert_eq!(dirs.len(), 1, "one session: {dirs:?}");
    let transcript = read_transcript(&dirs[0]);
    let result = transcript
        .entries
        .iter()
        .filter_map(|entry| entry["model"].as_array())
        .flatten()
        .rfind(|message| message["role"] == "toolResult")
        .expect("a tool result")
        .clone();
    (
        result["isError"] == true,
        result["content"][0]["text"]
            .as_str()
            .unwrap_or_default()
            .to_owned(),
    )
}

/// Turn 1: read `notes.txt` and edit its line 2; returns the home.
fn first_turn() -> tempfile::TempDir {
    let home = tempfile::TempDir::new().unwrap();
    let source = "alpha\nbeta\ngamma\n";
    std::fs::write(home.path().join("notes.txt"), source).unwrap();
    let tag = eukhe_docs::file_hash(source);
    let script = json!({ "responses": [
        call("read", &json!({ "i": "Reading notes", "path": "notes.txt" }), "call-read"),
        call(
            "edit",
            &json!({ "i": "Fixing beta", "input": format!("[notes.txt#{tag}]\nPUT 2.=2:\n+BETA") }),
            "call-edit",
        ),
        "first done",
    ]});
    run_turn(home.path(), &["-p", "fix beta"], &script);
    assert_eq!(
        std::fs::read_to_string(home.path().join("notes.txt")).unwrap(),
        "alpha\nBETA\ngamma\n"
    );
    home
}

/// Turn 2: edit line 3 of the text `text` under its tag, without a read.
fn second_turn(home: &Path, text: &str) {
    let tag = eukhe_docs::file_hash(text);
    let script = json!({ "responses": [
        call(
            "edit",
            &json!({ "i": "Fixing gamma", "input": format!("[notes.txt#{tag}]\nPUT 3.=3:\n+GAMMA") }),
            "call-edit-2",
        ),
        "second done",
    ]});
    run_turn(home, &["-p", "-c", "now gamma"], &script);
}

/// Turn 2 edits a line turn 1's edit showed, under that edit's tag: the
/// edit lands.
#[test]
fn a_continued_turn_edits_the_lines_the_last_turn_showed() {
    let home = first_turn();
    second_turn(home.path(), "alpha\nBETA\ngamma\n");
    let (is_error, text) = last_tool_result(home.path());
    assert_eq!(
        (
            is_error,
            std::fs::read_to_string(home.path().join("notes.txt")).unwrap()
        ),
        (false, "alpha\nBETA\nGAMMA\n".to_owned()),
        "{text}"
    );
}

/// The file changes on disk between the turns: turn 2's edit under the
/// new text's tag is refused as unseen, and the file keeps the change.
#[test]
fn a_continued_turn_cannot_edit_a_file_changed_since() {
    let home = first_turn();
    let changed = "alpha\nchanged elsewhere\ngamma\n";
    std::fs::write(home.path().join("notes.txt"), changed).unwrap();
    second_turn(home.path(), changed);
    let (is_error, text) = last_tool_result(home.path());
    assert_eq!(
        (
            is_error,
            text.contains("never displayed"),
            std::fs::read_to_string(home.path().join("notes.txt")).unwrap()
        ),
        (true, true, changed.to_owned()),
        "{text}"
    );
}
