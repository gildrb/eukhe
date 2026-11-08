//! `rlm.query` end to end: the real binary in print mode, an isolated
//! HOME, the scripted faux provider (`EUKHE_FAUX_SCRIPT`) and a real
//! kernel. A cell asks a sub-model about a context it holds as data and
//! prints only the answer's length: the answer is a Python value, and the
//! transcript grows by the cell's own call and result, nothing else.

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

#[path = "support/durable_store.rs"]
mod durable_store;
use durable_store::{read_transcript, session_dirs, storage_contains};

/// The sub-model's answer: it must never reach the stored session.
const ANSWER: &str = "the context repeats one word";

#[test]
fn a_query_answers_the_cell_without_growing_the_transcript() {
    let home = tempfile::TempDir::new().expect("home");
    let cell = "ctx = 'word ' * 500\nr = await rlm.query('summarize', ctx)\nprint(len(r))";
    let script = serde_json::json!({ "responses": [
        { "content": [{ "type": "toolCall", "name": "ipython", "arguments": { "code": cell } }] },
        ANSWER,
        "done",
    ] });
    let output = eukhe_command()
        .args(["-p", "summarize the context"])
        .env("HOME", home.path())
        .env("EUKHE_FAUX_SCRIPT", script.to_string())
        .env_remove("EUKHE_CODING_AGENT_DIR")
        .env_remove("EUKHE_SESSION_DIR")
        .env_remove("EUKHE_CODING_AGENT_SESSION_DIR")
        .env_remove("RLM_DEPTH")
        .current_dir(home.path())
        .output()
        .expect("binary present");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(0), "stderr: {stderr}");
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "done");

    let storages = session_dirs(&home.path().join(".eukhe/sessions"));
    assert_eq!(storages.len(), 1, "{storages:?}");
    let transcript = read_transcript(&storages[0]);
    let turn: Vec<(&str, String)> = transcript
        .entries
        .iter()
        .filter(|entry| {
            ["pi.user", "pi.assistant", "pi.tool-result"]
                .contains(&entry["kind"].as_str().unwrap_or_default())
        })
        .map(|entry| {
            let text = entry["model"][0]["content"]
                .as_array()
                .and_then(|blocks| blocks.iter().find_map(|block| block["text"].as_str()))
                .or_else(|| entry["model"][0]["content"].as_str())
                .unwrap_or_default()
                .to_owned();
            (entry["kind"].as_str().unwrap_or_default(), text)
        })
        .collect();
    assert_eq!(
        turn,
        vec![
            ("pi.user", "summarize the context".to_owned()),
            ("pi.assistant", String::new()),
            ("pi.tool-result", format!("{}\n", ANSWER.len())),
            ("pi.assistant", "done".to_owned()),
        ]
    );
    assert!(
        !storage_contains(&storages[0], ANSWER),
        "the answer stayed a value: no stored row carries it"
    );
}
