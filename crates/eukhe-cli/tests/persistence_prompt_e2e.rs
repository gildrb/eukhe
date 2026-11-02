//! The persistence rules reach the model: the real binary in print mode, an
//! isolated HOME, and the scripted faux provider (`EUKHE_FAUX_SCRIPT`),
//! whose `systemPrompt` entry answers with the request's system prompt. The
//! `<critical>` block closes every section of the prompt the model sees (the
//! tool list of `codemode` included); only the environment follows it in a
//! project without instructions files. No line orders the model to end its
//! turn while its work still runs — the drill's premature stops ("I'll
//! commit once it passes", then an idle agent).

#[path = "support/eukhe.rs"]
mod eukhe;
use eukhe::eukhe_command;

/// Lines the prompt used to carry that tell the model to end its turn while
/// a job, command, or run is still going.
const STOP_ORDERS: &[&str] = &[
    "otherwise they end the turn",
    "await commands before ending the turn",
    "before ending a turn while work is still running",
];

#[test]
fn the_prompt_the_model_sees_closes_with_the_persistence_rules() {
    let home = tempfile::TempDir::new().expect("home");
    let script = serde_json::json!({ "responses": [{ "systemPrompt": true }] });
    let output = eukhe_command()
        .args(["-p", "run the build and tell me when it is done"])
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
    let prompt = String::from_utf8_lossy(&output.stdout);
    let prompt = prompt.trim_end();

    let critical = eukhe_core::prompts::closing_block(None).expect("the layered prompt closes");
    let at = prompt
        .find(critical)
        .expect("the prompt holds the critical block");
    let after = &prompt[at + critical.len()..];
    assert!(
        after.contains("Working directory:") && !after.contains("\n\n#") && !after.contains('<'),
        "only the environment follows the critical block:\n{after}"
    );
    assert!(
        prompt
            .find("<codemode>")
            .is_none_or(|codemode| codemode < at),
        "the critical block does not follow the codemode section"
    );
    for order in STOP_ORDERS {
        assert!(!prompt.contains(order), "the prompt still says {order:?}");
    }
}
