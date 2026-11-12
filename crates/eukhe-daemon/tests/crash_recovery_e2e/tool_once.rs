//! A tool call as an exactly-once effect across `kill -9` (spec O1-O8):
//! the worker dies by `SIGKILL` at each point of a call's lifecycle
//! (`EUKHE_TEST_KILL_AT=<kind>:<point>`: `intended` once its intent is
//! durable, `started` just before it runs (a docs write: once its probe
//! is durable, before the rename), `finished` once its result is). After
//! the restart the change is in the world at most once, and the transcript
//! says done or interrupted as the restart's verdict says:
//!
//! - `write`: the docs `edit` tool appends a line. Cut before its probe,
//!   nothing on record tells: interrupted, the file unchanged. Cut after
//!   its probe and before the rename, the file still holds its old bytes
//!   and its writer is dead: run again, the line appended once. Cut after
//!   its result: done, the line appended once.
//! - `tool`: `bash` appends a line (no probe, never replayed). Cut before
//!   it ran: interrupted, nothing appended. Cut after its result: done, one
//!   line.

use super::*;

/// The prompt tags the script answers: a docs `edit` that appends a line
/// (after a `read` of the file), a `bash` command that appends a line.
pub(crate) const WRITE_TAG: &str = "[docs-append]";
pub(crate) const BASH_TAG: &str = "[bash-append]";

/// The file the docs edit appends to, in the session's cwd, and its text
/// before the edit.
const NOTES: &str = "notes.txt";
const NOTES_TEXT: &str = "one\ntwo\n";

/// The file the bash command appends a line to, once per run.
const APPENDS: &str = "bash-appends";

/// The script's reply to a turn tagged here (`prompt` its name) until its
/// call has a result; `None` then (the shared script answers the turn), and
/// for any other turn.
pub(crate) fn reply(request: &Request, prompt: &str, release: &Path) -> Option<Reply> {
    let answered = |id: &str| request.tool_results.iter().any(|result| result == id);
    let call = format!("call-{prompt}");
    if answered(&call) {
        return None;
    }
    if request.prompt.contains(WRITE_TAG) {
        let read = format!("read-{prompt}");
        if !answered(&read) {
            return Some(Reply::tool_call(read, "read", json!({ "path": NOTES })));
        }
        // After the read: its rows are seen, its tag is the text's.
        let input = format!(
            "[{NOTES}#{}]\nPUT >2:\n+three",
            eukhe_docs::file_hash(NOTES_TEXT)
        );
        return Some(Reply::tool_call(call, "edit", json!({ "input": input })));
    }
    if request.prompt.contains(BASH_TAG) {
        let appends = release.with_file_name(APPENDS);
        let script = format!("echo run >> {}", appends.display());
        return Some(Reply::tool_call(call, "bash", json!({ "script": script })));
    }
    None
}

/// What the transcript says of the call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Said {
    Done,
    Interrupted,
}

/// Prompt one turn tagged `tag` in a world whose worker dies at
/// `kind:point`, wait until it died there, reattach to its replacement and
/// let the turn finish: the turn is answered once and every call has one
/// result. Answers the world and what the transcript says of the turn's
/// call `call-t1` of `tool`.
fn cut_at(kind: &str, point: &str, tag: &str, tool: &str) -> (World, Said) {
    let marks = tempfile::tempdir().expect("marker dir");
    let marker = marks.path().join("killed");
    let world = World::with_env(
        128_000,
        &json!({}),
        &[(
            "EUKHE_TEST_KILL_AT",
            format!("{kind}:{point}@{}", marker.display()),
        )],
    );
    std::fs::write(world.dir.path().join(NOTES), NOTES_TEXT).expect("the notes file");
    let mut client = world.connect();
    let session_id = world.create(&mut client, 0);
    let worker = worker_pid(&mut client, &session_id);
    let message = prompt("t1", &[tag], 0);
    client.send(&json!({ "type": "prompt", "activeSessionId": session_id, "message": message }));
    // The process that reaches the point makes the marker, then dies.
    let deadline = Instant::now() + WAIT;
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "no process reached {kind}:{point}\n{}",
            world.diagnostics()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    wait_dead(worker);
    drop(client);

    let mut client = reattach(&world, &session_id);
    wait_idle(&mut client, &session_id);
    assert_transcript(&world, std::slice::from_ref(&message));
    let results: Vec<String> = messages_of(&world.transcript(), "toolResult")
        .iter()
        .filter(|(_, result)| result["toolCallId"] == "call-t1")
        .map(|(_, result)| texts(result).join("\n"))
        .collect();
    let [result] = results.as_slice() else {
        panic!("one result of the call: {results:?}");
    };
    let interrupted = format!(
        "Tool {tool} was interrupted and may have partially run. Check the state it changes \
         (files, processes, jobs) before you run it again."
    );
    let said = if result.contains(&interrupted) {
        Said::Interrupted
    } else {
        assert!(
            !result.contains("interrupted"),
            "a result that is neither done nor interrupted: {result}"
        );
        Said::Done
    };
    // The ledger lists exactly the call a restart settled interrupted, under
    // its kind (`write:<id>` for a probed write, `tool:<id>` otherwise).
    let listed = client.request(
        &json!({ "type": "get_unknown_effects", "activeSessionId": session_id }),
        WAIT,
    );
    assert_eq!(listed["success"], true, "get_unknown_effects: {listed}");
    let ids: Vec<&str> = listed["data"]["effects"]
        .as_array()
        .map_or_default(|effects| {
            effects
                .iter()
                .filter_map(|effect| effect["id"].as_str())
                .collect()
        });
    let expected = match said {
        Said::Interrupted => vec![format!("{kind}:call-t1")],
        Said::Done => Vec::new(),
    };
    assert_eq!(ids, expected, "the unknown effects: {listed}");
    (world, said)
}

/// `(what the transcript says, the notes file)` after a docs append cut at
/// `point`.
fn docs_append_cut_at(point: &str) -> (Said, String) {
    let (world, said) = cut_at("write", point, WRITE_TAG, "edit");
    let notes = std::fs::read_to_string(world.dir.path().join(NOTES)).expect("the notes file");
    (said, notes)
}

/// `(what the transcript says, the appends file)` after a bash append cut
/// at `point`.
fn bash_append_cut_at(point: &str) -> (Said, Option<String>) {
    let (world, said) = cut_at("tool", point, BASH_TAG, "bash");
    let appends = std::fs::read_to_string(world.dir.path().join(APPENDS)).ok();
    (said, appends)
}

#[test]
fn a_docs_append_cut_before_its_probe_is_interrupted_and_never_applied() {
    assert_eq!(
        docs_append_cut_at("intended"),
        (Said::Interrupted, NOTES_TEXT.to_owned())
    );
}

#[test]
fn a_docs_append_cut_before_its_rename_runs_again_and_lands_once() {
    assert_eq!(
        docs_append_cut_at("started"),
        (Said::Done, "one\ntwo\nthree\n".to_owned())
    );
}

#[test]
fn a_docs_append_cut_after_its_result_is_done_and_lands_once() {
    assert_eq!(
        docs_append_cut_at("finished"),
        (Said::Done, "one\ntwo\nthree\n".to_owned())
    );
}

#[test]
fn a_bash_append_cut_after_its_intent_is_interrupted_and_never_runs() {
    assert_eq!(bash_append_cut_at("intended"), (Said::Interrupted, None));
}

#[test]
fn a_bash_append_cut_before_it_runs_is_interrupted_and_never_runs() {
    assert_eq!(bash_append_cut_at("started"), (Said::Interrupted, None));
}

#[test]
fn a_bash_append_cut_after_its_result_is_done_and_ran_once() {
    assert_eq!(
        bash_append_cut_at("finished"),
        (Said::Done, Some("run\n".to_owned()))
    );
}
