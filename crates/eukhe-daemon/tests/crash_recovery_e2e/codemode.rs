//! A `codemode` script survives a worker kill between its nested calls.
//!
//! The model calls `codemode` with [`SCRIPT`]: an `ipython` cell that
//! appends a line to the `marker` file (replay-unsafe: it must never run
//! again), then a `read` of the `held.fifo` named pipe (replay-safe), then
//! a `read` of a plain file. The pipe holds the second call in flight until
//! the test writes it, so the worker dies with the first call finished and
//! the second running. The replacement worker replays the script from its
//! journal: the cell's journaled result, the read run again.

use std::fs::File;
use std::io::Write as _;
use std::sync::mpsc::{self, Receiver};

use super::*;

/// The prompt tag the mock answers with a `codemode` call of [`SCRIPT`].
pub const TAG: &str = "[codemode]";

/// The script. Every path is relative to the session's cwd, so the script
/// is the same text in every world and its result can be compared across
/// worlds.
pub const SCRIPT: &str = r#"const marked = await tools.ipython({ code: "with open('marker', 'a') as f:\n    f.write('run\\n')\nprint('marked')" });
const held = await tools.read({ path: "held.fifo" });
const plain = await tools.read({ path: "plain.txt" });
return { marked, held, plain };"#;

/// What the test writes into the pipe once the read may finish.
const HELD_CONTENT: &str = "held line one\nheld line two\n";
const PLAIN_CONTENT: &str = "plain line\n";

/// A world with the script's files in its cwd.
fn codemode_world() -> World {
    let world = World::new(128_000, &json!({}));
    let fifo = fifo_path(&world);
    let status = Command::new("mkfifo")
        .arg(&fifo)
        .status()
        .expect("run mkfifo");
    assert!(status.success(), "mkfifo {}", fifo.display());
    std::fs::write(world.dir.path().join("plain.txt"), PLAIN_CONTENT).expect("plain.txt");
    world
}

fn fifo_path(world: &World) -> PathBuf {
    world.dir.path().join("held.fifo")
}

fn marker_path(world: &World) -> PathBuf {
    world.dir.path().join("marker")
}

/// Open the pipe for writing on a thread. The open returns once a reader
/// has the pipe open, so the received writer means a `read` is in flight.
fn writer_once_read(world: &World) -> Receiver<File> {
    let fifo = fifo_path(world);
    let (sender, receiver) = mpsc::channel();
    std::thread::spawn(move || {
        let writer = std::fs::OpenOptions::new()
            .write(true)
            .open(&fifo)
            .expect("open the pipe for writing");
        // The test may have failed and gone; nothing to hand over then.
        let _ = sender.send(writer);
    });
    receiver
}

fn received(world: &World, receiver: &Receiver<File>, what: &str) -> File {
    receiver
        .recv_timeout(WAIT)
        .unwrap_or_else(|_| panic!("{what} never opened the pipe\n{}", world.diagnostics()))
}

/// Let the in-flight read finish: write the content, then close every
/// writer so the reader sees the end of the pipe.
fn release(mut writer: File, others: Vec<File>) {
    writer
        .write_all(HELD_CONTENT.as_bytes())
        .expect("write the pipe");
    drop(writer);
    drop(others);
}

/// Wait until `pid` is reaped: only then has its last thread exited and
/// closed its files.
fn wait_reaped(world: &World, pid: u32) {
    let deadline = Instant::now() + WAIT;
    while Path::new(&format!("/proc/{pid}")).exists() {
        assert!(
            Instant::now() < deadline,
            "worker {pid} was never reaped\n{}",
            world.diagnostics()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// The text of the `codemode` call's one result in the world's transcript,
/// its wall-time line masked (the clock is no part of the script's
/// result), and whether it is an error.
fn codemode_result(world: &World) -> (String, bool) {
    let transcript = world.transcript();
    let results: Vec<Value> = messages_of(&transcript, "toolResult")
        .into_iter()
        .map(|(_, message)| message)
        .filter(|message| message["toolName"] == "codemode")
        .collect();
    assert_eq!(results.len(), 1, "one codemode result: {results:#?}");
    let text = texts(&results[0])
        .join("\n")
        .lines()
        .map(|line| {
            if line.starts_with("Wall time ") {
                "Wall time <t> seconds"
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    (text, results[0]["isError"] == true)
}

/// The pre-crash turn and the codemode turn's prompt.
fn prompts() -> (String, String) {
    (prompt("t1", &[], 0), prompt("crash", &[TAG], 0))
}

/// The same script in a fresh session that nothing interrupts.
fn reference() -> String {
    let world = codemode_world();
    let mut client = world.connect();
    let session_id = world.create(&mut client, 0);
    let (first, crash) = prompts();
    run_turn(&mut client, &session_id, &first);
    let reader = writer_once_read(&world);
    let id = client.send(
        &json!({ "type": "prompt_and_wait", "activeSessionId": session_id, "message": crash }),
    );
    release(received(&world, &reader, "the reference read"), Vec::new());
    let done = client.response(&id, WAIT);
    assert_eq!(done["success"], true, "reference turn: {done}");
    assert_transcript(&world, &[first, crash]);
    let (text, is_error) = codemode_result(&world);
    assert!(!is_error, "the reference script failed: {text}");
    assert_eq!(
        std::fs::read_to_string(marker_path(&world)).expect("marker"),
        "run\n"
    );
    text
}

#[test]
fn worker_killed_between_codemode_nested_calls() {
    let expected = reference();

    let world = codemode_world();
    let mut client = world.connect();
    let session_id = world.create(&mut client, 0);
    let (first, crash) = prompts();
    run_turn(&mut client, &session_id, &first);

    // Drive the script to its second nested call: the `read` holds the
    // pipe open, so the cell before it finished.
    let pid = worker_pid(&mut client, &session_id);
    let reader = writer_once_read(&world);
    client.send(&json!({ "type": "prompt", "activeSessionId": session_id, "message": crash }));
    let crashed_writer = received(&world, &reader, "the first read");
    assert_eq!(
        std::fs::read_to_string(marker_path(&world)).expect("the cell ran"),
        "run\n"
    );
    let log_before = world.mock.log().len();

    // The crash. The first writer stays open, so the replay's reader is
    // the only one a new writer's open waits for: the killed reader is
    // gone once the supervisor reaped the worker (a zombie leader can
    // outlive the thread that still holds the pipe).
    sigkill(pid);
    wait_dead(pid);
    wait_reaped(&world, pid);
    drop(client);
    let replayed = writer_once_read(&world);
    let mut client = reattach(&world, &session_id);
    release(
        received(&world, &replayed, "the replayed read"),
        vec![crashed_writer],
    );
    wait_idle(&mut client, &session_id);

    // The session keeps working after the recovery.
    let next = prompt("next", &[], 0);
    run_turn(&mut client, &session_id, &next);
    wait_idle(&mut client, &session_id);

    let log = world.mock.log();
    let context = format!(
        "provider log: {:#?}\n{}",
        mock_llm::summary(&log),
        world.diagnostics()
    );
    // The turn finished exactly once; nothing duplicated.
    assert_transcript(&world, &[first, crash, next]);
    // The script replayed to the uninterrupted result.
    let (text, is_error) = codemode_result(&world);
    assert!(!is_error, "the replayed script failed: {text}; {context}");
    assert_eq!(text, expected, "{context}");
    // The finished cell was not run again.
    assert_eq!(
        std::fs::read_to_string(marker_path(&world)).expect("marker"),
        "run\n",
        "{context}"
    );
    // The model was asked after the tool exactly once, after the crash.
    let after_tool: Vec<Served> = log
        .iter()
        .filter(|entry| entry.request.after_tool)
        .map(|entry| entry.served)
        .collect();
    assert_eq!(after_tool, vec![Served::Complete], "{context}");
    assert!(
        !log[..log_before]
            .iter()
            .any(|entry| entry.request.after_tool),
        "{context}"
    );
}
