//! A `bash` command running when its worker is killed (SIGKILL) dies with the
//! worker: the supervisor kills the command's process group once it sees
//! the worker exit, and the run that resumes in the replacement reads the
//! call as interrupted, never running it a second time.

use super::*;

/// The prompt tag the script answers with a `bash` call that records its
/// pid and then runs until killed.
pub(crate) const TAG: &str = "[slow-bash]";

/// The call's script: `sh` records its pid, then becomes the `sleep`.
pub(crate) fn script(release: &Path) -> String {
    let pids = release.with_file_name("bash-pids");
    format!("sh -c 'echo $$ >> {}; exec sleep 600'", pids.display())
}

#[test]
fn a_worker_killed_mid_bash_takes_the_command_with_it() {
    let world = World::new(128_000, &json!({}));
    let mut client = world.connect();
    let session_id = world.create(&mut client, 0);
    let worker = worker_pid(&mut client, &session_id);
    let message = prompt("crash", &[TAG], 0);
    client.send(&json!({ "type": "prompt", "activeSessionId": session_id, "message": message }));
    // The file the command appends its pid to, once per run.
    let pids = world.dir.path().join("bash-pids");
    let deadline = Instant::now() + WAIT;
    let command: u32 = loop {
        if let Some(pid) = std::fs::read_to_string(&pids)
            .ok()
            .and_then(|pids| pids.lines().next().and_then(|pid| pid.parse().ok()))
        {
            break pid;
        }
        assert!(Instant::now() < deadline, "the bash command never started");
        std::thread::sleep(Duration::from_millis(20));
    };

    sigkill(worker);
    wait_dead(worker);
    // The command outlives the worker only until the supervisor sees the
    // exit: its group dies before the session relaunches.
    wait_dead(command);
    drop(client);

    let mut client = reattach(&world, &session_id);
    wait_idle(&mut client, &session_id);
    assert_transcript(&world, std::slice::from_ref(&message));
    let runs = std::fs::read_to_string(&pids).expect("the command's pids");
    assert_eq!(runs.lines().count(), 1, "the call ran once: {runs}");
    let results: Vec<String> = messages_of(&world.transcript(), "toolResult")
        .iter()
        .map(|(_, message)| texts(message).join("\n"))
        .collect();
    assert!(
        results.len() == 1
            && results[0].contains(
                "Tool bash was interrupted and may have partially run. Check the state it changes (files, processes, jobs) before you run it again."
            ),
        "the call's one result: {results:?}\n{}",
        world.diagnostics()
    );
}
