//! An irreversible network call cut by a crash (spec O4, O13): a `bash`
//! call POSTs to a host, then runs on; the worker is killed (`SIGKILL`)
//! once the host has the request. Nothing tells whether the call finished
//! and a repeat would POST again, so the restart treats it as not run: the
//! host sees one POST, the call's result says it was interrupted, the
//! ledger lists it once under the run in flight with its cause, and the
//! run goes on to its answer with nobody asked.

use std::io::{Read, Write};
use std::net::TcpListener;

use super::*;

/// The prompt tag the script answers with the `bash` call that sends a POST.
pub(crate) const TAG: &str = "[net-post]";

/// The file holding the port of the test's host, beside the release file.
const PORT_FILE: &str = "net-port";

/// The call's script: one POST to the test's host, then a wait the kill
/// cuts.
pub(crate) fn script(release: &Path) -> String {
    let port = std::fs::read_to_string(release.with_file_name(PORT_FILE)).expect("the host port");
    format!(
        "curl -s -X POST --data charge=1 http://127.0.0.1:{}/charge; sleep 600",
        port.trim()
    )
}

/// Accept the host's connections on a thread, answering each `200 OK`,
/// and count them in `posts`.
fn serve(listener: TcpListener, posts: std::sync::Arc<std::sync::atomic::AtomicUsize>) {
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            let mut request = [0_u8; 4096];
            let read = stream.read(&mut request).unwrap_or_default();
            if request[..read].starts_with(b"POST ") {
                posts.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            }
            let _ = stream.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok");
        }
    });
}

#[test]
fn a_post_cut_by_a_crash_is_treated_as_not_run_and_never_sent_again() {
    let world = World::new(128_000, &json!({}));
    let listener = TcpListener::bind("127.0.0.1:0").expect("the host");
    let port = listener.local_addr().expect("the host's port").port();
    std::fs::write(world.dir.path().join(PORT_FILE), port.to_string()).expect("the port file");
    let posts = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    serve(listener, std::sync::Arc::clone(&posts));

    let mut client = world.connect();
    let session_id = world.create(&mut client, 0);
    let worker = worker_pid(&mut client, &session_id);
    let message = prompt("net", &[TAG], 0);
    client.send(&json!({ "type": "prompt", "activeSessionId": session_id, "message": message }));
    let deadline = Instant::now() + WAIT;
    while posts.load(std::sync::atomic::Ordering::SeqCst) == 0 {
        assert!(
            Instant::now() < deadline,
            "the POST never reached the host\n{}",
            world.diagnostics()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    sigkill(worker);
    wait_dead(worker);
    drop(client);

    let mut client = reattach(&world, &session_id);
    wait_idle(&mut client, &session_id);
    // The run went on to its answer: nothing waited on a person.
    assert_transcript(&world, std::slice::from_ref(&message));
    let results: Vec<String> = messages_of(&world.transcript(), "toolResult")
        .iter()
        .map(|(_, result)| texts(result).join("\n"))
        .collect();
    assert!(
        results.len() == 1
            && results[0].contains(
                "Tool bash was interrupted and may have partially run. Check the state it \
                 changes (files, processes, jobs) before you run it again."
            ),
        "the call's one result: {results:?}\n{}",
        world.diagnostics()
    );
    let listed = client.request(
        &json!({ "type": "get_unknown_effects", "activeSessionId": session_id }),
        WAIT,
    );
    assert_eq!(listed["success"], true, "get_unknown_effects: {listed}");
    let effects = listed["data"]["effects"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let noted: Vec<(Value, Value, Value)> = effects
        .iter()
        .map(|effect| {
            (
                effect["id"].clone(),
                effect["cause"].clone(),
                effect["resolution"].clone(),
            )
        })
        .collect();
    assert_eq!(
        (posts.load(std::sync::atomic::Ordering::SeqCst), noted),
        (
            1,
            vec![(json!("tool:call-net"), json!("notRepeatSafe"), Value::Null)]
        ),
        "{listed}"
    );
    assert!(
        effects[0]["settledRun"].is_u64(),
        "the entry names its run: {listed}"
    );
}
