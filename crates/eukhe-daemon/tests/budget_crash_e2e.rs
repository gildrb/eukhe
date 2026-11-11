//! A budgeted session's worker killed mid-request (spec/README.md B5, B9),
//! through the real supervisor: the session's model request is in flight
//! (a faux provider that holds it until the test lets go) when its worker
//! is `SIGKILLed`. The supervisor respawns the worker, the session opens
//! again and resumes, and its ledger
//! (`<agent dir>/budgets/<session>.jsonl`) shows the reservation that was
//! in flight charged in full exactly once, no hold left open, the next
//! request reserved and settled normally (no double spend), and an audit
//! that replays exactly.
#![allow(clippy::too_many_lines)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

/// How long the test waits for anything the daemon must do.
const WAIT: Duration = Duration::from_mins(3);

fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    std::fs::create_dir_all(agent_dir).expect("agent dir");
    Daemon::spawn_bound(
        supervisor_command(socket, agent_dir)
            .env_remove("PRIME_API_KEY")
            .env_remove("EUKHE_CODING_AGENT_DIR")
            // A supervisor killed at teardown must not leak its workers.
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "15000",
            ),
        socket,
        Duration::from_secs(10),
    )
}

/// One client connection: a request and its response.
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> Client {
        let stream = UnixStream::connect(socket).expect("connect");
        stream.set_read_timeout(Some(WAIT)).expect("read timeout");
        let writer = stream.try_clone().expect("clone");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
        };
        let hello = client.read_line();
        assert_eq!(hello["type"], "daemon_hello");
        client
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        loop {
            line.clear();
            let read = self.reader.read_line(&mut line).expect("a daemon line");
            assert!(read > 0, "the supervisor closed the connection");
            if !line.trim().is_empty() {
                return serde_json::from_str(line.trim()).expect("parse line");
            }
        }
    }

    /// The response to `command`, sent as `id` (events on the way are
    /// skipped).
    fn request(&mut self, id: &str, command: &Value) -> Value {
        let envelope = json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION },
            "command": command,
        });
        writeln!(self.writer, "{envelope}").expect("write the command");
        loop {
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                return line;
            }
        }
    }
}

/// Every complete record of the one ledger in `dir`, with its owner.
fn ledger(dir: &Path) -> (String, Vec<Value>) {
    let files: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("the budgets dir")
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "jsonl")
        })
        .collect();
    assert_eq!(files.len(), 1, "one account, one ledger: {files:?}");
    let owner = files[0]
        .file_stem()
        .expect("a stem")
        .to_string_lossy()
        .into_owned();
    let text = std::fs::read_to_string(&files[0]).expect("the ledger");
    let complete = &text[..text.rfind('\n').expect("a record")];
    let records = complete
        .lines()
        .map(|line| serde_json::from_str(line).expect("a ledger line"))
        .collect();
    (owner, records)
}

fn amount(value: &Value, dimension: &str) -> u64 {
    value[dimension].as_u64().unwrap_or(0)
}

/// A `--budget-*` like budget: tokens and model requests limited.
const LIMITS: (u64, u64) = (2_000_000, 10);

#[test]
fn a_worker_killed_mid_request_is_charged_its_reservation_once() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let sessions_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    // No session title: its background request would reserve from the
    // budget too.
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({ "titles": { "generate": false } }).to_string(),
    )
    .expect("write settings.json");
    // Every model request connects to the hold socket and stays in flight
    // until the test closes that connection, then answers.
    let hold = dir.path().join("hold.sock");
    let listener = UnixListener::bind(&hold).expect("bind the hold socket");
    let script = dir.path().join("faux.json");
    std::fs::write(
        &script,
        json!({
            "engine": "faux",
            "repeatLastResponse": true,
            "responses": [{ "text": "answered", "holdUntilReleased": hold.to_string_lossy() }],
        })
        .to_string(),
    )
    .expect("write the faux script");

    let socket = dir.path().join("budget-crash.sock");
    let _supervisor = spawn_supervisor(&socket, &agent_dir);
    let mut client = Client::connect(&socket);
    let created = client.request(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": script.to_string_lossy(),
                "name": "budget-crash",
                "budget": { "tokens": LIMITS.0, "requests": LIMITS.1 },
            },
        }),
    );
    assert_eq!(created["success"], true, "create failed: {created}");
    let active = created["data"]["activeSessionId"]
        .as_str()
        .expect("active session id")
        .to_string();

    // The turn's request reserves, then connects: once the hold socket has
    // its connection, the reservation is on disk and the request in flight.
    let (hand_over, connected) = std::sync::mpsc::channel();
    let accept = listener.try_clone().expect("clone the listener");
    std::thread::spawn(move || {
        let (connection, _) = accept.accept().expect("the request connects");
        hand_over
            .send(connection)
            .expect("hand the connection over");
    });
    let prompted = client.request(
        "p1",
        &json!({ "type": "prompt", "activeSessionId": active, "message": "think it over" }),
    );
    assert_eq!(prompted["success"], true, "prompt failed: {prompted}");
    let in_flight = connected.recv_timeout(WAIT).expect("the request in flight");
    let budgets = agent_dir.join("budgets");
    let (owner, before) = ledger(&budgets);
    let crashed = before.last().expect("a record")["state"].clone();
    let holds = crashed["account"]["holds"]
        .as_array()
        .expect("holds")
        .clone();
    assert_eq!(holds.len(), 1, "one request in flight: {crashed:#}");
    let hold_id = holds[0]["id"].as_u64().expect("a hold id");
    let reserved = holds[0]["amount"].clone();
    assert_eq!(
        (
            holds[0]["agent"].as_str(),
            amount(&crashed["account"]["spent"], "tokens")
        ),
        (Some(owner.as_str()), 0),
        "{crashed:#}"
    );

    // Kill the worker with its request in flight.
    let state = client.request(
        "st1",
        &json!({ "type": "get_state", "activeSessionId": active }),
    );
    let worker_pid = state["data"]["workerPid"].as_u64().expect("worker pid");
    let killed = std::process::Command::new("kill")
        .args(["-9", &worker_pid.to_string()])
        .status()
        .expect("kill");
    assert!(killed.success(), "kill -9 {worker_pid}");
    drop(in_flight);
    // Every request of the respawned worker is answered at once.
    std::thread::spawn(move || {
        for connection in listener.incoming() {
            drop(connection);
        }
    });

    // The supervisor respawns the worker and the session resumes; a prompt
    // sent before the respawn is served is answered with a failure, so it
    // is sent again until the new worker serves it.
    let deadline = Instant::now() + WAIT;
    loop {
        let done = client.request(
            "rp",
            &json!({
                "type": "prompt_and_wait",
                "activeSessionId": active,
                "message": "are you back",
            }),
        );
        if done["success"] == true {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "the session never came back: {done}"
        );
        std::thread::sleep(Duration::from_millis(500));
    }
    let idle = client.request(
        "w1",
        &json!({ "type": "wait_for_idle", "activeSessionId": active }),
    );
    assert_eq!(idle["success"], true, "never went idle: {idle}");
    let audit = client.request(
        "a1",
        &json!({ "type": "audit_budget", "activeSessionId": active }),
    );

    let (after_owner, records) = ledger(&budgets);
    assert_eq!(after_owner, owner, "the same account");
    let kind = |record: &Value| record["op"]["kind"].as_str().unwrap_or_default().to_owned();
    // The hold that was in flight: never settled; charged by the one
    // recovery that found it open, at what it held.
    let settled_in_flight = records
        .iter()
        .filter(|record| kind(record) == "settle" && record["op"]["id"] == hold_id)
        .count();
    let charges_in_flight = |pair: &[Value]| {
        kind(&pair[1]) == "recover"
            && pair[0]["state"]["account"]["holds"]
                .as_array()
                .is_some_and(|holds| holds.iter().any(|hold| hold["id"] == hold_id))
    };
    let charging: Vec<(Value, Value)> = records
        .windows(2)
        .filter(|pair| charges_in_flight(pair))
        .map(|pair| {
            (
                pair[0]["state"]["account"]["spent"].clone(),
                pair[1]["state"]["account"]["spent"].clone(),
            )
        })
        .collect();
    let recovered_at = records
        .windows(2)
        .position(charges_in_flight)
        .expect("a recovery of the in-flight hold")
        + 1;
    // After the recovery: every reservation granted with a new id, and
    // settled once each.
    let after = &records[recovered_at + 1..];
    let granted: Vec<u64> = after
        .iter()
        .filter(|record| kind(record) == "reserve" && record["outcome"]["kind"] == "granted")
        .map(|record| record["op"]["id"].as_u64().expect("an id"))
        .collect();
    let settles: Vec<(u64, Value)> = after
        .iter()
        .filter(|record| kind(record) == "settle")
        .map(|record| {
            (
                record["op"]["id"].as_u64().expect("an id"),
                record["op"]["actual"].clone(),
            )
        })
        .collect();
    let settled_ids: Vec<u64> = settles.iter().map(|(id, _)| *id).collect();
    let resumed_tokens: u64 = settles
        .iter()
        .map(|(_, actual)| amount(actual, "tokens"))
        .sum();
    let last = &records.last().expect("a record")["state"]["account"];

    assert_eq!(settled_in_flight, 0, "the in-flight hold was settled");
    assert_eq!(
        charging,
        vec![(
            json!({ "costMicros": 0, "tokens": 0, "timeMs": 0, "toolCalls": 0, "requests": 0 }),
            json!({
                "costMicros": 0,
                "tokens": amount(&reserved, "tokens"),
                "timeMs": 0,
                "toolCalls": 0,
                "requests": amount(&reserved, "requests"),
            }),
        )],
        "the in-flight reservation is charged in full exactly once"
    );
    assert!(
        !granted.is_empty() && granted.iter().all(|id| *id > hold_id),
        "the resumed turn reserved again with new ids: {granted:?}"
    );
    assert_eq!(settled_ids, granted, "each new reservation settled once");
    assert_eq!(
        (
            last["holds"].clone(),
            amount(&last["spent"], "tokens"),
            amount(&last["spent"], "requests"),
        ),
        (
            json!([]),
            amount(&reserved, "tokens") + resumed_tokens,
            amount(&reserved, "requests") + granted.len() as u64,
        ),
        "no hold open, and no double spend"
    );
    let spent = last["spent"].clone();
    assert_eq!(
        (audit["success"].clone(), audit["data"].clone()),
        (
            json!(true),
            json!({
                "audit": {
                    "records": records.len(),
                    "settled": spent,
                    "spent": spent,
                    "exact": true,
                    "firstMismatch": null,
                },
            }),
        ),
        "the ledger replays exactly"
    );
}
