//! MCP catalog e2e: the `/mcp` view's daemon surface serves the RESOLVED
//! service catalog (the discovery rows the interactive view renders), the
//! paste flow installs a token service end-to-end through the real daemon,
//! and the disconnect removes it. The compiled linear/notion built-ins and
//! the user's local source (`<agent-dir>/mcp-services.json`) feed the
//! catalog; a record whose service left every source keeps a pinned row.

// Pedantic-gate dispositions (fleet-uniform ruling; see this lane's PR for
// the full rationale).
// Stack-resident futures by design on the daemon's hot paths; boxing the
// call sites for a lint tick is a perf regression with zero correctness gain.
#![allow(clippy::large_futures)]
// 64-bit-only targets; the narrowing casts sit at OS boundaries
// (pid/fd/time/size) where the values are bounded by the kernel - the
// dead-guard expect()s would add panic paths where silent wrap was
// deliberate.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]
// The fn-length threshold is a style gate, not correctness; the structure
// campaign owns the god-fn splits as a follow-up.
#![allow(clippy::too_many_lines)]
// API-shape opinions, not defects; the surfaces are deliberate.
#![allow(
    clippy::unnecessary_wraps,
    clippy::zero_sized_map_values,
    clippy::struct_excessive_bools,
    clippy::struct_field_names
)]
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

/// The daemon e2e tests each supervise a daemon + a session worker;
/// serializing them keeps the harness out of parallel-spawn resource races.
static DAEMON_E2E: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Spawn the supervisor. A stray ambient package dir never leaks in; the
/// kernel runtime and skills fall back to the source checkout.
fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    let mut command = supervisor_command(socket, agent_dir);
    command.env("EUKHE_CODING_AGENT_DIR", agent_dir);
    command.env_remove("EUKHE_PACKAGE_DIR");
    command.env(
        eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
        "15000",
    );
    Daemon::spawn_listening(&mut command, socket, Duration::from_secs(15))
}

struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> (Self, Value) {
        let stream =
            eukhe_types::platform::transport::connect_std(socket).expect("connect supervisor");
        let write_stream = stream.try_clone().expect("clone socket");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer: write_stream,
        };
        let hello = client.read_line();
        (client, hello)
    }

    fn send(&mut self, value: &Value) {
        let mut line = serde_json::to_string(value).expect("serialize command");
        line.push('\n');
        self.writer.write_all(line.as_bytes()).expect("send");
        self.writer.flush().expect("flush");
    }

    fn send_command(&mut self, id: &str, command: &Value) {
        self.send(&json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        }));
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        let deadline = Instant::now() + Duration::from_mins(2);
        self.reader
            .get_mut()
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("set timeout");
        loop {
            match self.reader.read_line(&mut line) {
                Ok(0) => panic!("supervisor closed the connection"),
                Ok(_) if line.trim().is_empty() => line.clear(),
                Ok(_) => return serde_json::from_str(line.trim()).expect("parse response line"),
                Err(error) => {
                    assert!(
                        Instant::now() < deadline,
                        "timed out waiting for supervisor line: {error}"
                    );
                }
            }
        }
    }

    fn read_response(&mut self, id: &str) -> Value {
        let deadline = Instant::now() + Duration::from_mins(4);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                return line;
            }
        }
    }

    /// Graceful supervisor stop: the supervisor routes `shutdown` to its
    /// resident worker (no orphaned workers race the next daemon in the
    /// suite), then exits. The `Drop` SIGKILL stays as the safety net.
    fn shutdown_daemon(&mut self) {
        self.send_command("shutdown", &json!({ "type": "shutdown" }));
        let _ = self.read_response("shutdown");
    }
}

/// TS parity (byte-exact, the daemon wire renders it on the card): the
/// pinned-definition hint.
const PINNED_FROM_RECORD_HINT: &str =
    "This service's catalog source is unavailable; its connection keeps the pinned definition.";

/// The user's local source: a GitHub entry whose two fields alias one token,
/// and one pasteable service whose endpoint cannot resolve (the reserved
/// `invalid` TLD): the install's verification fails closed with the network
/// category instead of touching any real endpoint.
fn local_services_document() -> Value {
    let github_field = |id: &str| {
        json!({
            "id": id, "label": id, "required": true,
            "kind": "bearer-token", "credentialSet": "github-pat"
        })
    };
    json!({
        "version": 1,
        "entries": [
            {
                "server": "github", "service": "github", "label": "GitHub",
                "url": "https://api.githubcopilot.com/mcp/", "aliases": [],
                "transport": { "type": "http", "url": "https://api.githubcopilot.com/mcp/" },
                "auth": { "strategy": "api_key", "clientRegistration": "unknown" },
                "setup": {
                    "status": "requires-setup",
                    "reason": "paste a GitHub personal access token",
                    "fields": [
                        github_field("GITHUB_PAT_TOKEN"),
                        github_field("GITHUB_PERSONAL_ACCESS_TOKEN")
                    ]
                },
                "verification": { "status": "unverified" },
                "legacyBuiltin": false, "provenance": [{ "source": "user" }]
            },
            {
                "server": "paste-fixture", "service": "paste-fixture",
                "label": "Paste Fixture", "url": "https://paste-fixture.invalid/mcp",
                "aliases": [],
                "transport": { "type": "http", "url": "https://paste-fixture.invalid/mcp" },
                "auth": { "strategy": "api_key", "clientRegistration": "unknown" },
                "setup": {
                    "status": "requires-setup",
                    "reason": "paste a fixture token",
                    "fields": [
                        { "id": "FIXTURE_PAT_TOKEN", "label": "FIXTURE_PAT_TOKEN",
                          "required": true, "kind": "bearer-token",
                          "credentialSet": "fixture-pat" }
                    ]
                },
                "verification": { "status": "unverified" },
                "legacyBuiltin": false, "provenance": [{ "source": "user" }]
            }
        ]
    })
}

/// Write `document` as the user's default local source.
fn write_local_services(agent_dir: &Path, document: &Value) {
    std::fs::write(agent_dir.join("mcp-services.json"), document.to_string())
        .expect("write local source");
}

#[test]
fn catalog_surfaces_and_paste_installs_through_the_daemon() {
    let _serial = DAEMON_E2E.lock().unwrap();
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let sessions_dir = dir.path().join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    write_local_services(&agent_dir, &local_services_document());

    let socket = dir.path().join("mcp.sock");
    let _daemon = spawn_supervisor(&socket, &agent_dir);
    let (mut client, hello) = Client::connect(&socket);
    assert_eq!(hello["type"], "daemon_hello");

    client.send_command(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
            },
        }),
    );
    let created = client.read_response("c1");
    assert_eq!(created["success"], true, "create failed: {created}");
    let session_id = created["data"]["activeSessionId"]
        .as_str()
        .or_else(|| created["data"]["id"].as_str())
        .expect("active session id")
        .to_string();

    // The resolved catalog surfaces: 4 service cards (the two built-ins and
    // the two local entries), the fixture row pasteable.
    client.send_command(
        "m1",
        &json!({ "type": "get_mcp_connections", "activeSessionId": session_id }),
    );
    let roster = client.read_response("m1");
    assert_eq!(
        roster["success"], true,
        "get_mcp_connections failed: {roster}"
    );
    let services = roster["data"]["services"]
        .as_array()
        .unwrap_or_else(|| panic!("services array: {roster}"));
    let mut ids: Vec<&str> = services
        .iter()
        .filter_map(|service| service["serviceId"].as_str())
        .collect();
    ids.sort_unstable();
    assert_eq!(
        ids,
        ["github", "linear", "notion", "paste-fixture"],
        "the resolved catalog surfaces: {services:?}"
    );
    let linear = services
        .iter()
        .find(|service| service["serviceId"] == "linear")
        .expect("linear discovery row");
    assert_eq!(linear["connectionStatus"], "not_connected");
    assert_eq!(
        linear["connectable"], true,
        "the metadata-reviewed OAuth builtin is connectable"
    );
    let paste = services
        .iter()
        .find(|service| service["serviceId"] == "paste-fixture")
        .expect("paste fixture row");
    assert_eq!(paste["connectionStatus"], "setup_required");
    assert_eq!(
        paste["pasteToken"], true,
        "the paste marker drives the paste panel"
    );
    let github = services
        .iter()
        .find(|service| service["serviceId"] == "github")
        .expect("github discovery row");
    assert_eq!(
        github["pasteToken"], true,
        "github is pasteable (alias pair)"
    );

    // The paste flow installs end-to-end: the credential is stored bound to
    // the service endpoint and a record is persisted; verification against
    // the unreachable endpoint fails closed with the network category.
    client.send_command(
        "p1",
        &json!({
            "type": "set_mcp_static_token",
            "activeSessionId": session_id,
            "server": "paste-fixture",
            "token": "fixture-pasted-token",
        }),
    );
    let installed = client.read_response("p1");
    assert_eq!(
        installed["success"], true,
        "set_mcp_static_token failed: {installed}"
    );
    assert_eq!(
        installed["data"]["endpoint"],
        "https://paste-fixture.invalid/mcp"
    );
    assert_eq!(
        installed["data"]["verified"], false,
        "the unreachable endpoint never verifies"
    );
    assert!(
        installed["data"]["error"]
            .as_str()
            .is_some_and(|error| error != "credential-changed"),
        "a fixed network category, not a guard discard: {installed}"
    );
    // The credential: typed, bound to the endpoint (read from the auth file
    // the daemon and the kernel share).
    let auth: Value = serde_json::from_str(
        &std::fs::read_to_string(agent_dir.join("auth.json")).expect("auth.json"),
    )
    .expect("auth json");
    assert_eq!(auth["mcp:paste-fixture"]["type"], "mcp_static_token");
    assert_eq!(auth["mcp:paste-fixture"]["bearer"], "fixture-pasted-token");
    assert_eq!(
        auth["mcp:paste-fixture"]["endpoint"],
        "https://paste-fixture.invalid/mcp"
    );
    // The connection record: the durable endpoint pin.
    let records: Value = serde_json::from_str(
        &std::fs::read_to_string(agent_dir.join("mcp-connections.json"))
            .expect("mcp-connections.json"),
    )
    .expect("records json");
    let record = &records["connections"]["paste-fixture"];
    assert_eq!(record["serviceId"], "paste-fixture");
    assert_eq!(record["endpoint"], "https://paste-fixture.invalid/mcp");

    // The roster reflects the install: the service row now carries the
    // account (pending verification), and the connections roster lists it.
    client.send_command(
        "m2",
        &json!({ "type": "get_mcp_connections", "activeSessionId": session_id }),
    );
    let roster = client.read_response("m2");
    let services = roster["data"]["services"]
        .as_array()
        .unwrap_or_else(|| panic!("services array: {roster}"));
    let paste = services
        .iter()
        .find(|service| service["serviceId"] == "paste-fixture")
        .expect("paste fixture row after install");
    assert_eq!(paste["connectionStatus"], "pending", "pending: {paste}");
    assert_eq!(
        paste["connectionIds"],
        json!(["paste-fixture"]),
        "the account id joins the view"
    );
    let connections = roster["data"]["connections"]
        .as_array()
        .expect("connections");
    assert!(
        connections
            .iter()
            .any(|connection| connection["server"] == "paste-fixture"),
        "the roster lists the installed connection: {connections:?}"
    );

    // The disconnect: the credential and the record leave together.
    client.send_command(
        "r1",
        &json!({
            "type": "remove_mcp_connection",
            "activeSessionId": session_id,
            "server": "paste-fixture",
        }),
    );
    let removed = client.read_response("r1");
    assert_eq!(
        removed["success"], true,
        "remove_mcp_connection failed: {removed}"
    );
    let auth: Value = serde_json::from_str(
        &std::fs::read_to_string(agent_dir.join("auth.json")).expect("auth.json"),
    )
    .expect("auth json");
    assert!(
        auth.get("mcp:paste-fixture").is_none(),
        "the credential is gone: {auth}"
    );
    client.send_command(
        "m3",
        &json!({ "type": "get_mcp_connections", "activeSessionId": session_id }),
    );
    let roster = client.read_response("m3");
    let services = roster["data"]["services"]
        .as_array()
        .unwrap_or_else(|| panic!("services array: {roster}"));
    let paste = services
        .iter()
        .find(|service| service["serviceId"] == "paste-fixture")
        .expect("paste fixture row after removal");
    assert_eq!(
        paste["connectionStatus"], "setup_required",
        "back to discovery: {paste}"
    );
    assert_eq!(
        paste["connectionIds"],
        json!([]),
        "no account after the disconnect"
    );
    client.shutdown_daemon();
}

/// A connection record whose service left every source keeps a pinned row
/// through the real daemon (TS parity): manageable, never one-click
/// connectable, and carrying the byte-exact catalog-source hint.
#[test]
fn pinned_row_shows_the_source_unavailable_hint() {
    let _serial = DAEMON_E2E.lock().unwrap();
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    // A local source that does NOT define the service, plus the durable
    // record the pin is built from.
    write_local_services(
        &agent_dir,
        &json!({
            "version": 1,
            "entries": [{
                "server": "local-only", "service": "local-only", "label": "Local Only",
                "url": "https://local-only.example/mcp", "aliases": [],
                "transport": { "type": "http", "url": "https://local-only.example/mcp" },
                "auth": { "strategy": "oauth", "clientRegistration": "dynamic" },
                "setup": { "status": "ready" },
                "verification": { "status": "unverified" },
                "legacyBuiltin": false, "provenance": [{ "source": "user" }]
            }]
        }),
    );
    let record = json!({
        "version": 1,
        "connections": {
            "vanished-service": {
                "connectionId": "vanished-service",
                "serviceId": "vanished-service",
                "endpoint": "https://vanished.example/mcp",
                "label": "Vanished",
                "status": "pending",
                "createdAt": 1u64,
                "updatedAt": 1u64,
            }
        }
    });
    std::fs::write(agent_dir.join("mcp-connections.json"), record.to_string())
        .expect("write records");

    let socket = dir.path().join("pinned.sock");
    let _daemon = spawn_supervisor(&socket, &agent_dir);
    let (mut client, _hello) = Client::connect(&socket);
    let view = pinned_service_view(&mut client, dir.path(), "pinned");
    client.shutdown_daemon();
    assert_eq!(
        (
            view["connectionStatus"].as_str(),
            view["connectable"].as_bool(),
            view["setupHint"].as_str(),
        ),
        (
            Some("not_connected"),
            Some(false),
            Some(PINNED_FROM_RECORD_HINT)
        ),
        "the pinned card: {view}"
    );
}

/// One pinned card off the daemon's `/mcp` roster: create a session, read
/// the service catalog, find the pinned row.
fn pinned_service_view(client: &mut Client, dir: &std::path::Path, id: &str) -> Value {
    client.send_command(
        &format!("c-{id}"),
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.to_string_lossy(),
                "sessionDir": dir.join("sessions").to_string_lossy(),
            },
        }),
    );
    let created = client.read_response(&format!("c-{id}"));
    assert_eq!(created["success"], true, "create failed: {created}");
    let session_id = created["data"]["activeSessionId"]
        .as_str()
        .or_else(|| created["data"]["id"].as_str())
        .expect("active session id")
        .to_string();
    client.send_command(
        &format!("m-{id}"),
        &json!({ "type": "get_mcp_connections", "activeSessionId": session_id }),
    );
    let roster = client.read_response(&format!("m-{id}"));
    assert_eq!(roster["success"], true, "get_mcp_connections: {roster}");
    roster["data"]["services"]
        .as_array()
        .unwrap_or_else(|| panic!("services array: {roster}"))
        .iter()
        .find(|service| service["serviceId"] == "vanished-service")
        .expect("pinned discovery row")
        .clone()
}
