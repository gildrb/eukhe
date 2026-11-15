// Harness fns are linear scripts.
#![allow(clippy::too_many_lines)]

//! Real-terminal e2e for `/restart` across two builds: what happens to the
//! daemon a client is attached to when the install moves to another
//! version.
//!
//! Two `eukhe` builds of this source, versions `<series>.1` (old) and
//! `<series>.2` (new), built as the release workflow builds a release:
//! `EUKHE_RELEASE_VERSION` set, `cargo build -p eukhe-cli --bin eukhe`.
//! The test builds them itself (debug profile) into
//! `<target>/restart-e2e/<version>`, one target dir per version so a rerun
//! rebuilds only what changed; the first run compiles the workspace twice.
//! Each runs from an install laid out as install.sh lays it out
//! (`root/eukhe-<v>/`, `bin/eukhe` the launcher); the test moves the
//! launcher to a payload the way an update leaves it, and `/restart` reads
//! the target from the launcher. Readiness is the pty stream, the daemon's
//! hello and `wait_for_idle`; a turn is held at the faux provider's
//! `holdUntilReleased` gate (the request connected to a socket the test
//! owns) until the test closes it. A session reopened on a new daemon is
//! woken there by the supervisor, which hands it `EUKHE_FAUX_SCRIPT` (the
//! daemon's verification seam in its wake create), read when the worker
//! starts: the test rewrites the script before such a start.
//!
//! - Idle daemon: `/restart` onto the new version stops the old daemon,
//!   the new version serves the socket, and the session reopens from
//!   storage and answers.
//! - Busy daemon: `/restart` keeps the daemon running its turn, the client
//!   restarts onto the new version (same protocol and schema) and shows
//!   the held answer; a later interactive start on the idle daemon moves
//!   it to the new version.
//! - Incompatible target: the client stays (the plan's stay message) and
//!   keeps working on the old daemon, busy (`WaitForIdle`) and idle with
//!   an older target (`Blocked`). The incompatible build is the new build
//!   behind a launcher payload whose `--build-identity` answer carries
//!   another `schemaId`: the plan reads a target only through that answer
//!   and the daemon's hello, so this is what a build of another schema
//!   presents, without compiling a third build of a changed wire.

use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::Duration;

use eukhe_client::restart::{Identity, Plan, Target};
use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;

#[path = "support/ctty.rs"]
mod ctty;

#[path = "support/install_pty.rs"]
mod install_pty;

use install_pty::{
    daemon_request, exits_within, graceful_shutdown, hello, launched_payload, launcher_script,
    supervisor_pid, Client,
};

/// The child test the terminal client runs as.
const CHILD_TEST: &str = "restart_daemon_child_mode";

/// Wide enough that the stay messages render on one row.
const COLS: u16 = 250;

/// How long a stopped supervisor may take to exit.
const EXIT_WAIT: Duration = Duration::from_secs(30);

/// The terminal half ([`install_pty::run_child`]).
#[test]
fn restart_daemon_child_mode() {
    install_pty::run_child();
}

/// One release build of this source.
struct Build {
    version: String,
    exe: PathBuf,
    identity: Identity,
}

/// What `eukhe --build-identity` prints.
#[derive(serde::Deserialize)]
struct Printed {
    version: String,
    identity: Identity,
}

/// The release versions of the workspace's series `X.Y.Z`: `X.Y.(Z+n)`.
fn release_version(n: u64) -> String {
    let workspace = env!("CARGO_PKG_VERSION");
    let (series, patch) = workspace.rsplit_once('.').expect("an X.Y.Z version");
    let patch: u64 = patch.parse().expect("a numeric patch");
    format!("{series}.{}", patch + n)
}

/// The old and the new build, compiled at once.
fn builds() -> (Build, Build) {
    let old = release_version(1);
    let new = release_version(2);
    let compiling = [spawn_build(&old), spawn_build(&new)];
    let [old, new] = compiling.map(|(version, child, log)| finish_build(version, child, &log));
    (old, new)
}

/// The build dir of `version`: `<target>/restart-e2e/<version>`.
fn build_dir(version: &str) -> PathBuf {
    Path::new(env!("CARGO_BIN_EXE_eukhe"))
        .parent()
        .and_then(Path::parent)
        .expect("the target dir")
        .join("restart-e2e")
        .join(version)
}

/// Start `cargo build` of `version` as the release workflow runs it.
fn spawn_build(version: &str) -> (String, std::process::Child, PathBuf) {
    let dir = build_dir(version);
    std::fs::create_dir_all(&dir).expect("build dir");
    let log = dir.join("build.log");
    let output = std::fs::File::create(&log).expect("build log");
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let child = Command::new(cargo)
        .args(["build", "--locked", "-p", "eukhe-cli", "--bin", "eukhe"])
        .arg("--manifest-path")
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../Cargo.toml"))
        .arg("--target-dir")
        .arg(&dir)
        .env("EUKHE_RELEASE_VERSION", version)
        .env_remove("EUKHE_BUILD_COMMIT")
        .stdin(Stdio::null())
        .stdout(output.try_clone().expect("build log"))
        .stderr(output)
        .spawn()
        .expect("start cargo build");
    (version.to_string(), child, log)
}

fn finish_build(version: String, mut child: std::process::Child, log: &Path) -> Build {
    let status = child.wait().expect("cargo build");
    assert!(
        status.success(),
        "cargo build of {version} failed ({status}):\n{}",
        std::fs::read_to_string(log).unwrap_or_default()
    );
    let exe = build_dir(&version).join("debug/eukhe");
    let printed = printed_identity(&exe);
    assert_eq!(printed.version, version, "the build reports its release");
    Build {
        version,
        exe,
        identity: printed.identity,
    }
}

fn printed_identity(exe: &Path) -> Printed {
    let output = Command::new(exe)
        .arg("--build-identity")
        .output()
        .expect("run --build-identity");
    assert!(output.status.success(), "--build-identity: {output:?}");
    serde_json::from_slice(&output.stdout).expect("the build identity JSON")
}

/// The daemon serving a socket, as its hello reports it.
#[derive(Debug, PartialEq, Eq)]
struct Daemon {
    pid: u32,
    identity: Identity,
}

/// The identity a daemon's hello reports.
fn hello_identity(hello: &Value) -> Identity {
    let text = |value: &Value| {
        value
            .as_str()
            .unwrap_or_else(|| panic!("hello field: {hello}"))
            .to_string()
    };
    Identity {
        build_version: text(&hello["appVersion"]),
        build_id: text(&hello["runtime"]["buildId"]),
        protocol_version: hello["protocol"]["version"]
            .as_u64()
            .unwrap_or_else(|| panic!("hello protocol: {hello}")),
        schema_id: text(&hello["schemaId"]),
    }
}

/// The test's world: an install of the old build, its agent dir and
/// daemon socket.
struct World {
    dir: tempfile::TempDir,
}

impl World {
    fn new(builds: &(Build, Build)) -> World {
        let world = World {
            dir: tempfile::tempdir().expect("temp dir"),
        };
        for sub in ["agent/sessions", "project", "tmp", "bin", "mise", "root"] {
            std::fs::create_dir_all(world.base().join(sub)).expect("world dir");
        }
        for build in [&builds.0, &builds.1] {
            let payload = world.payload(&build.version);
            std::fs::create_dir_all(&payload).expect("payload dir");
            // A hard link where the build sits on the same filesystem, a
            // copy where it does not.
            if std::fs::hard_link(&build.exe, payload.join("eukhe")).is_err() {
                std::fs::copy(&build.exe, payload.join("eukhe")).expect("copy eukhe");
            }
            std::fs::write(
                payload.join("package.json"),
                format!("{{\"version\": \"{}\"}}\n", build.version),
            )
            .expect("manifest");
        }
        world.point_launcher(&world.payload(&builds.0.version));
        std::fs::write(
            world.base().join("agent/settings.json"),
            json!({"terminal": {"fullscreen": false}, "update": {"autoDownload": false}})
                .to_string(),
        )
        .expect("settings");
        world
    }

    fn base(&self) -> PathBuf {
        self.dir.path().canonicalize().expect("temp dir path")
    }

    fn payload(&self, version: &str) -> PathBuf {
        self.base().join(format!("root/eukhe-{version}"))
    }

    fn launcher(&self) -> PathBuf {
        self.base().join("bin/eukhe")
    }

    fn socket(&self) -> PathBuf {
        self.base().join("daemon.sock")
    }

    fn gate(&self) -> PathBuf {
        self.base().join("hold.sock")
    }

    /// The install's launcher now runs `payload`, as an update leaves it.
    fn point_launcher(&self, payload: &Path) {
        std::fs::write(self.launcher(), launcher_script(payload)).expect("launcher");
        std::fs::set_permissions(self.launcher(), std::fs::Permissions::from_mode(0o755))
            .expect("launcher mode");
    }

    /// The faux script the next client start hands its sessions.
    fn script(&self, script: &Value) {
        std::fs::write(self.base().join("script.json"), script.to_string()).expect("faux script");
    }

    /// The install's launcher, run by a shell on a fresh pty.
    fn client(&self) -> Client {
        let base = self.base();
        let path = format!(
            "{}:{}",
            base.join("bin").display(),
            std::env::var("PATH").unwrap_or_default()
        );
        let mut command = install_pty::child_command(CHILD_TEST, &self.launcher());
        command
            .current_dir(base.join("project"))
            .env("PATH", path)
            .env("HOME", &base)
            .env("TMPDIR", base.join("tmp"))
            .env("TERM", "xterm-256color")
            .env("EUKHE_CODING_AGENT_DIR", base.join("agent"))
            .env("EUKHE_SESSION_DIR", base.join("agent/sessions"))
            .env("EUKHE_DAEMON_SOCKET", self.socket())
            .env("EUKHE_FAUX_SCRIPT", base.join("script.json"))
            .env("EUKHE_INSTALL_BIN_DIR", base.join("bin"))
            .env("MISE_DATA_DIR", base.join("mise"))
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "15000",
            );
        eukhe::eukhe_env(&mut command);
        Client::spawn(command, COLS)
    }

    /// The daemon serving the socket.
    fn daemon(&self) -> Daemon {
        let hello = hello(&self.socket());
        Daemon {
            pid: supervisor_pid(&hello),
            identity: hello_identity(&hello),
        }
    }

    /// Returns once the one live session holds no work.
    fn wait_for_idle(&self) {
        let list = daemon_request(
            &self.socket(),
            "list",
            &json!({"type": "list", "includeClientOwned": true}),
        );
        let sessions = list["data"]["sessions"]
            .as_array()
            .unwrap_or_else(|| panic!("a session list: {list}"));
        assert_eq!(sessions.len(), 1, "one live session: {list}");
        let idle = daemon_request(
            &self.socket(),
            "idle",
            &json!({"type": "wait_for_idle", "activeSessionId": sessions[0]["activeSessionId"]}),
        );
        assert_eq!(idle["success"], json!(true), "{idle}");
    }

    /// The session storages (`<sessions>/<id>/`).
    fn sessions(&self) -> Vec<PathBuf> {
        std::fs::read_dir(self.base().join("agent/sessions"))
            .expect("sessions dir")
            .map(|entry| entry.expect("session entry").path())
            .filter(|path| path.is_dir())
            .collect()
    }

    /// A payload whose `eukhe` answers `--build-identity` with `printed`
    /// and runs the new build otherwise.
    fn install_reporting(&self, name: &str, printed: &Value, new: &Build) -> PathBuf {
        let payload = self.base().join("root").join(name);
        std::fs::create_dir_all(&payload).expect("payload dir");
        let exe = payload.join("eukhe");
        std::fs::write(
            &exe,
            format!(
                "#!/bin/sh\nif [ \"$1\" = --build-identity ]; then\n  printf '%s\\n' '{printed}'\n  exit 0\nfi\nexec \"{}\" \"$@\"\n",
                new.exe.display()
            ),
        )
        .expect("payload exe");
        std::fs::set_permissions(&exe, std::fs::Permissions::from_mode(0o755)).expect("exe mode");
        payload
    }
}

impl Drop for World {
    fn drop(&mut self) {
        graceful_shutdown(&self.socket());
    }
}

/// The provider gate of `holdUntilReleased`: bound before the client
/// starts; [`Gate::held`] returns the request's connection once a turn
/// reached the provider, and dropping it releases the turn.
struct Gate {
    accepted: mpsc::Receiver<UnixStream>,
}

impl Gate {
    fn bind(path: &Path) -> Gate {
        let listener = UnixListener::bind(path).expect("bind the hold gate");
        let (sender, accepted) = mpsc::channel();
        std::thread::spawn(move || {
            for stream in listener.incoming().flatten() {
                if sender.send(stream).is_err() {
                    return;
                }
            }
        });
        Gate { accepted }
    }

    fn held(&self) -> UnixStream {
        self.accepted
            .recv_timeout(Duration::from_secs(60))
            .expect("a turn held at the provider gate")
    }
}

/// The session reopened by the restarted client answers on the same
/// storage, and its file holds every prompt.
fn assert_one_session_holding(world: &World, prompts: &[&str]) {
    let sessions = world.sessions();
    assert_eq!(sessions.len(), 1, "one session: {sessions:?}");
    let log = std::fs::read_to_string(sessions[0].join("main.jsonl")).expect("session log");
    let missing: Vec<&str> = prompts
        .iter()
        .copied()
        .filter(|prompt| !log.contains(prompt))
        .collect();
    assert_eq!(missing, Vec::<&str>::new(), "prompts the session lacks");
}

#[test]
fn restart_on_an_idle_daemon_moves_it_to_the_new_version_with_the_session() {
    let builds = builds();
    let (old, new) = &builds;
    let world = World::new(&builds);
    world.script(&json!({"responses": ["firstanswer42"]}));
    let mut client = world.client();
    client.submit("remember alpha42");
    client.pty.wait_for("firstanswer42", "the first answer");
    world.wait_for_idle();
    let before = world.daemon();
    assert_eq!(before.identity, old.identity, "the old build serves");

    // The install moves to the new build; the session, reopened on the
    // new daemon, answers from the new script.
    world.point_launcher(&world.payload(&new.version));
    world.script(&json!({"responses": ["afterrestart42"]}));
    let mark = client.pty.mark();
    client.submit("/restart");
    client.pty.wait_for_after(
        mark,
        &format!("Restarting on eukhe {}", new.version),
        "the restart note",
    );
    let restarted = client.pty.mark();
    client.pty.wait_for_after(
        restarted,
        "firstanswer42",
        "the session's transcript, reopened",
    );
    assert!(
        exits_within(before.pid, EXIT_WAIT),
        "the old supervisor {} exits",
        before.pid
    );
    assert_eq!(
        world.daemon().identity,
        new.identity,
        "the new build serves the socket"
    );

    client.submit("and now?");
    client
        .pty
        .wait_for_after(restarted, "afterrestart42", "an answer after the restart");
    assert_one_session_holding(&world, &["remember alpha42", "and now?"]);
}

#[test]
fn restart_beside_a_busy_daemon_keeps_its_turn_and_a_later_start_moves_it() {
    let builds = builds();
    let (old, new) = &builds;
    let world = World::new(&builds);
    let gate = Gate::bind(&world.gate());
    world.script(&json!({"responses": [
        "firstanswer42",
        {"text": "heldanswer42", "holdUntilReleased": world.gate()},
    ]}));
    let mut client = world.client();
    client.submit("remember alpha42");
    client.pty.wait_for("firstanswer42", "the first answer");
    client.submit("hold this");
    let held = gate.held();
    let before = world.daemon();
    assert_eq!(before.identity, old.identity, "the old build serves");

    // `/restart` onto the new build, which speaks the old daemon's wire:
    // the client restarts, the daemon keeps its turn.
    world.point_launcher(&world.payload(&new.version));
    let mark = client.pty.mark();
    client.submit("/restart");
    client.pty.wait_for_after(
        mark,
        &format!("Restarting on eukhe {}", new.version),
        "the restart note",
    );
    let restarted = client.pty.mark();
    client.pty.wait_for_after(
        restarted,
        "firstanswer42",
        "the session's transcript, reopened",
    );
    assert_eq!(world.daemon(), before, "the busy daemon keeps running");

    // The held turn finishes on the old daemon and shows in the new
    // client.
    drop(held);
    client
        .pty
        .wait_for_after(restarted, "heldanswer42", "the held turn's answer");
    world.wait_for_idle();
    assert_eq!(world.daemon(), before, "a restart never moves the daemon");
    assert_one_session_holding(&world, &["remember alpha42", "hold this"]);
    drop(client);

    // A later interactive start finds the daemon idle and moves it.
    world.script(&json!({"responses": ["laterstart42"]}));
    let mut later = world.client();
    later.submit("a later start");
    later
        .pty
        .wait_for("laterstart42", "the later start's answer");
    assert!(
        exits_within(before.pid, EXIT_WAIT),
        "the old supervisor {} exits",
        before.pid
    );
    assert_eq!(
        world.daemon().identity,
        new.identity,
        "the new build serves the socket"
    );
}

#[test]
fn a_target_that_cannot_attach_leaves_the_client_on_the_old_daemon() {
    let builds = builds();
    let (old, new) = &builds;
    let world = World::new(&builds);
    let gate = Gate::bind(&world.gate());
    world.script(&json!({"responses": [
        "firstanswer42",
        {"text": "heldanswer42", "holdUntilReleased": world.gate()},
        "thirdanswer42",
    ]}));
    let mut client = world.client();
    client.submit("remember alpha42");
    client.pty.wait_for("firstanswer42", "the first answer");
    client.submit("hold this");
    let held = gate.held();
    let before = world.daemon();
    assert_eq!(before.identity, old.identity, "the old build serves");

    // A newer target of another schema, the daemon busy: the client stays.
    let other_wire = other_wire_of(new);
    let newer = world.install_reporting(
        "eukhe-newer-other-wire",
        &json!({"version": new.version, "identity": other_wire}),
        new,
    );
    world.point_launcher(&newer);
    let waits = Plan::WaitForIdle {
        daemon_version: old.version.clone(),
    }
    .stay_message(&Target {
        exe: world.launcher(),
        version: new.version.clone(),
        identity: Some(other_wire),
    })
    .expect("a stay message");
    let mark = client.pty.mark();
    client.submit("/restart");
    client
        .pty
        .wait_for_after(mark, &waits, "the wait-for-idle stay message");
    assert_eq!(world.daemon(), before, "the busy daemon keeps running");

    // The old client still works: the held turn finishes, a new prompt
    // answers.
    drop(held);
    client
        .pty
        .wait_for_after(mark, "heldanswer42", "the held turn's answer");
    client.submit("still here");
    client
        .pty
        .wait_for_after(mark, "thirdanswer42", "an answer after the stay");
    world.wait_for_idle();

    // An older target of another schema, the daemon idle: the client
    // stays and the daemon keeps running.
    let older_version = release_version(0);
    let older_wire = Identity {
        build_version: older_version.clone(),
        build_id: format!("{older_version}+other-wire"),
        ..other_wire_of(new)
    };
    let older = world.install_reporting(
        "eukhe-older-other-wire",
        &json!({"version": older_version, "identity": older_wire}),
        new,
    );
    world.point_launcher(&older);
    let blocked = Plan::Blocked {
        daemon_version: old.version.clone(),
    }
    .stay_message(&Target {
        exe: world.launcher(),
        version: older_version,
        identity: Some(older_wire),
    })
    .expect("a stay message");
    let mark = client.pty.mark();
    client.submit("/restart");
    client
        .pty
        .wait_for_after(mark, &blocked, "the blocked stay message");
    assert_eq!(
        (world.daemon(), launched_payload(&world.launcher())),
        (before, older),
        "the idle daemon keeps running"
    );
    assert_one_session_holding(&world, &["remember alpha42", "hold this", "still here"]);
}

/// The new build's identity on another schema.
fn other_wire_of(new: &Build) -> Identity {
    Identity {
        schema_id: format!("{}-other", new.identity.schema_id),
        ..new.identity.clone()
    }
}
