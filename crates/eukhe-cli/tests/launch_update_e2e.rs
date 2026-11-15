// Harness fns are linear scripts; pid and length narrowing sits at OS
// boundaries where the values are bounded.
#![allow(clippy::too_many_lines, clippy::cast_possible_truncation)]

//! Real-terminal e2e for the launch update check and `/restart`: an
//! install laid out as install.sh lays it out runs an old version on a
//! pty, a local release mirror (`EUKHE_RELEASES_URL`) serves a newer one,
//! and the launch downloads, checks and stages it without switching the
//! launcher. The notice shows; `/restart` switches the launcher and starts
//! the new version on the same session, its transcript intact; a second
//! `/restart` (nothing staged) starts the same build again. Launches the
//! check must skip ask the mirror nothing.

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpListener;
use std::os::fd::{AsRawFd, OwnedFd};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use base64::Engine as _;
use nix::fcntl::{fcntl, FcntlArg::F_SETFL, OFlag};
use nix::pty::{openpty, Winsize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

#[path = "support/eukhe.rs"]
mod eukhe;

#[path = "support/ctty.rs"]
mod ctty;

/// The parent hands the child the launcher to run through this env var;
/// unset, the child test passes trivially.
const CHILD_ENV: &str = "EUKHE_LAUNCH_UPDATE_CHILD";

const OLD: &str = "0.10.1";
const NEW: &str = "0.10.2";

const NOTICE: &str = "/restart to apply the downloaded update";

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const PLATFORM: &str = "linux-x64";
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const PLATFORM: &str = "linux-arm64";
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const PLATFORM: &str = "darwin-arm64";

/// The terminal half: claims the pty as its controlling terminal, then
/// becomes the install's launcher (`exec`), as a user's shell runs it.
#[test]
fn launch_update_child_mode() {
    let Ok(launcher) = std::env::var(CHILD_ENV) else {
        return;
    };
    ctty::claim_controlling_tty();
    let error = Command::new(launcher).exec();
    panic!("exec the launcher: {error}");
}

/// A loopback HTTP/1.1 server answering fixed routes, one request per
/// connection, counting the requests. Bound before the client starts.
struct Mirror {
    port: u16,
    requests: Arc<AtomicUsize>,
}

impl Mirror {
    fn start(routes: HashMap<String, Vec<u8>>) -> Mirror {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind the mirror");
        let port = listener.local_addr().expect("mirror address").port();
        let requests = Arc::new(AtomicUsize::new(0));
        let counted = Arc::clone(&requests);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(mut stream) = stream else { continue };
                let Ok(clone) = stream.try_clone() else {
                    continue;
                };
                let mut reader = BufReader::new(clone);
                let mut request = String::new();
                if reader.read_line(&mut request).is_err() {
                    continue;
                }
                let mut header = String::new();
                while reader.read_line(&mut header).is_ok_and(|n| n > 2) {
                    header.clear();
                }
                counted.fetch_add(1, Ordering::SeqCst);
                let path = request.split_whitespace().nth(1).unwrap_or("/");
                let reply = match routes.get(path) {
                    Some(body) => {
                        let mut reply = format!(
                            "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                            body.len()
                        )
                        .into_bytes();
                        reply.extend_from_slice(body);
                        reply
                    }
                    None => {
                        b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
                            .to_vec()
                    }
                };
                let _ = stream.write_all(&reply);
            }
        });
        Mirror { port, requests }
    }

    fn releases(&self) -> String {
        format!("http://127.0.0.1:{}/releases", self.port)
    }

    fn pin(&self) -> String {
        format!("http://127.0.0.1:{}/pin/release.json", self.port)
    }
}

/// Release `NEW` as the release workflow publishes it: release.json,
/// SHA256SUMS, the `.tar.xz` and the pin of main. Its payload's `eukhe`
/// runs this checkout's binary with the payload as its package dir, so it
/// reports `NEW`.
fn release_routes() -> HashMap<String, Vec<u8>> {
    let real = Path::new(env!("CARGO_BIN_EXE_eukhe"))
        .canonicalize()
        .expect("the built eukhe");
    let files = [
        (
            "eukhe",
            format!(
                "#!/bin/sh\nEUKHE_PACKAGE_DIR=\"$(cd \"$(dirname \"$0\")\" && pwd)\" exec \"{}\" \"$@\"\n",
                real.display()
            ),
            0o755,
        ),
        ("package.json", format!("{{\"version\": \"{NEW}\"}}\n"), 0o644),
    ];
    let xz = liblzma::write::XzEncoder::new(Vec::new(), 0);
    let mut archive = tar::Builder::new(xz);
    for (name, content, mode) in files {
        let mut header = tar::Header::new_gnu();
        header.set_size(content.len() as u64);
        header.set_mode(mode);
        header.set_cksum();
        archive
            .append_data(&mut header, name, content.as_bytes())
            .expect("archive entry");
    }
    let tarball = archive
        .into_inner()
        .expect("archive")
        .finish()
        .expect("xz stream");
    let tag = format!("eukhe-v{NEW}");
    let name = format!("eukhe-{NEW}-{PLATFORM}.tar.xz");
    let digest = Sha256::digest(&tarball);
    let hash = base64::engine::general_purpose::STANDARD.encode(digest);
    let url = format!("https://example.invalid/releases/download/{tag}/{name}");
    let pin = json!({
        "version": NEW,
        "tag": tag,
        "assets": {"system": {
            "url": url.replace(".tar.xz", ".tar.gz"),
            "hash": format!("sha256-{}", base64::engine::general_purpose::STANDARD.encode([1u8; 32])),
            "xz": {"url": url, "hash": format!("sha256-{hash}")},
        }},
    });
    HashMap::from([
        (
            "/releases/latest/download/release.json".to_string(),
            json!({"version": NEW, "tag": tag, "assets": {}})
                .to_string()
                .into_bytes(),
        ),
        (
            format!("/releases/download/{tag}/SHA256SUMS"),
            format!("{digest:x}  {name}\n").into_bytes(),
        ),
        (format!("/releases/download/{tag}/{name}"), tarball),
        (
            "/pin/release.json".to_string(),
            pin.to_string().into_bytes(),
        ),
    ])
}

/// How a launch may reach the mirror.
#[derive(Clone, Copy)]
enum Launch {
    /// Online, the check on.
    Checks,
    /// Offline mode.
    Offline,
    /// `update.autoDownload` off.
    TurnedOff,
    /// A CI run.
    Ci,
}

/// The test's world: an install of `OLD` (`root/eukhe-OLD`, the real
/// binary reporting `OLD` through its package.json, and `bin/eukhe`), the
/// agent dir, the daemon socket and the mirror.
struct World {
    dir: tempfile::TempDir,
    mirror: Mirror,
}

impl World {
    fn new(launch: Launch) -> World {
        let dir = tempfile::tempdir().expect("temp dir");
        let world = World {
            dir,
            mirror: Mirror::start(release_routes()),
        };
        for sub in ["agent/sessions", "project", "tmp", "bin", "mise"] {
            std::fs::create_dir_all(world.base().join(sub)).expect("world dir");
        }
        let payload = world.root().join(format!("eukhe-{OLD}"));
        std::fs::create_dir_all(&payload).expect("payload dir");
        std::fs::copy(env!("CARGO_BIN_EXE_eukhe"), payload.join("eukhe")).expect("copy eukhe");
        std::fs::write(
            payload.join("package.json"),
            format!("{{\"version\": \"{OLD}\"}}\n"),
        )
        .expect("manifest");
        std::fs::write(world.launcher(), launcher_script(&payload)).expect("launcher");
        std::fs::set_permissions(world.launcher(), std::fs::Permissions::from_mode(0o755))
            .expect("launcher mode");
        let settings = match launch {
            Launch::TurnedOff => json!({
                "terminal": {"fullscreen": false},
                "update": {"autoDownload": false},
            }),
            Launch::Checks | Launch::Offline | Launch::Ci => {
                json!({"terminal": {"fullscreen": false}})
            }
        };
        std::fs::write(
            world.agent_dir().join("settings.json"),
            settings.to_string(),
        )
        .expect("settings");
        std::fs::write(
            world.base().join("script.json"),
            json!({"responses": ["firstanswer42", "secondanswer42"]}).to_string(),
        )
        .expect("faux script");
        world
    }

    fn base(&self) -> PathBuf {
        self.dir.path().canonicalize().expect("temp dir path")
    }

    fn root(&self) -> PathBuf {
        self.base().join("root")
    }

    fn launcher(&self) -> PathBuf {
        self.base().join("bin/eukhe")
    }

    fn agent_dir(&self) -> PathBuf {
        self.base().join("agent")
    }

    fn socket(&self) -> PathBuf {
        self.base().join("daemon.sock")
    }

    /// The install's launcher, run by a shell on a fresh pty.
    fn client(&self, launch: Launch) -> Client {
        let pty = openpty(
            Some(&Winsize {
                ws_row: 30,
                ws_col: 120,
                ws_xpixel: 0,
                ws_ypixel: 0,
            }),
            None,
        )
        .expect("open pty");
        let slave = pty.slave;
        let base = self.base();
        let path = format!(
            "{}:{}",
            base.join("bin").display(),
            std::env::var("PATH").unwrap_or_default()
        );
        let mut command = Command::new(std::env::current_exe().expect("test binary"));
        command
            .args(["--exact", "launch_update_child_mode", "--nocapture"])
            .current_dir(base.join("project"))
            .env_clear()
            .env(CHILD_ENV, self.launcher())
            .env("PATH", path)
            .env("HOME", &base)
            .env("TMPDIR", base.join("tmp"))
            .env("TERM", "xterm-256color")
            .env("EUKHE_CODING_AGENT_DIR", self.agent_dir())
            .env("EUKHE_SESSION_DIR", self.agent_dir().join("sessions"))
            .env("EUKHE_DAEMON_SOCKET", self.socket())
            .env("EUKHE_FAUX_SCRIPT", base.join("script.json"))
            .env("EUKHE_INSTALL_BIN_DIR", base.join("bin"))
            .env("EUKHE_RELEASES_URL", self.mirror.releases())
            .env("EUKHE_RELEASE_PIN_URL", self.mirror.pin())
            .env("MISE_DATA_DIR", base.join("mise"))
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "15000",
            )
            .stdin(slave.try_clone().expect("clone pty slave"))
            .stdout(slave.try_clone().expect("clone pty slave"))
            .stderr(slave.try_clone().expect("clone pty slave"));
        eukhe::eukhe_env(&mut command);
        match launch {
            Launch::Checks | Launch::TurnedOff => {}
            Launch::Offline => {
                command.env("EUKHE_OFFLINE", "1");
            }
            Launch::Ci => {
                command.env("CI", "true");
            }
        }
        let child = command.spawn().expect("spawn the terminal client");
        drop(command);
        drop(slave);
        Client {
            child,
            pty: PtyReader::new(pty.master),
        }
    }

    /// The payload the launcher execs.
    fn launched_payload(&self) -> PathBuf {
        let script = std::fs::read_to_string(self.launcher()).expect("launcher");
        let line = script
            .lines()
            .find_map(|line| line.strip_prefix("exec \""))
            .expect("the launcher's exec line");
        PathBuf::from(line.trim_end_matches("/eukhe\" \"$@\""))
    }

    /// The session storages (`<sessions>/<id>/`).
    fn sessions(&self) -> Vec<PathBuf> {
        std::fs::read_dir(self.agent_dir().join("sessions"))
            .expect("sessions dir")
            .map(|entry| entry.expect("session entry").path())
            .filter(|path| path.is_dir())
            .collect()
    }
}

impl Drop for World {
    fn drop(&mut self) {
        graceful_shutdown(&self.socket());
    }
}

fn launcher_script(payload: &Path) -> String {
    format!(
        "#!/bin/sh\n# eukhe launcher written by install.sh; the payload sits beside itself\nexec \"{}/eukhe\" \"$@\"\n",
        payload.display()
    )
}

/// The protocol shutdown of the daemon the client started; waits
/// (bounded) for the supervisor its hello names to exit.
fn graceful_shutdown(socket: &Path) {
    let Ok(stream) = eukhe_types::platform::transport::connect_std(socket) else {
        return;
    };
    let Ok(mut writer) = stream.try_clone() else {
        return;
    };
    let mut reader = BufReader::new(stream);
    let mut hello = String::new();
    if reader.read_line(&mut hello).is_err() {
        return;
    }
    let Ok(hello) = serde_json::from_str::<Value>(hello.trim()) else {
        return;
    };
    let Some(pid) = hello["supervisorPid"].as_u64() else {
        return;
    };
    let shutdown = json!({
        "type": "command",
        "id": "launch-update-e2e-shutdown",
        "protocol": {"name": "eukhe.daemon", "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION},
        "command": {"type": "shutdown", "force": true},
    });
    let _ = writeln!(writer, "{shutdown}");
    let _ = writer.flush();
    let deadline = Instant::now() + Duration::from_secs(10);
    let pid = u32::try_from(pid).unwrap_or(0);
    while matches!(
        eukhe_types::platform::process::is_process_alive(pid),
        Ok(true)
    ) && Instant::now() < deadline
    {
        std::thread::sleep(Duration::from_millis(20));
    }
}

struct Client {
    child: Child,
    pty: PtyReader,
}

impl Client {
    /// Type `text` and Enter once the echo shows.
    fn submit(&mut self, text: &str) {
        self.pty.write(text.as_bytes());
        self.pty.wait_for(text, "the typed text");
        self.pty.write(b"\r");
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        let _ = self.child.kill();
        // Keep reading the pty while the child exits, as a terminal does.
        while matches!(self.child.try_wait(), Ok(None)) {
            self.pty.drain();
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}

/// Non-blocking reader over the pty master.
struct PtyReader {
    file: std::fs::File,
    output: Vec<u8>,
}

impl PtyReader {
    fn new(master: OwnedFd) -> PtyReader {
        fcntl(master.as_raw_fd(), F_SETFL(OFlag::O_NONBLOCK)).expect("pty master non-blocking");
        PtyReader {
            file: master.into(),
            output: Vec::new(),
        }
    }

    fn drain(&mut self) {
        let mut buffer = vec![0u8; 65536];
        while let Ok(n) = self.file.read(&mut buffer) {
            if n == 0 {
                break;
            }
            self.output.extend_from_slice(&buffer[..n]);
        }
    }

    fn write(&mut self, payload: &[u8]) {
        let deadline = Instant::now() + Duration::from_secs(30);
        let mut rest = payload;
        while !rest.is_empty() {
            match self.file.write(rest) {
                Ok(n) => rest = &rest[n..],
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    assert!(Instant::now() < deadline, "the pty never took the input");
                    self.drain();
                    std::thread::sleep(Duration::from_millis(10));
                }
                Err(error) => panic!("write to the pty: {error}"),
            }
        }
    }

    /// The byte offset of the stream so far: a later wait reads past it.
    fn mark(&mut self) -> usize {
        self.drain();
        self.output.len()
    }

    fn wait_for(&mut self, needle: &str, what: &str) {
        self.wait_for_after(0, needle, what);
    }

    /// Drain until `needle` shows in the escape-stripped stream after
    /// byte `from`.
    fn wait_for_after(&mut self, from: usize, needle: &str, what: &str) {
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            self.drain();
            let text = strip_escapes(&self.output[from..]);
            if text.contains(needle) {
                return;
            }
            assert!(
                Instant::now() < deadline,
                "timeout waiting for {what} ({needle:?}); stream tail:\n{}",
                &text[text.len().saturating_sub(3000)..]
            );
            std::thread::sleep(Duration::from_millis(20));
        }
    }
}

/// The stream without CSI and OSC sequences.
fn strip_escapes(bytes: &[u8]) -> String {
    let text = String::from_utf8_lossy(bytes);
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\x1b' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('[') => {
                for c in chars.by_ref() {
                    if ('@'..='~').contains(&c) {
                        break;
                    }
                }
            }
            Some(']') => {
                while let Some(c) = chars.next() {
                    if c == '\x07' {
                        break;
                    }
                    if c == '\x1b' {
                        chars.next();
                        break;
                    }
                }
            }
            Some(_) | None => {}
        }
    }
    out
}

#[test]
fn a_launch_stages_the_new_release_and_restart_lands_on_it_with_the_session() {
    let world = World::new(Launch::Checks);
    let mut client = world.client(Launch::Checks);
    client.submit("remember alpha42");
    client.pty.wait_for("firstanswer42", "the first answer");
    client.pty.wait_for(NOTICE, "the staged-update notice");

    // Staged: the new payload sits beside the install, the launcher still
    // runs the old one.
    let old = world.root().join(format!("eukhe-{OLD}"));
    let new = world.root().join(format!("eukhe-{NEW}"));
    assert_eq!(
        (
            std::fs::read_to_string(new.join("package.json")).expect("the staged manifest"),
            world.launched_payload(),
        ),
        (format!("{{\"version\": \"{NEW}\"}}\n"), old)
    );

    // `/restart` applies it and starts the new version on this session.
    let before = client.pty.mark();
    client.submit("/restart");
    client.pty.wait_for_after(
        before,
        &format!("Restarting on eukhe {NEW}"),
        "the restart note",
    );
    assert_eq!(world.launched_payload(), new);
    let restarted = client.pty.mark();
    client.pty.wait_for_after(
        restarted,
        "firstanswer42",
        "the session's transcript, reopened",
    );

    // The running build reports the new version: a second `/restart`
    // (nothing staged) names the build it starts again, and the session
    // still answers.
    client.submit("/restart");
    client.pty.wait_for_after(
        restarted,
        &format!("Restarting on eukhe {NEW}"),
        "the second restart note",
    );
    let again = client.pty.mark();
    client.pty.wait_for_after(
        again,
        "firstanswer42",
        "the transcript after the second restart",
    );
    client.submit("and now?");
    client.pty.wait_for_after(
        again,
        "secondanswer42",
        "an answer on the restarted session",
    );

    // One session the whole way, holding both prompts.
    let sessions = world.sessions();
    assert_eq!(sessions.len(), 1, "one session: {sessions:?}");
    let log = std::fs::read_to_string(sessions[0].join("main.jsonl")).expect("session log");
    assert!(
        log.contains("remember alpha42") && log.contains("and now?"),
        "the session holds both prompts"
    );
}

#[test]
fn offline_ci_and_turned_off_launches_ask_the_mirror_nothing() {
    for launch in [Launch::Offline, Launch::Ci, Launch::TurnedOff] {
        let world = World::new(launch);
        let mut client = world.client(launch);
        client.submit("remember alpha42");
        client.pty.wait_for("firstanswer42", "the first answer");
        drop(client);
        assert_eq!(
            (
                world.mirror.requests.load(Ordering::SeqCst),
                world.root().join(format!("eukhe-{NEW}")).exists(),
            ),
            (0, false),
            "a skipped launch neither asks nor stages"
        );
    }
}
