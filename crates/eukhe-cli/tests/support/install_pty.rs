//! The harness of the e2es that run an install of the release installer
//! on a pty: the terminal child (the test binary in child mode becomes the
//! install's launcher on a fresh pty), the pty reader, the launcher script
//! install.sh writes, and the daemon wire calls a test makes beside the
//! client (hello, one command, protocol shutdown).

#![allow(dead_code)] // each including test binary uses its own subset

use std::io::{BufRead, BufReader, Read, Write};
use std::os::fd::{AsRawFd, OwnedFd};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::time::{Duration, Instant};

use nix::fcntl::{fcntl, FcntlArg::F_SETFL, OFlag};
use nix::pty::{openpty, Winsize};
use serde_json::{json, Value};

/// The parent hands the child the launcher to run through this env var;
/// unset, the child test passes trivially.
const CHILD_ENV: &str = "EUKHE_INSTALL_PTY_CHILD";

/// The child test's body: claims the pty as its controlling terminal, then
/// becomes the install's launcher (`exec`), as a user's shell runs it.
pub fn run_child() {
    let Ok(launcher) = std::env::var(CHILD_ENV) else {
        return;
    };
    super::ctty::claim_controlling_tty();
    let error = Command::new(launcher).exec();
    panic!("exec the launcher: {error}");
}

/// The test binary in child mode (`child_test`, the binary's test that
/// calls [`run_child`]) running `launcher`, with a cleared environment:
/// the caller adds the rest.
pub fn child_command(child_test: &str, launcher: &Path) -> Command {
    let mut command = Command::new(std::env::current_exe().expect("test binary"));
    command
        .args(["--exact", child_test, "--nocapture"])
        .env_clear()
        .env(CHILD_ENV, launcher);
    command
}

/// The launcher install.sh writes: it execs the payload beside it.
pub fn launcher_script(payload: &Path) -> String {
    format!(
        "#!/bin/sh\n# eukhe launcher written by install.sh; the payload sits beside itself\nexec \"{}/eukhe\" \"$@\"\n",
        payload.display()
    )
}

/// The payload the launcher at `launcher` execs.
pub fn launched_payload(launcher: &Path) -> PathBuf {
    let script = std::fs::read_to_string(launcher).expect("launcher");
    let line = script
        .lines()
        .find_map(|line| line.strip_prefix("exec \""))
        .expect("the launcher's exec line");
    PathBuf::from(line.trim_end_matches("/eukhe\" \"$@\""))
}

/// The hello of the daemon serving `socket`.
pub fn hello(socket: &Path) -> Value {
    let stream =
        eukhe_types::platform::transport::connect_std(socket).expect("connect the daemon socket");
    let mut line = String::new();
    BufReader::new(stream)
        .read_line(&mut line)
        .expect("the daemon's hello");
    serde_json::from_str(line.trim()).expect("hello JSON")
}

/// The supervisor pid a daemon's hello names.
pub fn supervisor_pid(hello: &Value) -> u32 {
    hello["supervisorPid"]
        .as_u64()
        .and_then(|pid| u32::try_from(pid).ok())
        .unwrap_or_else(|| panic!("a supervisor pid in the hello: {hello}"))
}

/// One daemon command over its own connection, answered by the response
/// with `id`.
pub fn daemon_request(socket: &Path, id: &str, command: &Value) -> Value {
    let mut writer =
        eukhe_types::platform::transport::connect_std(socket).expect("connect the daemon socket");
    let reader = writer.try_clone().expect("daemon socket clone");
    reader
        .set_read_timeout(Some(Duration::from_secs(120)))
        .expect("read timeout");
    let protocol = json!({
        "name": "eukhe.daemon",
        "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION,
    });
    let frame = json!({"type": "command", "id": id, "protocol": protocol, "command": command});
    writeln!(writer, "{frame}").expect("daemon frame");
    writer.flush().expect("daemon flush");
    BufReader::new(reader)
        .lines()
        .map(|line| serde_json::from_str::<Value>(&line.expect("daemon line")).expect("JSON"))
        .find(|frame| frame["id"] == json!(id))
        .unwrap_or_else(|| panic!("the daemon closed without answering {id}"))
}

/// Whether `pid` exited within `budget`.
pub fn exits_within(pid: u32, budget: Duration) -> bool {
    let deadline = Instant::now() + budget;
    loop {
        if !matches!(
            eukhe_types::platform::process::is_process_alive(pid),
            Ok(true)
        ) {
            return true;
        }
        if Instant::now() >= deadline {
            return false;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// The protocol shutdown of the daemon serving `socket`; waits (bounded)
/// for the supervisor its hello names to exit.
pub fn graceful_shutdown(socket: &Path) {
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
        "id": "install-pty-e2e-shutdown",
        "protocol": {"name": "eukhe.daemon", "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION},
        "command": {"type": "shutdown", "force": true},
    });
    let _ = writeln!(writer, "{shutdown}");
    let _ = writer.flush();
    exits_within(u32::try_from(pid).unwrap_or(0), Duration::from_secs(10));
}

/// A terminal client: the child on a pty, read as a terminal reads it.
pub struct Client {
    pub child: Child,
    pub pty: PtyReader,
}

impl Client {
    /// Spawn `command` on a fresh pty of `cols` columns, its stdio the
    /// pty's slave.
    pub fn spawn(mut command: Command, cols: u16) -> Client {
        let pty = openpty(
            Some(&Winsize {
                ws_row: 30,
                ws_col: cols,
                ws_xpixel: 0,
                ws_ypixel: 0,
            }),
            None,
        )
        .expect("open pty");
        let slave = pty.slave;
        command
            .stdin(slave.try_clone().expect("clone pty slave"))
            .stdout(slave.try_clone().expect("clone pty slave"))
            .stderr(slave.try_clone().expect("clone pty slave"));
        let child = command.spawn().expect("spawn the terminal client");
        drop(command);
        drop(slave);
        Client {
            child,
            pty: PtyReader::new(pty.master),
        }
    }

    /// Type `text` and Enter once the echo shows.
    pub fn submit(&mut self, text: &str) {
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
pub struct PtyReader {
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

    pub fn drain(&mut self) {
        let mut buffer = vec![0u8; 65536];
        while let Ok(n) = self.file.read(&mut buffer) {
            if n == 0 {
                break;
            }
            self.output.extend_from_slice(&buffer[..n]);
        }
    }

    pub fn write(&mut self, payload: &[u8]) {
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
    pub fn mark(&mut self) -> usize {
        self.drain();
        self.output.len()
    }

    pub fn wait_for(&mut self, needle: &str, what: &str) {
        self.wait_for_after(0, needle, what);
    }

    /// Drain until `needle` shows in the escape-stripped stream after
    /// byte `from`.
    pub fn wait_for_after(&mut self, from: usize, needle: &str, what: &str) {
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
pub fn strip_escapes(bytes: &[u8]) -> String {
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
