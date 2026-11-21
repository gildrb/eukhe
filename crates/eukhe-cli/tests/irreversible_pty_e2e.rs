//! Real-pty e2e of irreversible effects in the terminal UI: the product's
//! renderer runs on a pty against a real supervisor, and a scripted run
//! commits an edit and pushes it to a local bare repository.
//!
//! - The push runs unasked: the remote has the commit when the run ends.
//! - The end-of-run message names it, once; a later run with nothing
//!   irreversible shows none.
//! - `/effects` lists the session's ledger.
//! - `/undo` (twice: the second prompt, then the first) restores the file
//!   and names the push it cannot take back.
//!
//! The child is this binary re-executed in child mode in its own process
//! group with the pty slave as its terminal. Every wait reads the pty as
//! it becomes readable (poll) into the virtual terminal the inline writer
//! is checked against, until the rendered lines show the text or the
//! deadline.

use std::io::{Read, Write};
use std::os::fd::{AsFd, AsRawFd, OwnedFd};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use nix::fcntl::{fcntl, FcntlArg::F_SETFL, OFlag};
use nix::poll::{poll, PollFd, PollFlags, PollTimeout};
use nix::pty::{openpty, Winsize};
use serde_json::json;

use eukhe_tui::interactive::{
    run_interactive, InteractiveOptions, ModelSelection, SessionSelection, UiMode,
};

#[path = "support/eukhe.rs"]
mod eukhe;
#[path = "../../eukhe-daemon/tests/support/process.rs"]
mod process;
/// The virtual terminal the inline writer checks its frames on.
#[path = "../../eukhe-tui/src/vt.rs"]
// The test reads the logical lines only; eukhe-tui allows the cast
// crate-wide (lib.rs), and vt.rs's own tests rely on it.
#[allow(dead_code, clippy::cast_possible_truncation)]
mod vt;

/// What `vt` measures a glyph with.
mod width {
    pub(crate) fn grapheme_width(glyph: &str) -> usize {
        eukhe_tui::width::str_width(glyph)
    }
}

use eukhe::{daemon_mode_args, eukhe_command, scrub_provider_keys};
use process::Daemon;

/// The child mode's root dir (socket, workspace, script), set only when
/// this binary runs as the product under test.
const CHILD_ROOT_ENV: &str = "EUKHE_IRREVERSIBLE_PTY_CHILD_ROOT";

/// The model's one step: commit an edit, then push it.
const STEP: &str = "echo two >> notes.txt && git -c user.name=t -c user.email=t@e commit -qam two && git push -q origin main";

/// The end-of-run message's first line.
const REPORT: &str = "Irreversible effects ran this run:";

/// `/effects`' first line.
const LEDGER: &str = "Irreversible effects ran in this session:";

/// `/undo`'s line for the effects it cannot take back.
const NOT_UNDONE: &str = "Not undone (irreversible):";

/// `/undo`'s first words.
const UNDONE: &str = "Restored the workspace";

/// The push, as the end-of-run message, `/effects` and `/undo` name it.
const PUSH_LINE: &str = "- e1 git push -q origin main (exec+net)";

const PTY_ROWS: u16 = 40;
const PTY_COLS: u16 = 120;

/// The child half: the real interactive loop in terminal mode. A plain run
/// (no `CHILD_ROOT_ENV`) passes at once.
#[test]
fn irreversible_pty_child_mode() {
    let Ok(root) = std::env::var(CHILD_ROOT_ENV) else {
        return;
    };
    let root = PathBuf::from(root);
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    let _ = runtime.block_on(run_interactive(child_options(&root), UiMode::Terminal));
}

/// Run `git` in `dir`; its trimmed stdout.
fn git(dir: &Path, args: &[&str]) -> String {
    let output = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_AUTHOR_NAME", "test")
        .env("GIT_AUTHOR_EMAIL", "test@example.com")
        .env("GIT_COMMITTER_NAME", "test")
        .env("GIT_COMMITTER_EMAIL", "test@example.com")
        .output()
        .expect("git runs");
    assert!(
        output.status.success(),
        "git {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).trim().to_owned()
}

#[test]
fn an_irreversible_step_runs_unasked_and_the_tui_reports_lists_and_names_it() {
    if nix::unistd::tcgetpgrp(std::io::stdin()).is_err() {
        eprintln!(
            "no controlling-terminal session on the runner (tcgetpgrp(fd 0) failed); \
             the pty e2e needs one to drive the pty child"
        );
        return;
    }
    nix::unistd::setsid().expect("a fresh session for the harness");
    let root = tempfile::TempDir::new().expect("temp root");
    let work = root.path().join("work");
    let remote = root.path().join("remote.git");
    std::fs::create_dir_all(&work).expect("workspace");
    git(
        root.path(),
        &["init", "-q", "--bare", "-b", "main", "remote.git"],
    );
    git(&work, &["init", "-q", "-b", "main"]);
    std::fs::write(work.join("notes.txt"), "one\n").expect("seed file");
    git(&work, &["add", "notes.txt"]);
    git(&work, &["commit", "-q", "-m", "one"]);
    git(
        &work,
        &["remote", "add", "origin", &remote.display().to_string()],
    );
    git(&work, &["push", "-q", "origin", "main"]);
    std::fs::write(
        root.path().join("script.json"),
        json!({ "responses": [
            { "content": [{ "type": "toolCall", "name": "bash", "id": "call-1",
                "arguments": { "script": STEP } }], "stopReason": "toolUse" },
            { "text": "Committed and pushed." },
            { "text": "Nothing else to do." },
        ]})
        .to_string(),
    )
    .expect("write script");
    let agent_dir = root.path().join("agent");
    std::fs::create_dir_all(agent_dir.join("sessions")).expect("agent dir");
    let socket = root.path().join("daemon.sock");
    let mut command = eukhe_command();
    daemon_mode_args(&mut command, &socket, &agent_dir);
    scrub_provider_keys(&mut command)
        .env("HOME", root.path())
        .env("EUKHE_DAEMON_WORKER_CONNECT_TIMEOUT_MS", "90000");
    let _daemon = Daemon::spawn_listening(&mut command, &socket, Duration::from_mins(1));

    let pty = openpty(
        Some(&Winsize {
            ws_row: PTY_ROWS,
            ws_col: PTY_COLS,
            ws_xpixel: 0,
            ws_ypixel: 0,
        }),
        None,
    )
    .expect("open pty");
    let mut child = spawn_child(root.path(), &pty.slave);
    let mut tty = Pty::new(pty.master);
    tty.wait_for("the first frame", |lines| shows(lines, "eukhe"));

    // The push runs unasked; the message at the run's end names it.
    tty.send("Commit and push.\r");
    tty.wait_for("the end-of-run message", |lines| shows(lines, REPORT));
    assert_eq!(
        git(&remote, &["rev-parse", "main"]),
        git(&work, &["rev-parse", "main"]),
        "the push ran without a question"
    );

    // A run with nothing irreversible; then the ledger.
    tty.send("Anything else?\r");
    tty.wait_for("the second run's answer", |lines| {
        shows(lines, "Nothing else to do.")
    });
    tty.send("/effects\r");
    tty.wait_for("the ledger", |lines| shows(lines, LEDGER));

    // `/undo` takes back the second prompt (nothing irreversible), then the
    // first: its file comes back and the push is named as not undone.
    tty.send("/undo\r");
    tty.wait_for("the first undo", |lines| {
        lines.iter().filter(|line| line.contains(UNDONE)).count() == 1
    });
    tty.send("/undo\r");
    tty.wait_for("the second undo", |lines| shows(lines, NOT_UNDONE));
    assert_eq!(
        std::fs::read_to_string(work.join("notes.txt")).expect("read notes"),
        "one\n",
        "/undo restored the file"
    );

    // On the rendered screen and its scrollback (redraws land on the same
    // cells): the end-of-run message once, from the first run only, with
    // exactly that run's line; the ledger and the second undo name the same
    // effect.
    let lines = tty.lines();
    assert_eq!(
        [REPORT, LEDGER, NOT_UNDONE].map(|header| headed(&lines, header)),
        [
            vec![PUSH_LINE.to_owned()],
            vec![PUSH_LINE.to_owned()],
            vec![PUSH_LINE.to_owned()],
        ],
        "rendered:\n{}",
        lines.join("\n")
    );

    let _ = child.kill();
    let _ = child.wait();
}

/// Some rendered line holds `needle`.
fn shows(lines: &[String], needle: &str) -> bool {
    lines.iter().any(|line| line.contains(needle))
}

/// For each rendered line holding `header`, the line after it (trimmed).
fn headed(lines: &[String], header: &str) -> Vec<String> {
    lines
        .windows(2)
        .filter(|pair| pair[0].contains(header))
        .map(|pair| pair[1].trim().to_owned())
        .collect()
}

/// The pty master, rendered through the virtual terminal the inline writer
/// is checked against: a redraw paints the same cells again, so a row
/// shows once however often it is painted.
struct Pty {
    file: std::fs::File,
    /// Read bytes that end inside a UTF-8 sequence, kept for the next read.
    partial: Vec<u8>,
    screen: vt::Vt,
}

impl Pty {
    fn new(master: OwnedFd) -> Pty {
        fcntl(master.as_raw_fd(), F_SETFL(OFlag::O_NONBLOCK)).expect("pty master non-blocking");
        Pty {
            file: master.into(),
            partial: Vec::new(),
            screen: vt::Vt::new(usize::from(PTY_COLS), usize::from(PTY_ROWS)),
        }
    }

    /// Type `keys`.
    fn send(&mut self, keys: &str) {
        self.file
            .write_all(keys.as_bytes())
            .expect("write to the pty");
    }

    /// The logical lines of the scrollback and the screen.
    fn lines(&self) -> Vec<String> {
        self.screen.logical()
    }

    /// Feed `bytes` to the screen, keeping an unfinished UTF-8 sequence.
    fn feed(&mut self, bytes: &[u8]) {
        self.partial.extend_from_slice(bytes);
        let valid = match std::str::from_utf8(&self.partial) {
            Ok(text) => text.len(),
            Err(error) => error.valid_up_to(),
        };
        let text = String::from_utf8_lossy(&self.partial[..valid]).into_owned();
        self.screen.feed(&text);
        self.partial.drain(..valid);
    }

    /// Read the pty as it becomes readable until the rendered lines pass
    /// `done` (90 s at most: a run and a snapshot restore each wait on the
    /// daemon).
    fn wait_for(&mut self, what: &str, done: impl Fn(&[String]) -> bool) {
        let deadline = Instant::now() + Duration::from_secs(90);
        while !done(&self.lines()) {
            let left = deadline.saturating_duration_since(Instant::now());
            assert!(
                !left.is_zero(),
                "timeout waiting for {what}; rendered:\n{}",
                self.lines().join("\n")
            );
            let wait = PollTimeout::try_from(left).unwrap_or(PollTimeout::MAX);
            let mut fds = [PollFd::new(self.file.as_fd(), PollFlags::POLLIN)];
            poll(&mut fds, wait).expect("poll the pty");
            let mut buffer = [0u8; 8192];
            if let Ok(n) = self.file.read(&mut buffer) {
                self.feed(&buffer[..n]);
            }
        }
    }
}

/// This binary in child mode, in its own process group, on the pty.
fn spawn_child(root: &Path, slave: &OwnedFd) -> Child {
    let stdio = || -> Stdio { slave.try_clone().expect("clone pty slave").into() };
    Command::new(std::env::current_exe().expect("test binary"))
        .args(["--exact", "irreversible_pty_child_mode", "--nocapture"])
        .env(CHILD_ROOT_ENV, root)
        .env("HOME", root)
        .env_remove("TMUX")
        .stdin(stdio())
        .stdout(stdio())
        .stderr(stdio())
        .process_group(0)
        .spawn()
        .expect("spawn child")
}

fn child_options(root: &Path) -> InteractiveOptions {
    InteractiveOptions {
        budget: None,
        models: None,
        socket_path: root.join("daemon.sock"),
        cwd: root.join("work"),
        session_dir: Some(root.join("agent").join("sessions")),
        script_path: Some(root.join("script.json")),
        model_selection: ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: SessionSelection::New,
        initial_message: None,
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        client_auth: None,
        provider_auth: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
        dictation: None,
        daemon_launcher: None,
        restart: None,
    }
}
