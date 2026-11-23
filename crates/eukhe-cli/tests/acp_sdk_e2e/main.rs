//! The acceptance test of `eukhe acp` as the embedding surface: the real
//! `@agentclientprotocol/sdk` client (2.9.1, pinned with ajv by
//! `package-lock.json` here and installed by `npm ci` into the target
//! dir) drives the real binary over stdio on the faux provider, and ajv
//! checks every `_eukhe/` payload against
//! `docs/embed/eukhe-acp.schema.json`. `client.mjs` holds the scenarios;
//! this file builds each one's sandbox (home, git workspace, daemon
//! socket, faux scripts) and runs it. Needs `node` and `npm` on PATH.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::{json, Value};

#[path = "../support/eukhe.rs"]
mod eukhe;

/// This test's directory: the lockfile, its manifest and the client.
const FIXTURE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/acp_sdk_e2e");

/// The installed client: `node_modules` from `npm ci` of the fixture's
/// lockfile, beside a copy of `client.mjs` (node resolves its imports
/// next to it). Tests run in parallel processes: one installs, under a
/// file lock, the others wait for it; a changed lockfile installs again.
fn installed_client() -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("acp-sdk-e2e");
    std::fs::create_dir_all(&dir).expect("the client dir");
    let lock = std::fs::File::create(dir.join(".install.lock")).expect("the install lock");
    lock.lock().expect("hold the install lock");
    let fixture = |name: &str| {
        std::fs::read(Path::new(FIXTURE).join(name))
            .unwrap_or_else(|error| panic!("{name}: {error}"))
    };
    let lockfile = fixture("package-lock.json");
    let installed = dir.join(".installed-lock.json");
    if std::fs::read(&installed).ok().as_deref() != Some(lockfile.as_slice()) {
        std::fs::write(dir.join("package.json"), fixture("package.json")).unwrap();
        std::fs::write(dir.join("package-lock.json"), &lockfile).unwrap();
        let status = Command::new("npm")
            .args([
                "ci",
                "--ignore-scripts",
                "--no-audit",
                "--no-fund",
                "--loglevel=error",
            ])
            .current_dir(&dir)
            .stdin(Stdio::null())
            .status()
            .unwrap_or_else(|error| panic!("npm on PATH: {error}"));
        assert!(status.success(), "npm ci in {}", dir.display());
        std::fs::write(&installed, &lockfile).unwrap();
    }
    std::fs::write(dir.join("client.mjs"), fixture("client.mjs")).unwrap();
    dir
}

/// One scenario's sandbox: the home (also the workspace: a git repository
/// with a bare `remote.git` as `origin`) and the daemon socket in it. The
/// drop stops the daemon the scenario's `eukhe acp` processes started.
struct Sandbox {
    home: tempfile::TempDir,
    socket: PathBuf,
}

impl Sandbox {
    fn new() -> Sandbox {
        let home = tempfile::TempDir::new().unwrap();
        let socket = home.path().join("daemon.sock");
        let git = |args: &[&str]| {
            let status = Command::new("git")
                .args([
                    "-c",
                    "user.name=e2e",
                    "-c",
                    "user.email=e2e@example.invalid",
                    "-c",
                    "commit.gpgsign=false",
                    "-c",
                    "init.defaultBranch=main",
                ])
                .args(args)
                .current_dir(home.path())
                .env("HOME", home.path())
                .env("GIT_CONFIG_NOSYSTEM", "1")
                .status()
                .expect("git present");
            assert!(status.success(), "git {args:?}");
        };
        git(&["init", "--quiet"]);
        std::fs::write(home.path().join("README"), "e2e\n").unwrap();
        git(&["add", "README"]);
        git(&["commit", "--quiet", "-m", "first"]);
        git(&["init", "--quiet", "--bare", "remote.git"]);
        git(&["remote", "add", "origin", "./remote.git"]);
        Sandbox { home, socket }
    }

    fn path(&self) -> &Path {
        self.home.path()
    }

    /// Write a faux script into the home; its path.
    fn script(&self, name: &str, responses: &Value) -> PathBuf {
        let path = self.path().join(name);
        std::fs::write(
            &path,
            json!({ "engine": "faux", "responses": responses }).to_string(),
        )
        .unwrap();
        path
    }

    /// Run `client.mjs <scenario>` with `vars`; panics with its output
    /// unless it passes.
    fn run(&self, scenario: &str, vars: &[(&str, &Path)]) {
        let client = installed_client();
        let mut command = Command::new("node");
        command
            .arg(client.join("client.mjs"))
            .arg(scenario)
            .current_dir(self.path())
            .env("HOME", self.path())
            .env("EUKHE_BIN", env!("CARGO_BIN_EXE_eukhe"))
            .env("EUKHE_ACP_SOCKET", &self.socket)
            .env("EUKHE_ACP_WORKSPACE", self.path())
            .env(
                "EUKHE_ACP_SCHEMA",
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../../docs/embed/eukhe-acp.schema.json"),
            )
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "15000",
            )
            .env_remove("EUKHE_FAUX_SCRIPT")
            .stdin(Stdio::null());
        for (name, value) in vars {
            command.env(name, value);
        }
        eukhe::eukhe_env(&mut command);
        eukhe::scrub_provider_keys(&mut command);
        let output = command
            .output()
            .unwrap_or_else(|error| panic!("node on PATH: {error}"));
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && stdout.contains(&format!("ok {scenario}")),
            "scenario {scenario} failed ({}):\n--- stdout\n{stdout}\n--- stderr\n{stderr}",
            output.status
        );
    }
}

impl Drop for Sandbox {
    fn drop(&mut self) {
        use std::io::{BufRead as _, BufReader, Write as _};
        let Ok(mut stream) = eukhe_types::platform::transport::connect_blocking(
            &self.socket,
            eukhe_bend::rules::server_peer::PEER_RULES,
        ) else {
            return;
        };
        let frame = json!({
            "type": "command",
            "id": "shutdown-test",
            "protocol": { "name": "eukhe.daemon", "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION },
            "command": { "type": "shutdown" },
        });
        if writeln!(stream, "{frame}")
            .and_then(|()| stream.flush())
            .is_err()
        {
            return;
        }
        // The daemon exits after it answers the shutdown.
        let Ok(reader) = stream.try_clone_box() else {
            return;
        };
        let _ = reader.set_read_timeout(std::time::Duration::from_secs(30));
        let _ = BufReader::new(reader)
            .lines()
            .map_while(Result::ok)
            .find(|line| line.contains("\"shutdown-test\""));
    }
}

fn bash(script: &str) -> Value {
    json!({ "content": [
        { "type": "toolCall", "name": "bash", "arguments": { "script": script } },
    ] })
}

/// The embedding flow end to end: initialize, session/new, budget and
/// acceptance set, a prompt whose first bash call streams its output
/// (held on a FIFO until the client saw the first line) and writes a
/// note, whose second pushes (asked and allowed), the schema-checked run
/// report, effects, diff, undo, close; then a fresh `eukhe acp` process
/// resumes the session by id and answers the next prompt.
#[test]
fn the_sdk_client_runs_the_embedding_flow_and_resumes_in_a_fresh_process() {
    let sandbox = Sandbox::new();
    let gate = sandbox.path().join("gate.fifo");
    let made = Command::new("mkfifo")
        .arg(&gate)
        .status()
        .expect("mkfifo present");
    assert!(made.success(), "mkfifo {}", gate.display());
    std::fs::write(
        sandbox.path().join(".git/info/exclude"),
        "/gate.fifo\n/remote.git/\n/.eukhe/\n/*.json\n",
    )
    .unwrap();
    // The markers are printed as `streamed-%s`: the step's `$ command`
    // line never contains them.
    let stream = "printf 'streamed-%s\\n' one; read -r _ < gate.fifo; printf 'hello\\n' > note.txt; printf 'streamed-%s\\n' two";
    let push = "git push origin HEAD:refs/heads/main";
    // The resumed prompt's answer is its own text, whichever worker
    // serves it: the first process's (its script's last entry) or a
    // fresh one (the resume script's first).
    let script = sandbox.script(
        "first-script.json",
        &json!([
            bash(stream),
            bash(push),
            "Done: the note is written and pushed.",
            { "userText": true },
        ]),
    );
    let resume_script = sandbox.script("resume-script.json", &json!([{ "userText": true }]));
    sandbox.run(
        "full",
        &[
            ("EUKHE_ACP_SCRIPT", &script),
            ("EUKHE_ACP_RESUME_SCRIPT", &resume_script),
            ("EUKHE_ACP_GATE", &gate),
            ("EUKHE_ACP_BASH_STREAM", Path::new(stream)),
            ("EUKHE_ACP_BASH_PUSH", Path::new(push)),
        ],
    );
}

/// A plain ACP client that handles no `_eukhe/` method runs a turn, and
/// the SDK parses every frame the agent sends.
#[test]
fn a_plain_sdk_client_ignores_the_extensions() {
    let sandbox = Sandbox::new();
    let script = sandbox.script("script.json", &json!(["plain answer"]));
    sandbox.run("plain", &[("EUKHE_ACP_SCRIPT", &script)]);
}

/// Without a logged-in model provider, session/new and authenticate
/// answer `-32000` with `data.login` naming `eukhe login <provider>`.
#[test]
fn without_a_login_the_session_start_asks_for_one() {
    let sandbox = Sandbox::new();
    sandbox.run("no-login", &[]);
}
