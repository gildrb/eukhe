//! The Signal gateway end to end: a real supervisor, `eukhe gateway` with
//! a fake `signal-cli` (`support/fake_signal_cli.rs`) and the scripted faux
//! model (`EUKHE_FAUX_SCRIPT`), every process in a clean environment over
//! one temp home (its own agent dir and daemon socket, offline, no
//! provider keys).
//!
//! New assertions: [`Setup::start`] with the model's script, then the
//! phone helpers - `phone.say(text)`, `phone.wait_reply(&said, X)`, and
//! `phone.settle_run(&said)` (every reply of the run once it ended) or
//! `phone.assert_run_never_says(&said, Y)`.

use std::path::Path;
use std::process::{Child, Command, Stdio};

use serde_json::{json, Value};

#[path = "support/eukhe.rs"]
mod eukhe;
#[path = "support/fake_signal_cli.rs"]
mod fake_signal_cli;
#[path = "../../eukhe-daemon/tests/support/process.rs"]
mod process;

use eukhe::{daemon_mode_args, eukhe_env};
use fake_signal_cli::{FakeSignalCli, WAIT};
use process::Daemon;

/// The gateway's Signal account.
const ACCOUNT: &str = "+15550000001";
/// The phone: the one allowed contact.
const PHONE: &str = "+15550000002";

/// The `eukhe` binary in an `env -i` environment over `home`: only the
/// agent dir, offline mode, `PATH` and the kernel runtime the e2e tests
/// share.
fn clean_eukhe(home: &Path, agent_dir: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_eukhe"));
    command
        .env_clear()
        .env("HOME", home)
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("EUKHE_CODING_AGENT_DIR", agent_dir)
        .env("EUKHE_OFFLINE", "1")
        .current_dir(home);
    eukhe_env(&mut command);
    command
}

/// A supervisor, the gateway, and the phone over one temp home.
struct Setup {
    gateway: Child,
    phone: FakeSignalCli,
    _daemon: Daemon,
    _root: tempfile::TempDir,
}

impl Drop for Setup {
    fn drop(&mut self) {
        let _ = self.gateway.kill();
        let _ = self.gateway.wait();
    }
}

impl Setup {
    /// Start the daemon and the gateway; the sessions the gateway opens run
    /// the faux model answering `responses` (faux-script steps) in order.
    fn start(responses: &Value) -> Setup {
        let root = tempfile::TempDir::new().expect("temp root");
        let home = root.path();
        let agent_dir = home.join("agent");
        let work = home.join("work");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");
        std::fs::create_dir_all(&work).expect("workspace dir");
        let phone = FakeSignalCli::start(home, ACCOUNT, PHONE);
        std::fs::write(
            agent_dir.join("settings.json"),
            json!({
                "gateway": { "signal": {
                    "account": ACCOUNT,
                    "allow": [PHONE],
                    "cliPath": phone.cli_path.display().to_string(),
                    "cwd": work.display().to_string(),
                }},
            })
            .to_string(),
        )
        .expect("write settings");
        let script = home.join("script.json");
        std::fs::write(&script, json!({ "responses": responses }).to_string())
            .expect("write the faux script");
        let socket = home.join("daemon.sock");
        let mut daemon = clean_eukhe(home, &agent_dir);
        daemon_mode_args(&mut daemon, &socket, &agent_dir);
        let daemon = Daemon::spawn_listening(&mut daemon, &socket, WAIT);
        let gateway = clean_eukhe(home, &agent_dir)
            .args(["gateway", "--daemon-socket"])
            .arg(&socket)
            .env("EUKHE_FAUX_SCRIPT", &script)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .spawn()
            .expect("start the gateway");
        let setup = Setup {
            gateway,
            phone,
            _daemon: daemon,
            _root: root,
        };
        setup.phone.wait_started();
        setup
    }
}

#[test]
fn the_phone_gets_the_help_and_the_faux_models_answer() {
    let setup = Setup::start(&json!([{ "text": "Four, from the faux model." }]));
    let phone = &setup.phone;

    let help = phone.say("/help");
    let reply = phone.wait_reply(&help, "/status");
    assert!(
        ["/help", "/new", "/stop", "/model"]
            .iter()
            .all(|command| reply.contains(command)),
        "the help lists the phone commands: {reply}"
    );

    let prompt = phone.say("What is two plus two?");
    assert_eq!(
        phone.assert_run_never_says(&prompt, "Error"),
        vec!["Four, from the faux model.".to_owned()],
        "the run's one message is the model's answer"
    );
    assert!(
        !phone
            .seen()
            .iter()
            .any(|seen| matches!(seen, fake_signal_cli::Seen::Other { .. })),
        "the gateway used only send, sendTyping and sendReceipt: {:#?}",
        phone.seen()
    );
}
