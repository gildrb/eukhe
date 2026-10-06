//! `eukhe agents` opens the interactive agents view. Without a terminal it
//! must refuse with a pointer to `eukhe list`, not fall into an empty
//! print run that starts (and then cancels) the kernel setup.

use std::process::{Command, Stdio};

#[test]
fn agents_without_a_terminal_refuses_instead_of_running_print_mode() {
    let dir = tempfile::tempdir().expect("temp dir");
    let output = Command::new(env!("CARGO_BIN_EXE_eukhe"))
        .arg("agents")
        .current_dir(dir.path())
        .env_clear()
        .env("HOME", dir.path())
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("EUKHE_TELEMETRY", "0")
        .env("EUKHE_CODING_AGENT_DIR", dir.path().join("agent"))
        .env("EUKHE_DAEMON_SOCKET", dir.path().join("d.sock"))
        .env("EUKHE_KERNEL_VENV", dir.path().join("venv"))
        .stdin(Stdio::null())
        .output()
        .expect("run eukhe agents");
    assert_eq!(
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        ),
        (
            Some(1),
            String::new(),
            "Error: agents requires an interactive terminal; `eukhe list` prints the agents\n"
                .to_string(),
        )
    );
    assert!(
        !dir.path().join("venv").exists(),
        "no kernel setup starts for a refused command"
    );
}
