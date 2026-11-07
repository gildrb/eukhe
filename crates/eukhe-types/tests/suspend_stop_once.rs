//! `stop_own_process_group` stops the process once: one SIGCONT (the
//! shell's `fg`) resumes it for good. On macOS the Linux-only
//! thread-directed SIGTSTP survived xnu's SIGCONT and stopped the
//! process a second time, so a resumed TUI sat stopped and painted
//! nothing.
#![cfg(unix)]

use std::io::Read;
use std::os::unix::process::CommandExt;
use std::process::{Command, Stdio};

use nix::sys::signal::{kill, Signal};
use nix::sys::wait::{waitpid, WaitPidFlag, WaitStatus};
use nix::unistd::Pid;

/// Set only when this binary is re-executed as the stopping child.
const CHILD_ENV: &str = "EUKHE_SUSPEND_STOP_ONCE_CHILD";
const RESUMED: &str = "resumed";

/// The child half: a second thread makes the process multi-threaded (the
/// TUI's shape: the loop plus its terminal reader), then the caller stops
/// its own group and reports the continuation. A plain `cargo test` run
/// (no `CHILD_ENV`) passes trivially.
#[test]
fn stop_once_child() {
    if std::env::var_os(CHILD_ENV).is_none() {
        return;
    }
    let (ready_tx, ready_rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        ready_tx.send(()).expect("signal the parked thread's start");
        loop {
            std::thread::park();
        }
    });
    ready_rx.recv().expect("the parked thread started");
    eukhe_types::platform::process::stop_own_process_group().expect("stop the process group");
    print!("{RESUMED}");
}

#[test]
fn one_sigcont_resumes_a_stopped_process_group() {
    // Its own process group, parented by this runner in another group of
    // the same session: the group is not orphaned, so SIGTSTP stops it,
    // and the child's kill(0) never reaches this runner.
    // The child is reaped by the `waitpid(WUNTRACED)` loop below (std's
    // `wait` cannot report the stops this test counts), which clippy's
    // `Child::wait` check does not see.
    #[allow(clippy::zombie_processes)]
    let mut child = Command::new(std::env::current_exe().expect("test binary"))
        .args([
            "--exact",
            "stop_once_child",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(CHILD_ENV, "1")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .process_group(0)
        .spawn()
        .expect("spawn the stopping child");
    let pid = Pid::from_raw(i32::try_from(child.id()).expect("pid fits i32"));
    let mut stops = 0_u32;
    let exit = loop {
        match waitpid(pid, Some(WaitPidFlag::WUNTRACED)).expect("wait for the child") {
            WaitStatus::Stopped(_, signal) => {
                stops += 1;
                if stops > 1 {
                    // The failing case leaves the child stopped for good:
                    // end it so the run leaks no stopped process.
                    let _ = kill(pid, Signal::SIGKILL);
                    let _ = waitpid(pid, None);
                    panic!("the child stopped again ({signal}) after the SIGCONT resumed it");
                }
                kill(pid, Signal::SIGCONT).expect("SIGCONT the child");
            }
            WaitStatus::Exited(_, code) => break code,
            other => panic!("the child ended unexpectedly: {other:?}"),
        }
    };
    let mut output = String::new();
    child
        .stdout
        .take()
        .expect("child stdout")
        .read_to_string(&mut output)
        .expect("read the child's output");
    assert_eq!(exit, 0, "the child failed; output: {output}");
    assert!(
        output.contains(RESUMED),
        "the child ran past its stop: {output}"
    );
}
