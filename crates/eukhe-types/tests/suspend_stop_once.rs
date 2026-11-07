//! `stop_own_process_group` stops the process once: one SIGCONT (the
//! shell's `fg`) resumes it for good. A thread-directed SIGTSTP queued
//! after the group signal could miss the stop it was meant to join (xnu
//! stops the task inside `kill`; on Linux another thread can start the
//! group stop and the caller stops at its next return to user space), so
//! the SIGCONT could not discard it and it stopped the resumed process a
//! second time: a resumed TUI sat stopped and painted nothing.
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
/// Suspend cycles of one child. On macOS the double stop showed on every
/// cycle; on Linux it is a race between the caller and the thread that
/// takes the group signal, lost on a few percent of the cycles, so the
/// child repeats the stop until a lost race is all but certain.
const CYCLES: u32 = 200;

/// The child half: a second thread makes the process multi-threaded (the
/// TUI's shape: the loop plus its terminal reader), then the caller stops
/// its own group `CYCLES` times and reports each continuation. A plain
/// `cargo test` run (no `CHILD_ENV`) passes trivially.
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
    for _ in 0..CYCLES {
        eukhe_types::platform::process::stop_own_process_group().expect("stop the process group");
        println!("{RESUMED}");
    }
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
    // Every stop gets exactly one SIGCONT, so a doubled stop does not
    // strand the child: it shows as more stops than cycles.
    let mut stops = 0_u32;
    let exit = loop {
        match waitpid(pid, Some(WaitPidFlag::WUNTRACED)).expect("wait for the child") {
            WaitStatus::Stopped(_, signal) => {
                stops += 1;
                if stops > CYCLES {
                    let _ = kill(pid, Signal::SIGKILL);
                    let _ = waitpid(pid, None);
                    panic!(
                        "the child stopped again ({signal}) after a SIGCONT resumed it: \
                         {stops} stops in {CYCLES} cycles"
                    );
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
    assert_eq!(
        stops, CYCLES,
        "the child ran past a stop or stopped again after its resume"
    );
    // libtest's own `test stop_once_child ... ` shares the first line, so
    // the markers are counted, not the lines.
    assert_eq!(
        output.matches(RESUMED).count(),
        usize::try_from(CYCLES).expect("cycles fit usize"),
        "the child did not report every resume: {output}"
    );
}
