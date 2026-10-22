//! Process identity, shared by eukhe-core (kernel/orphan journal) and eukhe-daemon
//! (session leases, wire auth).
//!
//! `process_start_id` is the pid-reuse identity the TS product records as
//! `proc:<starttime>` (TS `getProcessStartId`, `core/session-lease.ts`): the
//! kernel-reported process start time from `/proc/<pid>/stat` field 22. A
//! recycled pid has a different start time, so a recorded identity that still
//! matches proves the pid still names the same process. `None` means the
//! platform exposes no identity - owners then trust liveness checks alone,
//! exactly like TS records with `processStartId: undefined`.

/// The pid-reuse identity: `/proc/<pid>/stat` field 22 (starttime) as
/// `proc:<starttime>`, else the portable `ps:<lstart>` identity (TS
/// `getPsProcessStartId`) by running `ps -o lstart=` when the pid still
/// exists. A recycled pid has a different start time, so a recorded
/// identity that still matches proves the pid still names the same
/// process. `None` only when the platform exposes neither - owners then
/// trust liveness checks alone, exactly like TS records with
/// `processStartId: undefined`.
#[must_use]
pub fn process_start_id(pid: u32) -> Option<String> {
    if pid == 0 {
        return None;
    }
    if let Ok(stat) = std::fs::read_to_string(format!("/proc/{pid}/stat")) {
        let command_end = stat.rfind(')')?;
        let start_time = stat[command_end + 2..].split(' ').nth(19)?;
        if !start_time.is_empty() {
            return Some(format!("proc:{start_time}"));
        }
    }
    ps_process_start_id(pid)
}

/// The `ps` the no-/proc probes run. macOS: `/bin/ps` by absolute path,
/// so the identity and the zombie demotion never depend on `PATH` (the
/// value is persisted by earlier builds and the TS product, so a missing
/// or shadowed `ps` must not read as a recycled pid).
#[cfg(target_vendor = "apple")]
const PS: &str = "/bin/ps";
#[cfg(not(target_vendor = "apple"))]
const PS: &str = "ps";

/// The `ps -p <pid> -o lstart=` identity (TS `getPsProcessStartId`):
/// `lstart` renders in the subprocess timezone and locale, so both are
/// pinned for a durable identity. Formatted `ps:<lstart>` - the exact
/// value the TS product records on macOS and BSD. A pid that `kill(0)`
/// reports gone answers `None` without spawning `ps`.
fn ps_process_start_id(pid: u32) -> Option<String> {
    if matches!(pid_exists(pid), Ok(false)) {
        return None;
    }
    let output = std::process::Command::new(PS)
        .args(["-p", &pid.to_string(), "-o", "lstart="])
        .env("LC_ALL", "C")
        .env("LC_TIME", "C")
        .env("LANG", "C")
        .env("TZ", "UTC")
        .output()
        .ok()?;
    let start_time = String::from_utf8_lossy(&output.stdout).trim().to_string();
    (!start_time.is_empty()).then(|| format!("ps:{start_time}"))
}

/// The executable a live pid currently runs (best-effort, like the liveness
/// probes: `None` when the platform cannot answer). Names the process
/// holding a runtime session lease in the session-hold refusal - the TS and
/// Rust products share the session store, so the holder of a refused file is
/// whichever product owns it. An unresolvable holder stays anonymous, never
/// a guess: the refusal's flavor claim (TypeScript vs Rust) is made only
/// from a resolved path.
#[cfg(target_os = "linux")]
#[must_use]
pub fn process_executable_path(pid: u32) -> Option<std::path::PathBuf> {
    if pid == 0 {
        return None;
    }
    std::fs::read_link(format!("/proc/{pid}/exe")).ok()
}

/// macOS: `proc_pidpath` (libproc). A process the caller may not inspect
/// fails and stays `None` - the same best-effort contract as the Linux
/// `/proc` read.
#[cfg(target_vendor = "apple")]
#[must_use]
pub fn process_executable_path(pid: u32) -> Option<std::path::PathBuf> {
    if pid == 0 {
        return None;
    }
    let pid = libc::pid_t::try_from(pid).ok()?;
    libproc::proc_pid::pidpath(pid)
        .ok()
        .map(std::path::PathBuf::from)
}

// Suspend-to-background signal control (TS `handleCtrlZ`): the
// interactive TUI stops its whole process group with SIGTSTP when the
// user suspends it, with SIGINT ignored for the stopped window (a
// Ctrl+C at the shell prompt must not kill the backgrounded process)
// and restored on the SIGCONT resume. Lives here because eukhe-tui
// depends on eukhe-types alone (the platform wall).

/// Stop the caller's whole process group with SIGTSTP (TS
/// `process.kill(0, "SIGTSTP")`): with the default disposition every
/// process in the group stops, and execution continues after SIGCONT.
/// Errors when the signal could not be delivered.
///
/// The group signal alone does not stop the CALLING thread before
/// `kill` returns: the kernel hands a process-directed stop to any one
/// thread, and in a multi-threaded process the caller can run on (into
/// the resume path, re-arming raw mode on the shell's terminal) until the
/// group stop reaches it. So the caller blocks SIGTSTP around the group
/// signal, queues a thread-directed SIGTSTP on itself, and unblocks: the
/// unblock cannot return before this thread stops (it either joins the
/// group stop already in progress or starts it with its own signal).
/// SIGCONT discards every stop signal still pending, so the process
/// stops once.
///
/// # Errors
///
/// Returns an error when delivering `SIGTSTP` to the process group or to
/// the calling thread fails, or when the thread's signal mask cannot be
/// changed; the error carries the OS error.
pub fn stop_own_process_group() -> anyhow::Result<()> {
    use nix::sys::pthread::{pthread_kill, pthread_self};
    use nix::sys::signal::{kill, pthread_sigmask, SigSet, SigmaskHow, Signal};
    use nix::unistd::Pid;

    let mut tstp = SigSet::empty();
    tstp.add(Signal::SIGTSTP);
    let mut previous = SigSet::empty();
    // A thread-mask change on the calling thread; `previous` receives the
    // mask restored below.
    if let Err(errno) = pthread_sigmask(SigmaskHow::SIG_BLOCK, Some(&tstp), Some(&mut previous)) {
        anyhow::bail!("blocking SIGTSTP failed: {}", std::io::Error::from(errno));
    }
    // Delivers SIGTSTP to the caller's own process group; the default
    // disposition stops it, exactly like the terminal's own Ctrl+Z (ISIG)
    // would. On success, queues SIGTSTP on the calling thread itself; it
    // stays pending until the unblock below.
    let delivered = match kill(Pid::from_raw(0), Signal::SIGTSTP) {
        Err(errno) => Err(anyhow::anyhow!(
            "stopping the process group failed: {}",
            std::io::Error::from(errno)
        )),
        Ok(()) => pthread_kill(pthread_self(), Signal::SIGTSTP).map_err(|errno| {
            anyhow::anyhow!(
                "stopping the calling thread failed: {}",
                std::io::Error::from(errno)
            )
        }),
    };
    // Restores the caller's previous thread mask; a queued stop lands
    // before this call returns.
    let restore = pthread_sigmask(SigmaskHow::SIG_SETMASK, Some(&previous), None);
    delivered?;
    if let Err(errno) = restore {
        anyhow::bail!(
            "restoring the signal mask failed: {}",
            std::io::Error::from(errno)
        );
    }
    Ok(())
}

/// The suspended window's SIGINT shield: `true` while SIGINT must be
/// swallowed. The handler behind it is installed once (on the first
/// suspend) and stays for the process lifetime; with the shield down it
/// runs SIGINT's default action (terminate), so outside the window the
/// process ends on SIGINT exactly as under `SIG_DFL`.
static SIGINT_SHIELD: std::sync::Mutex<Option<std::sync::Arc<std::sync::atomic::AtomicBool>>> =
    std::sync::Mutex::new(None);

/// Ignore SIGINT for the suspended window (TS installs a no-op `SIGINT`
/// listener for the same reason: Ctrl+C at the shell must not kill the
/// backgrounded process). A real handler, not `SIG_IGN`: the kernel
/// queues signals sent to a *stopped* process and evaluates the
/// disposition at delivery - an ignored-at-generation signal still pends,
/// and it would then arrive after the resume restored the default
/// disposition and kill the process. The handler runs (and swallows) at
/// that delivery instead. Errors when the handler could not be
/// installed.
///
/// # Errors
///
/// Returns an error when installing the `SIGINT` handler fails; the error
/// carries the OS error.
pub fn ignore_sigint_for_suspend() -> anyhow::Result<()> {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, PoisonError};
    let mut shield = SIGINT_SHIELD.lock().unwrap_or_else(PoisonError::into_inner);
    if let Some(default_action) = shield.as_ref() {
        default_action.store(false, Ordering::SeqCst);
        return Ok(());
    }
    // `false`: the handler swallows SIGINT; `true`: it runs the default
    // action.
    let default_action = Arc::new(AtomicBool::new(false));
    signal_hook::flag::register_conditional_default(
        signal_hook::consts::SIGINT,
        Arc::clone(&default_action),
    )
    .map_err(|error| anyhow::anyhow!("ignoring SIGINT for suspend failed: {error}"))?;
    *shield = Some(default_action);
    Ok(())
}

/// Restore SIGINT's default behavior on the SIGCONT resume (TS removes
/// its no-op listener before restarting the TUI): the shield's handler
/// runs SIGINT's default action again. Never fails (the handler stays
/// installed; only its mode flips).
///
/// The mode flips only once no SIGINT raised inside the window still
/// waits in this process's shared signal queue. A cooked-mode editor
/// wrapper's Ctrl+C (`kill -INT 0`) is process-directed: the kernel
/// parks it in that queue and wakes one thread, which dequeues it when
/// it next runs -- under load, after the editor exited and the resume
/// reached this restore, so a flip first would hand a signal the window
/// owed a swallow to the default action and kill the TUI after the edit
/// landed. The queue is `ShdPnd` in `/proc/self/status`; the wait is
/// bounded, so a thread that blocks SIGINT for good never wedges the
/// resume. Node has no such race: a signal libuv consumed before the
/// listener went dies with the listener.
///
/// # Errors
///
/// None in practice; the `Result` keeps the suspend driver's contract.
pub fn restore_default_sigint() -> anyhow::Result<()> {
    use std::sync::atomic::Ordering;
    use std::sync::PoisonError;
    let shield = SIGINT_SHIELD.lock().unwrap_or_else(PoisonError::into_inner);
    if let Some(default_action) = shield.as_ref() {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        while shared_sigint_pending() && std::time::Instant::now() < deadline {
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        default_action.store(true, Ordering::SeqCst);
    }
    Ok(())
}

/// Whether a process-directed SIGINT waits in this process's shared
/// signal queue (`ShdPnd` in `/proc/self/status`). `false` where the
/// file is unavailable: nothing to wait for.
#[cfg(target_os = "linux")]
fn shared_sigint_pending() -> bool {
    std::fs::read_to_string("/proc/self/status")
        .is_ok_and(|status| shared_sigint_in_status(&status))
}

#[cfg(not(target_os = "linux"))]
fn shared_sigint_pending() -> bool {
    false
}

/// Whether the `ShdPnd` mask of a `/proc/<pid>/status` text has SIGINT's
/// bit (signal `n` is bit `n - 1`).
fn shared_sigint_in_status(status: &str) -> bool {
    status
        .lines()
        .find_map(|line| line.strip_prefix("ShdPnd:"))
        .and_then(|mask| u64::from_str_radix(mask.trim(), 16).ok())
        .is_some_and(|mask| mask & (1 << (nix::sys::signal::Signal::SIGINT as i32 - 1)) != 0)
}

/// TS `processIdExists`: `kill(pid, 0)` checks existence only. ESRCH and a
/// pid beyond `pid_t`'s range (which must not wrap into kill's negative
/// "every process" argument) do not exist; EPERM does - the pid is just
/// not ours to signal.
fn pid_exists(pid: u32) -> std::io::Result<bool> {
    use nix::errno::Errno;
    let Ok(pid) = libc::pid_t::try_from(pid) else {
        return Ok(false);
    };
    // Signal 0 delivers nothing; it only checks the pid.
    match nix::sys::signal::kill(nix::unistd::Pid::from_raw(pid), None) {
        Ok(()) | Err(Errno::EPERM) => Ok(true),
        Err(Errno::ESRCH) => Ok(false),
        Err(errno) => Err(errno.into()),
    }
}

/// True only for a process that is actually running: zombies do not count
/// (TS `isProcessAlive`). Errors when the platform cannot answer.
///
/// `/proc` is authoritative where it is mounted (Linux); platforms without
/// it (macOS/BSD) previously read every live process as dead here, so lease
/// staleness judged a live owner reclaimable. The fallback restores the TS
/// semantics: the `kill(pid, 0)` existence probe (EPERM counts as alive -
/// the pid exists but is not ours to signal) plus the zombie demotion
/// (`ps -o stat=`).
///
/// # Errors
///
/// Returns an error when the `kill(pid, 0)` probe fails with an error
/// other than `ESRCH` (dead) or `EPERM` (alive), or when the zombie
/// demotion cannot run.
pub fn is_process_alive(pid: u32) -> anyhow::Result<bool> {
    if pid == 0 {
        return Ok(false);
    }
    if std::path::Path::new(&format!("/proc/{pid}")).exists() {
        // A zombie still owns /proc; treat it as dead for lease purposes.
        if let Ok(status) = std::fs::read_to_string(format!("/proc/{pid}/status")) {
            if let Some(state) = status.lines().find_map(|l| l.strip_prefix("State:")) {
                return Ok(!state.trim_start().starts_with('Z'));
            }
        }
        return Ok(true);
    }
    // No /proc entry: either the platform has no /proc or the pid is gone.
    if !pid_exists(pid)
        .map_err(|error| anyhow::anyhow!("kill(0) liveness probe failed: {error}"))?
    {
        return Ok(false);
    }
    // The pid resolves: demote zombies (TS `isZombieProcess`) - there is
    // no /proc state line to read here.
    let output = std::process::Command::new(PS)
        .args(["-p", &pid.to_string(), "-o", "stat="])
        .output()?;
    let zombie = String::from_utf8_lossy(&output.stdout)
        .trim_start()
        .starts_with('Z');
    Ok(!zombie)
}

/// A process named by its pid and, where the platform exposes one, its
/// start identity ([`process_start_id`]). Session leases and cron dispatch
/// claims record their owner with it, so a recycled pid never passes for
/// the owner.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProcessIdentity {
    pub pid: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub process_start_id: Option<String>,
}

impl ProcessIdentity {
    /// The identity of the calling process.
    #[must_use]
    pub fn current() -> Self {
        let pid = std::process::id();
        Self {
            pid,
            process_start_id: process_start_id(pid),
        }
    }

    /// Whether this process still runs: its pid is alive and, when a start
    /// identity was recorded, the pid still has that identity. A provably
    /// dead pid or a changed identity is dead. A liveness probe that cannot
    /// answer, or an identity the platform does not show, counts as alive:
    /// to take over the claim of a live owner is worse than to wait.
    #[must_use]
    pub fn is_alive(&self) -> bool {
        match is_process_alive(self.pid) {
            Ok(true) | Err(_) => {}
            Ok(false) => return false,
        }
        match self.process_start_id.as_deref() {
            None => true,
            Some(expected) => process_start_id(self.pid).is_none_or(|current| current == expected),
        }
    }
}

/// Liveness answers on every unix, /proc or not: the probe families are
/// both reachable on Linux (a pid without a /proc entry takes the
/// kill(0) fallback), so the fallback is testable without /proc.
#[cfg(test)]
mod liveness_tests {
    use super::*;

    /// This very process reads alive wherever the probe lands: /proc's
    /// state line on Linux, kill(0) + the process record where /proc is
    /// not mounted.
    #[test]
    fn a_live_process_reads_alive() {
        assert!(is_process_alive(std::process::id()).expect("liveness probe"));
    }

    /// A pid beyond `pid_t`'s range cannot name a process - and must not
    /// wrap into kill's negative "every process" argument.
    #[test]
    fn a_pid_beyond_the_pidt_range_is_dead() {
        assert!(!is_process_alive(u32::MAX).expect("liveness probe"));
    }

    /// A pid that cannot exist has no /proc entry even on Linux, so it
    /// exercises the kill(0) fallback on both probe families and reads
    /// dead.
    #[test]
    fn a_nonexistent_pid_reads_dead_through_the_fallback() {
        assert!(!is_process_alive(100_000_000).expect("liveness probe"));
    }

    /// A dead pid answers `None` without spawning `ps`: the parent re-runs
    /// this test with a `PATH` whose only `ps` is a fake that would turn
    /// any spawn into `Some("ps:...")`.
    #[test]
    fn a_dead_pid_has_no_identity_and_spawns_no_ps() {
        use std::os::unix::fs::PermissionsExt;
        const CHILD: &str = "EUKHE_TYPES_DEAD_PID_PS_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let dir = tempfile::tempdir().expect("temp dir");
            let fake_ps = dir.path().join("ps");
            std::fs::write(&fake_ps, "#!/bin/sh\necho 'Thu Jan  1 00:00:00 1970'\n")
                .expect("write the fake ps");
            std::fs::set_permissions(&fake_ps, std::fs::Permissions::from_mode(0o755))
                .expect("make the fake ps executable");
            let output = std::process::Command::new(std::env::current_exe().expect("test binary"))
                .args([
                    "--exact",
                    "platform::process::liveness_tests::a_dead_pid_has_no_identity_and_spawns_no_ps",
                ])
                .env(CHILD, "1")
                .env("PATH", dir.path())
                .output()
                .expect("re-run with only the fake ps on PATH");
            assert!(
                output.status.success(),
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        // A spawned `ps` resolves to the fake and would answer `Some("ps:...")`.
        assert!(!std::process::Command::new("ps")
            .output()
            .unwrap()
            .stdout
            .is_empty());
        assert_eq!(process_start_id(100_000_000), None);
        assert!(process_start_id(std::process::id()).is_some());
    }
}

/// The `/bin/ps` probes vs `ps` itself: the identity and zombie state
/// must match byte-for-byte with `ps` unresolvable on `PATH` (the test
/// re-execs itself without one).
#[cfg(all(test, target_vendor = "apple"))]
mod darwin_ps_probe_tests {
    use super::*;
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};

    /// The identity earlier builds and the TS product recorded: `ps -o
    /// lstart=` under the pinned env - the test-side ground truth.
    /// `/bin/ps` by absolute path, so it still runs when the test hides
    /// `ps` from `PATH`.
    fn ps_lstart_identity(pid: u32) -> Option<String> {
        let output = Command::new("/bin/ps")
            .args(["-p", &pid.to_string(), "-o", "lstart="])
            .env("LC_ALL", "C")
            .env("LC_TIME", "C")
            .env("LANG", "C")
            .env("TZ", "UTC")
            .output()
            .ok()?;
        let lstart = String::from_utf8_lossy(&output.stdout).trim().to_string();
        (!lstart.is_empty()).then(|| format!("ps:{lstart}"))
    }

    /// `ps -o stat=` by absolute path: the ground truth for the zombie
    /// state.
    fn ps_reports_zombie(pid: u32) -> bool {
        Command::new("/bin/ps")
            .args(["-p", &pid.to_string(), "-o", "stat="])
            .output()
            .is_ok_and(|output| {
                String::from_utf8_lossy(&output.stdout)
                    .trim_start()
                    .starts_with('Z')
            })
    }

    #[test]
    fn identity_and_zombie_state_match_ps_with_no_ps_on_path() {
        const CHILD: &str = "EUKHE_TYPES_PS_PROBE_CHILD";
        if std::env::var_os(CHILD).is_none() {
            // Re-run this very test where `ps` does not resolve: a probe
            // that spawns `ps` from `PATH` answers None/Err there.
            let output = Command::new(std::env::current_exe().expect("test binary"))
                .args([
                    "--exact",
                    "platform::process::darwin_ps_probe_tests::identity_and_zombie_state_match_ps_with_no_ps_on_path",
                ])
                .env(CHILD, "1")
                .env("PATH", "/var/empty")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        // Detached stdio: a sleep leaked by an assert failure cannot hold
        // the parent's output pipes open.
        let mut child = Command::new("/bin/sleep")
            .arg("600")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap();
        let pid = child.id();
        // pid 1 is root-owned launchd: readable without privilege, like ps.
        let live = [pid, 1];
        assert_eq!(live.map(process_start_id), live.map(ps_lstart_identity));
        assert!(is_process_alive(pid).unwrap());
        child.kill().unwrap();
        // Wait until the child has exited, but leave it unreaped (a zombie).
        let deadline = Instant::now() + Duration::from_secs(10);
        while !ps_reports_zombie(pid) {
            assert!(
                Instant::now() < deadline,
                "the killed child never turned zombie"
            );
            std::thread::sleep(Duration::from_millis(10));
        }
        assert_eq!(process_start_id(pid), ps_lstart_identity(pid));
        assert!(!is_process_alive(pid).unwrap());
        child.wait().unwrap();
        assert_eq!(
            (process_start_id(pid), ps_lstart_identity(pid)),
            (None, None)
        );
    }
}

/// The suspended window's SIGINT shield: a caught handler while
/// suspended (the kernel evaluates the disposition at delivery, so a
/// shield must be a handler, not `SIG_IGN`) that swallows SIGINT, and the
/// resume restores SIGINT's default action. Runs in a re-exec'd child,
/// whose death by the restored default action is the proof.
#[cfg(test)]
mod suspend_shield_tests {
    use super::*;
    use nix::sys::signal::{raise, Signal};
    use std::os::unix::process::ExitStatusExt;

    #[test]
    fn shield_swallows_sigint_and_restore_returns_the_default_action() {
        const CHILD: &str = "EUKHE_TYPES_SIGINT_SHIELD_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(
                std::env::current_exe().expect("test binary"),
            )
            .args([
                "--exact",
                "platform::process::suspend_shield_tests::shield_swallows_sigint_and_restore_returns_the_default_action",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .expect("re-run the shield test in a child");
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                stdout.contains("shield held"),
                "the shield swallowed SIGINT twice before the restore:\n{stdout}{stderr}"
            );
            assert_eq!(
                output.status.signal(),
                Some(libc::SIGINT),
                "the restored default action terminates on SIGINT:\n{stdout}{stderr}"
            );
            return;
        }
        ignore_sigint_for_suspend().expect("shield");
        raise(Signal::SIGINT).expect("raise SIGINT under the shield");
        // A second suspend window re-arms the same handler.
        restore_default_sigint().expect("restore");
        ignore_sigint_for_suspend().expect("re-arm the shield");
        raise(Signal::SIGINT).expect("raise SIGINT under the re-armed shield");
        println!("shield held");
        restore_default_sigint().expect("restore");
        raise(Signal::SIGINT).expect("raise SIGINT after the restore");
        std::thread::sleep(std::time::Duration::from_secs(5));
        panic!("SIGINT did not terminate the process after the restore");
    }

    /// The shield's drain reads the process-wide queue: SIGINT's bit in
    /// `ShdPnd`, never the per-thread `SigPnd` or another signal's bit.
    #[test]
    fn the_shared_queue_read_takes_sigints_bit_of_shdpnd() {
        let status = |shd: &str, sig: &str| {
            format!("Name:\tx\nSigPnd:\t{sig}\nShdPnd:\t{shd}\nSigBlk:\t0000000000000000\n")
        };
        assert!(shared_sigint_in_status(&status(
            "0000000000000002",
            "0000000000000000"
        )));
        assert!(shared_sigint_in_status(&status(
            "0000000000010002",
            "0000000000000000"
        )));
        assert!(!shared_sigint_in_status(&status(
            "0000000000000000",
            "0000000000000002"
        )));
        assert!(!shared_sigint_in_status(&status(
            "0000000000010000",
            "0000000000000000"
        )));
        assert!(!shared_sigint_in_status("Name:\tx\n"));
    }
}

/// The executable-path probe: the own pid resolves to the running binary,
/// and pid 0 (the no-process sentinel) never does. `PATH_MAX`-sized paths
/// and unresolvable pids answer `None` on the live path, so this pins the
/// one contract callers rely on - a resolved path names a live process's
/// image, never a guess.
#[cfg(test)]
mod executable_path_tests {
    use super::*;

    #[test]
    fn own_pid_resolves_and_zero_does_not() {
        let resolved = process_executable_path(std::process::id())
            .expect("the own pid's executable must resolve");
        let current = std::env::current_exe().expect("current_exe");
        let resolved_name = resolved
            .file_name()
            .map(|name| name.to_string_lossy().to_string())
            .unwrap_or_default();
        let current_name = current
            .file_name()
            .map(|name| name.to_string_lossy().to_string())
            .unwrap_or_default();
        assert_eq!(
            resolved_name, current_name,
            "the own pid must resolve to the running executable ({resolved:?} vs {current:?})"
        );
        assert_eq!(process_executable_path(0), None);
    }
}
