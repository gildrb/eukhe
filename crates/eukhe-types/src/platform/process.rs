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
/// `getPsProcessStartId`) - rendered in-process from the kernel process
/// record on macOS, by running `ps -o lstart=` on other unixes when the
/// pid still exists. A recycled pid has a different start time, so a
/// recorded identity that still matches proves the pid still names the
/// same process. `None` only when the platform exposes neither - owners
/// then trust liveness checks alone, exactly like TS records with
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

/// The `ps -p <pid> -o lstart=` fallback (TS `getPsProcessStartId`): `lstart`
/// renders in the subprocess timezone and locale, so both are pinned for a
/// durable identity. Formatted `ps:<lstart>` - the exact value the TS
/// product records on macOS and BSD. A pid that `kill(0)` reports gone
/// answers `None` without spawning `ps`.
#[cfg(not(target_vendor = "apple"))]
fn ps_process_start_id(pid: u32) -> Option<String> {
    if matches!(pid_exists(pid), Ok(false)) {
        return None;
    }
    let output = std::process::Command::new("ps")
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

/// macOS: the `ps:<lstart>` identity (TS `getPsProcessStartId`) rendered
/// in-process, byte-identical to `ps -p <pid> -o lstart=` under the pinned
/// `LC_ALL=C TZ=UTC` env: the same kernel record and field `ps` reads
/// (`kp_proc.p_starttime.tv_sec`), formatted with ps's own `strftime("%c")`
/// (with `gmtime_r` for `localtime` under `TZ=UTC`, and the null locale as
/// the C locale per xlocale(3)). The value is persisted by earlier builds
/// and the TS product, so any drift would read as a recycled pid.
#[cfg(target_vendor = "apple")]
fn ps_process_start_id(pid: u32) -> Option<String> {
    let start = darwin::kinfo_proc(pid).ok().flatten()?.p_starttime.tv_sec;
    // SAFETY: all-zero is a valid `tm` (integers and a null zone pointer).
    let mut civil: libc::tm = unsafe { std::mem::zeroed() };
    // SAFETY: writes only `civil`; null means `start` is out of range.
    if unsafe { libc::gmtime_r(&raw const start, &raw mut civil) }.is_null() {
        return None;
    }
    let mut buffer = [0u8; 64];
    // SAFETY: writes at most `buffer.len()` bytes (NUL-terminated) and
    // returns the length without the NUL, 0 when it does not fit.
    let written = unsafe {
        libc::strftime_l(
            buffer.as_mut_ptr().cast(),
            buffer.len(),
            c"%c".as_ptr(),
            &raw const civil,
            std::ptr::null_mut(),
        )
    };
    let lstart = String::from_utf8_lossy(&buffer[..written]);
    (written > 0).then(|| format!("ps:{lstart}"))
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
/// answers 0 and stays `None` - the same best-effort contract as the Linux
/// `/proc` read.
#[cfg(target_vendor = "apple")]
#[must_use]
pub fn process_executable_path(pid: u32) -> Option<std::path::PathBuf> {
    if pid == 0 {
        return None;
    }
    // `proc_pidpath`'s documented buffer contract is
    // `PROC_PIDPATHINFO_MAXSIZE` (4 * MAXPATHLEN); Apple's samples use it
    // and every XNU version accepts it, so the probe stays inside the
    // documented shape instead of the implementation's bare minimum.
    let mut buffer = [0u8; 4 * libc::PATH_MAX as usize];
    // A `PATH_MAX`-scaled constant length always fits proc_pidpath's u32
    // size parameter.
    #[allow(clippy::cast_possible_truncation)]
    let buffer_len = buffer.len() as u32;
    // SAFETY: writes the pid's executable path into `buffer` (at most its
    // size, NUL-terminated) and returns the byte count; 0 means the path
    // was not resolvable.
    let written =
        unsafe { libc::proc_pidpath(pid as libc::pid_t, buffer.as_mut_ptr().cast(), buffer_len) };
    if written <= 0 {
        return None;
    }
    // Positive by the check above, so widening to usize loses no sign.
    #[allow(clippy::cast_sign_loss)]
    let written = (written as usize).min(buffer.len());
    let end = buffer[..written]
        .iter()
        .position(|&byte| byte == 0)
        .unwrap_or(written);
    Some(std::path::PathBuf::from(
        String::from_utf8_lossy(&buffer[..end]).into_owned(),
    ))
}

// Suspend-to-background signal control (TS `handleCtrlZ`): the
// interactive TUI stops its whole process group with SIGTSTP when the
// user suspends it, with SIGINT ignored for the stopped window (a
// Ctrl+C at the shell prompt must not kill the backgrounded process)
// and restored on the SIGCONT resume. Lives here because eukhe-tui
// depends on eukhe-types alone (the platform wall; eukhe-tui opts into the
// workspace `unsafe_code` forbid).

/// Stop the caller's whole process group with SIGTSTP (TS
/// `process.kill(0, "SIGTSTP")`): with the default disposition every
/// process in the group stops, and execution continues after SIGCONT.
/// Errors when the signal could not be delivered.
///
/// # Errors
///
/// Returns an error when delivering `SIGTSTP` to the process group fails;
/// the error carries the last OS error.
pub fn stop_own_process_group() -> anyhow::Result<()> {
    // SAFETY: delivers SIGTSTP to the caller's own process group; the
    // default disposition stops it, exactly like the terminal's own
    // Ctrl+Z (ISIG) would.
    if unsafe { libc::kill(0, libc::SIGTSTP) } != 0 {
        anyhow::bail!(
            "stopping the process group failed: {}",
            std::io::Error::last_os_error()
        );
    }
    Ok(())
}

/// The no-op SIGINT handler for the suspended window (TS's
/// `process.on("SIGINT", noop)`): a real handler, not `SIG_IGN`, because
/// the kernel queues signals sent to a *stopped* process and evaluates
/// the disposition at delivery — an ignored-at-generation signal still
/// pends, and it would then arrive after this cycle restored the default
/// disposition and kill the process. A handler runs (and does nothing)
/// at that delivery instead.
extern "C" fn swallow_sigint(_signal: libc::c_int) {}

/// Ignore SIGINT for the suspended window (TS installs a no-op `SIGINT`
/// listener for the same reason: Ctrl+C at the shell must not kill the
/// backgrounded process). Errors when the disposition could not be set.
///
/// # Errors
///
/// Returns an error when setting the no-op `SIGINT` handler fails; the
/// error carries the last OS error.
pub fn ignore_sigint_for_suspend() -> anyhow::Result<()> {
    // SAFETY: swaps only the SIGINT disposition to the no-op handler.
    // The fn-item cast goes through the fn-pointer type so no
    // fn-item-to-integer warning fires under `-D warnings`.
    let handler: extern "C" fn(libc::c_int) = swallow_sigint;
    if unsafe { libc::signal(libc::SIGINT, handler as libc::sighandler_t) } == libc::SIG_ERR {
        anyhow::bail!(
            "ignoring SIGINT for suspend failed: {}",
            std::io::Error::last_os_error()
        );
    }
    Ok(())
}

/// Restore SIGINT's default disposition on the SIGCONT resume (TS removes
/// its no-op listener before restarting the TUI). Errors when the
/// disposition could not be set.
///
/// # Errors
///
/// Returns an error when restoring the default `SIGINT` disposition
/// fails; the error carries the last OS error.
pub fn restore_default_sigint() -> anyhow::Result<()> {
    // SAFETY: swaps only the SIGINT disposition back to SIG_DFL.
    if unsafe { libc::signal(libc::SIGINT, libc::SIG_DFL) } == libc::SIG_ERR {
        anyhow::bail!(
            "restoring the default SIGINT after suspend failed: {}",
            std::io::Error::last_os_error()
        );
    }
    Ok(())
}

/// TS `processIdExists`: `kill(pid, 0)` checks existence only. ESRCH and a
/// pid beyond `pid_t`'s range (which must not wrap into kill's negative
/// "every process" argument) do not exist; EPERM does - the pid is just
/// not ours to signal.
fn pid_exists(pid: u32) -> std::io::Result<bool> {
    let Ok(pid) = libc::pid_t::try_from(pid) else {
        return Ok(false);
    };
    // SAFETY: signal 0 delivers nothing; it only checks the pid.
    if unsafe { libc::kill(pid, 0) } == 0 {
        return Ok(true);
    }
    let error = std::io::Error::last_os_error();
    match error.raw_os_error() {
        Some(libc::ESRCH) => Ok(false),
        Some(libc::EPERM) => Ok(true),
        _ => Err(error),
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
/// (macOS: the kernel process record; other unixes: `ps`).
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
    #[cfg(target_vendor = "apple")]
    let zombie = darwin::kinfo_proc(pid)?.is_some_and(|info| u32::from(info.p_stat) == libc::SZOMB);
    #[cfg(not(target_vendor = "apple"))]
    let zombie = {
        let output = std::process::Command::new("ps")
            .args(["-p", &pid.to_string(), "-o", "stat="])
            .output()?;
        String::from_utf8_lossy(&output.stdout)
            .trim_start()
            .starts_with('Z')
    };
    Ok(!zombie)
}

/// XNU's process record (`struct kinfo_proc`, <sys/sysctl.h>), which the
/// libc crate does not bind: the leading `kp_proc` (`struct extern_proc`,
/// <sys/proc.h>) fields the probes read, padded to the full record. 648
/// bytes with `p_stat` at offset 36 on both 64-bit Darwin ABIs (`arm64`,
/// `x86_64`) - pinned at compile time below.
#[cfg(target_vendor = "apple")]
mod darwin {
    #[repr(C)]
    pub(super) struct KinfoProc {
        /// `kp_proc.p_starttime` (the `p_un` union's timeval arm): the
        /// start time `ps -o lstart` renders.
        pub(super) p_starttime: libc::timeval,
        _p_vmspace: *mut libc::c_void,
        _p_sigacts: *mut libc::c_void,
        _p_flag: libc::c_int,
        /// `kp_proc.p_stat`: `SZOMB` for an unreaped zombie.
        pub(super) p_stat: u8,
        _rest: [u8; 611],
    }

    const _: () = assert!(
        std::mem::size_of::<KinfoProc>() == 648 && std::mem::offset_of!(KinfoProc, p_stat) == 36
    );

    /// `sysctl(CTL_KERN, KERN_PROC, KERN_PROC_PID, pid)`: the record
    /// `ps -p <pid>` itself reads. Needs no privilege and answers zombies
    /// too; `Ok(None)` when no process has the pid.
    ///
    /// Not `proc_pidinfo(PROC_PIDTBSDINFO)`: it fails `EPERM` for
    /// other-uid (root-owned) pids, where `ps`/sysctl answer - turning
    /// `Some` identities into lease staleness's owner-alive `None`.
    pub(super) fn kinfo_proc(pid: u32) -> std::io::Result<Option<KinfoProc>> {
        let Ok(pid) = libc::pid_t::try_from(pid) else {
            return Ok(None);
        };
        let mut name = [libc::CTL_KERN, libc::KERN_PROC, libc::KERN_PROC_PID, pid];
        // SAFETY: all-zero is valid for integers, bytes, and null pointers.
        let mut info: KinfoProc = unsafe { std::mem::zeroed() };
        let mut length = std::mem::size_of::<KinfoProc>();
        // SAFETY: the kernel writes at most `length` bytes into `info` and
        // stores the written size back; no new value is set.
        let status = unsafe {
            libc::sysctl(
                name.as_mut_ptr(),
                4,
                (&raw mut info).cast(),
                &raw mut length,
                std::ptr::null_mut(),
                0,
            )
        };
        if status != 0 {
            return Err(std::io::Error::last_os_error());
        }
        Ok((length != 0).then_some(info))
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

/// The Apple process record vs the `ps` ground truth it replaces: the
/// identity and zombie state must match byte-for-byte, with `ps`
/// unresolvable on `PATH` (the test re-execs itself without one).
#[cfg(all(test, target_vendor = "apple"))]
mod darwin_process_record_tests {
    use super::*;
    use std::process::{Command, Stdio};

    /// The identity earlier builds and the TS product recorded: `ps -o
    /// lstart=` under the pinned env - the removed production path, kept
    /// as test-side ground truth. `/bin/ps` by absolute path, so it still
    /// runs when the test hides `ps` from `PATH`.
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

    #[test]
    fn identity_and_zombie_state_match_ps_with_no_ps_on_path() {
        const CHILD: &str = "EUKHE_TYPES_PROCESS_RECORD_CHILD";
        if std::env::var_os(CHILD).is_none() {
            // Re-run this very test where `ps` does not resolve: a probe
            // that spawns `ps` answers None/Err there.
            let output = Command::new(std::env::current_exe().expect("test binary"))
                .args([
                    "--exact",
                    "platform::process::darwin_process_record_tests::identity_and_zombie_state_match_ps_with_no_ps_on_path",
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
        // Block until the child has exited, but leave it unreaped (a zombie).
        // SAFETY: all-zero is valid for `siginfo_t` (integers and pointers).
        let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
        // SAFETY: writes only `info`; blocks until the child exits without
        // reaping it (WNOWAIT).
        assert_eq!(
            unsafe {
                libc::waitid(
                    libc::P_PID,
                    pid,
                    &raw mut info,
                    libc::WEXITED | libc::WNOWAIT,
                )
            },
            0
        );
        assert_eq!(process_start_id(pid), ps_lstart_identity(pid));
        assert!(!is_process_alive(pid).unwrap());
        child.wait().unwrap();
        assert_eq!(
            (process_start_id(pid), ps_lstart_identity(pid)),
            (None, None)
        );
    }
}

/// The suspended window's SIGINT shield: the dispositions are really
/// installed (a caught handler while suspended — the kernel evaluates
/// the disposition at delivery, so a shield must be a handler, not
/// `SIG_IGN` — and the default restored on resume).
#[cfg(test)]
mod suspend_shield_tests {
    use super::*;

    /// SIGINT's current disposition: default, ignored, or a caught
    /// handler. Queried through `sigaction` itself (not /proc's signal
    /// mask lines — the sandbox kernel does not surface those).
    fn sigint_disposition() -> &'static str {
        let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
        // SAFETY: queries SIGINT's disposition into `action`.
        unsafe { libc::sigaction(libc::SIGINT, std::ptr::null(), &raw mut action) };
        let handler = action.sa_sigaction;
        if handler == libc::SIG_DFL {
            "default"
        } else if handler == libc::SIG_IGN {
            "ignored"
        } else {
            "caught"
        }
    }

    #[test]
    fn shield_installs_a_handler_and_restore_returns_the_default() {
        // Some other lib test leaves SIGINT ignored, so the starting
        // disposition is recorded (and restored) rather than assumed.
        let before = sigint_disposition();
        ignore_sigint_for_suspend().expect("shield");
        assert_eq!(
            sigint_disposition(),
            "caught",
            "the shield is a caught handler (a queued signal delivered to a stopped process is evaluated at delivery — SIG_IGN would let a pending SIGINT kill the process after the resume restored the default)"
        );
        restore_default_sigint().expect("restore");
        assert_eq!(
            sigint_disposition(),
            "default",
            "the resume restored the default disposition"
        );
        // SAFETY: restores the disposition this test started with.
        unsafe {
            libc::signal(
                libc::SIGINT,
                if before == "ignored" {
                    libc::SIG_IGN
                } else {
                    libc::SIG_DFL
                },
            );
        }
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
