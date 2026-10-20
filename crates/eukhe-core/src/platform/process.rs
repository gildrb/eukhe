//! Process control: signals, process groups, detached spawns.
//!
//! nix `kill`/`killpg` / `process_group(0)`. Signatures that report
//! outcomes return `bool` where callers treat "unproven" conservatively (a
//! kill that could not be proven reports false, matching the TS
//! `killOrphanProcess` contract).

use std::os::fd::OwnedFd;
use std::process::Command;

use nix::sys::signal::{kill, killpg};
use nix::unistd::Pid;

/// Termination signal for [`kill_pid`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Signal {
    /// Graceful stop (SIGTERM).
    Term,
    /// Forcible stop (SIGKILL).
    Kill,
}

impl Signal {
    fn nix(self) -> nix::sys::signal::Signal {
        match self {
            Signal::Term => nix::sys::signal::Signal::SIGTERM,
            Signal::Kill => nix::sys::signal::Signal::SIGKILL,
        }
    }
}

/// Put the spawned child into its own process group so later group-scoped
/// kills reach all of its descendants (TS: `detached: true` on POSIX).
pub fn set_new_process_group(command: &mut Command) {
    use std::os::unix::process::CommandExt;
    command.process_group(0);
}

/// The marker [`request_new_session`] puts in the child's environment;
/// the eukhe binary's startup ([`enter_requested_session`]) consumes it.
pub const NEW_SESSION_ENV: &str = "EUKHE_START_NEW_SESSION";

/// Have the spawned eukhe child start in a new session with no
/// controlling terminal (`setsid`): the child cannot open `/dev/tty`, and
/// job-control signals from the parent's terminal never reach it. A new
/// process group alone is not enough: the group can still open the
/// terminal, and a background read then stops it with SIGTTIN.
///
/// std's only post-fork hook (`pre_exec`) is unsafe, so the child runs
/// `setsid` itself, first thing in `main`: the command must run the eukhe
/// binary.
pub fn request_new_session(command: &mut Command) {
    command.env(NEW_SESSION_ENV, "1");
}

/// The child half of [`request_new_session`]: when the launcher asked for
/// it, leave the inherited session (`setsid`, which also makes this
/// process its own group leader). Call it first thing in `main`, while
/// the process is still single-threaded: the marker is removed from the
/// environment so this process's own children never inherit it.
///
/// # Errors
///
/// The `setsid` failure.
pub fn enter_requested_session() -> std::io::Result<()> {
    if std::env::var_os(NEW_SESSION_ENV).is_none() {
        return Ok(());
    }
    std::env::remove_var(NEW_SESSION_ENV);
    nix::unistd::setsid()
        .map(drop)
        .map_err(std::io::Error::from)
}

/// Raise the soft open-file limit to the hard limit and return the
/// resulting soft limit (Node raises it the same way at startup). macOS
/// refuses a soft limit above `kern.maxfilesperproc`, `RLIM_INFINITY`
/// included, so the target is capped there.
///
/// # Errors
///
/// The OS error of a failed `getrlimit`, `sysctlbyname` or `setrlimit`.
pub fn raise_open_file_limit() -> std::io::Result<u64> {
    use nix::sys::resource::{getrlimit, setrlimit, Resource};
    let (soft, hard) = getrlimit(Resource::RLIMIT_NOFILE)?;
    #[cfg(not(target_os = "macos"))]
    let target = hard;
    #[cfg(target_os = "macos")]
    let target = {
        use sysctl::Sysctl;
        let value = sysctl::Ctl::new("kern.maxfilesperproc")
            .and_then(|ctl| ctl.value())
            .map_err(std::io::Error::other)?;
        let sysctl::CtlValue::Int(per_process) = value else {
            return Err(std::io::Error::other(format!(
                "kern.maxfilesperproc is not an int: {value:?}"
            )));
        };
        hard.min(per_process.unsigned_abs().into())
    };
    if soft < target {
        setrlimit(Resource::RLIMIT_NOFILE, target, hard)?;
        return Ok(target);
    }
    Ok(soft)
}

/// Signal a single pid. Returns true only when the signal was delivered,
/// proving the pid was alive at signal time.
#[must_use]
pub fn kill_pid(pid: i32, signal: Signal) -> bool {
    if pid <= 0 {
        return false;
    }
    kill(Pid::from_raw(pid), signal.nix()).is_ok()
}

/// Signal the process group `pgid` (a group leader's pid). Returns true
/// only when the signal was delivered to at least one member.
#[must_use]
pub fn signal_process_group(pgid: i32, signal: Signal) -> bool {
    if pgid <= 0 {
        return false;
    }
    killpg(Pid::from_raw(pgid), signal.nix()).is_ok()
}

/// The process group `pid` belongs to (`getpgid`), or `None` when the pid
/// is gone or not observable. A process spawned through
/// [`set_new_process_group`] leads its own group: its pgid is its pid.
#[must_use]
pub fn process_group_id(pid: u32) -> Option<i32> {
    let raw = i32::try_from(pid).ok().filter(|raw| *raw > 0)?;
    let group = nix::unistd::getpgid(Some(Pid::from_raw(raw)))
        .ok()?
        .as_raw();
    (group > 0).then_some(group)
}

/// Kill a process and all its children: the process group first (`bash()`
/// children run detached in a new group), then the bare pid as fallback.
/// Returns true when either signal was delivered (TS `killProcessTree`).
#[must_use]
pub fn kill_process_group_or_pid(pid: i32) -> bool {
    if pid <= 0 {
        return false;
    }
    let pid = Pid::from_raw(pid);
    killpg(pid, Signal::Kill.nix()).is_ok() || kill(pid, Signal::Kill.nix()).is_ok()
}

/// Cheap `kill(pid, 0)` existence probe; counts zombies as existing. A pid
/// beyond `pid_t`'s range names no process.
#[must_use]
pub fn pid_exists(pid: u32) -> bool {
    if pid == 0 {
        return false;
    }
    let Ok(raw) = i32::try_from(pid) else {
        return false;
    };
    kill(Pid::from_raw(raw), None).is_ok()
}

/// The kernel-held process handle (`pidfd_open`): pins the exact process
/// behind the pid, so a signal through it ([`pidfd_signal`]) reaches that
/// process even if the numeric pid is recycled afterwards. The caller
/// treats an unobtainable handle as never-signal: a missed stop is
/// recoverable, a wrong one is not. The handle closes on drop.
///
/// # Errors
///
/// Returns the open failure verbatim: `ESRCH` names a process that is
/// already gone, `EINVAL` a pid no process can have, `Unsupported` a
/// platform with no pidfd arm.
#[cfg(target_os = "linux")]
pub fn open_pidfd(pid: u32) -> std::io::Result<OwnedFd> {
    let pid = i32::try_from(pid)
        .ok()
        .and_then(rustix::process::Pid::from_raw)
        .ok_or_else(|| std::io::Error::from(rustix::io::Errno::INVAL))?;
    Ok(rustix::process::pidfd_open(
        pid,
        rustix::process::PidfdFlags::empty(),
    )?)
}

/// macOS has no pidfd: the handle is unobtainable.
///
/// # Errors
///
/// Always `Unsupported`.
#[cfg(target_os = "macos")]
pub fn open_pidfd(_pid: u32) -> std::io::Result<OwnedFd> {
    Err(std::io::ErrorKind::Unsupported.into())
}

/// What a signal through a kernel-held process handle did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PidfdSignal {
    /// The kernel queued the signal for the pinned process (a zombie
    /// still takes it).
    Delivered,
    /// The pinned process has exited and been reaped (`ESRCH`): the handle
    /// names that one process, so it is provably gone.
    Exited,
    /// The signal was not sent and nothing is known about the process (a
    /// refused permission, a platform with no pidfd).
    Failed,
}

/// Signal through the kernel-held handle (`pidfd_send_signal`): the
/// signal reaches the pinned process and nothing else.
#[cfg(target_os = "linux")]
#[must_use]
pub fn pidfd_signal(fd: &OwnedFd, signal: Signal) -> PidfdSignal {
    let signal = match signal {
        Signal::Term => rustix::process::Signal::TERM,
        Signal::Kill => rustix::process::Signal::KILL,
    };
    match rustix::process::pidfd_send_signal(fd, signal) {
        Ok(()) => PidfdSignal::Delivered,
        Err(rustix::io::Errno::SRCH) => PidfdSignal::Exited,
        Err(_) => PidfdSignal::Failed,
    }
}

#[cfg(target_os = "macos")]
#[must_use]
pub fn pidfd_signal(_fd: &OwnedFd, _signal: Signal) -> PidfdSignal {
    PidfdSignal::Failed
}

/// Resolve once the process behind `pid` has exited, parked on the kernel's
/// exit notification (Linux pidfd readability, macOS kqueue
/// `EVFILT_PROC`/`NOTE_EXIT`), with no timer. A pid that names no process
/// (already exited and reaped) resolves at once. The kernel handle pins
/// the process instance, so a pid recycled after registration is never
/// mistaken for it.
///
/// # Errors
///
/// The OS error when the watch cannot register (no pidfd, descriptor
/// exhaustion); the caller owns its fallback.
#[cfg(target_os = "linux")]
pub async fn wait_for_exit(pid: u32) -> std::io::Result<()> {
    use nix::poll::{poll, PollFd, PollFlags, PollTimeout};
    use std::os::fd::AsFd;
    use tokio::io::{unix::AsyncFd, Interest};

    let fd = match open_pidfd(pid) {
        Ok(fd) => fd,
        Err(error) if error.raw_os_error() == Some(libc::ESRCH) => return Ok(()),
        Err(error) => return Err(error),
    };
    // The handle closes on drop, on every path.
    let fd = AsyncFd::with_interest(fd, Interest::READABLE)?;
    // Every wake is confirmed by a zero-timeout poll (AsyncFd readiness
    // can be spurious).
    loop {
        let mut ready = fd.readable().await?;
        if let Ok(result) = ready.try_io(|fd| {
            let mut probe = [PollFd::new(fd.get_ref().as_fd(), PollFlags::POLLIN)];
            let ready = poll(&mut probe, PollTimeout::ZERO)?;
            if ready == 0 {
                Err(std::io::ErrorKind::WouldBlock.into())
            } else {
                Ok(())
            }
        }) {
            return result;
        }
    }
}

/// macOS: kqueue `EVFILT_PROC`/`NOTE_EXIT` on a pollable kqueue.
///
/// # Errors
///
/// The OS error when the watch cannot register; the caller owns its
/// fallback.
#[cfg(target_os = "macos")]
pub async fn wait_for_exit(pid: u32) -> std::io::Result<()> {
    use nix::errno::Errno;
    use nix::sys::event::{EventFilter, EventFlag, FilterFlag, KEvent, Kqueue};
    use std::os::fd::{AsFd, AsRawFd, RawFd};
    use tokio::io::{unix::AsyncFd, Interest};

    /// The kqueue descriptor (closed on drop, on every path), registrable
    /// with the tokio reactor.
    struct KqueueFd(Kqueue);

    impl AsRawFd for KqueueFd {
        fn as_raw_fd(&self) -> RawFd {
            self.0.as_fd().as_raw_fd()
        }
    }

    let ident =
        usize::try_from(pid).map_err(|_| std::io::Error::from(std::io::ErrorKind::InvalidInput))?;
    let kq = Kqueue::new()?;
    // The block drops the `KEvent` value (its `udata` raw pointer is
    // `!Send`) before the first `.await`.
    {
        let change = KEvent::new(
            ident,
            EventFilter::EVFILT_PROC,
            EventFlag::EV_ADD,
            FilterFlag::NOTE_EXIT,
            0,
            0,
        );
        // Registers one change and reads no events. With no event space,
        // an attach failure comes back as -1/errno (kevent(2)), not an
        // `EV_ERROR` event.
        if let Err(errno) = kq.kevent(&[change], &mut [], None) {
            // `ESRCH` means the pid names no attachable process (reaped,
            // or already past its exit ref-drain - XNU runs the drain
            // before the exit knote fires): the exit already happened.
            // Every other errno (EMFILE, ENOMEM, ...) is a watch that
            // could not register; the caller falls back.
            return if errno == Errno::ESRCH {
                Ok(())
            } else {
                Err(errno.into())
            };
        }
    }
    let kq = AsyncFd::with_interest(KqueueFd(kq), Interest::READABLE)?;
    // Only the exit knote is registered, so a drained event is the exit.
    loop {
        let mut ready = kq.readable().await?;
        if let Ok(result) = ready.try_io(|kq| {
            let zero = libc::timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            let mut event = [KEvent::new(
                0,
                EventFilter::EVFILT_PROC,
                EventFlag::empty(),
                FilterFlag::empty(),
                0,
                0,
            )];
            // Drains one event with a zero timeout.
            let drained = kq.get_ref().0.kevent(&[], &mut event, Some(zero))?;
            if drained == 0 {
                Err(std::io::ErrorKind::WouldBlock.into())
            } else {
                Ok(())
            }
        }) {
            return result;
        }
    }
}

/// The signal number that terminated a child, when it was signaled
/// (`ExitStatus::signal`).
#[must_use]
pub fn termination_signal(status: &std::process::ExitStatus) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;
    status.signal()
}

/// The kernel-watch arms' shared exit contract: a pid that names no live
/// process resolves at once, so a worker that died before its watch
/// registered still reports an exit.
#[cfg(test)]
mod exit_wait_tests {
    use super::*;

    #[tokio::test]
    async fn wait_for_exit_resolves_at_once_for_a_reaped_pid() {
        let mut child = std::process::Command::new("sleep")
            .arg("600")
            .spawn()
            .expect("spawn sleep");
        let pid = child.id();
        child.kill().expect("kill sleep");
        child.wait().expect("reap sleep");
        assert!(
            wait_for_exit(pid).await.is_ok(),
            "a reaped pid resolves at once"
        );
    }
}
