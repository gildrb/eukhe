//! Process control: signals, process groups, detached spawns.
//!
//! libc `kill` / `process_group(0)`. Signatures that report outcomes return
//! `bool` where callers treat "unproven" conservatively (a kill that could
//! not be proven reports false, matching the TS `killOrphanProcess`
//! contract).

use std::process::Command;

/// Termination signal for [`kill_pid`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Signal {
    /// Graceful stop (SIGTERM).
    Term,
    /// Forcible stop (SIGKILL).
    Kill,
}

/// Put the spawned child into its own process group so later group-scoped
/// kills reach all of its descendants (TS: `detached: true` on POSIX).
pub fn set_new_process_group(command: &mut Command) {
    use std::os::unix::process::CommandExt;
    command.process_group(0);
}

/// Start the spawned child in a new session with no controlling terminal
/// (`setsid`): the child cannot open `/dev/tty`, and job-control signals
/// from the parent's terminal never reach it. A new process group alone
/// is not enough: the group can still open the terminal, and a background
/// read then stops it with SIGTTIN.
pub fn set_new_session(command: &mut Command) {
    use std::os::unix::process::CommandExt;
    // SAFETY: the hook runs in the forked child before exec and only calls
    // setsid(2), which is async-signal-safe.
    unsafe {
        command.pre_exec(|| {
            nix::unistd::setsid()
                .map(drop)
                .map_err(std::io::Error::from)
        });
    }
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
    let mut limit = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &raw mut limit) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    #[cfg(not(target_os = "macos"))]
    let target = limit.rlim_max;
    #[cfg(target_os = "macos")]
    let target = {
        let mut per_process: libc::c_int = 0;
        let mut size = std::mem::size_of::<libc::c_int>();
        let read = unsafe {
            libc::sysctlbyname(
                c"kern.maxfilesperproc".as_ptr(),
                (&raw mut per_process).cast(),
                &raw mut size,
                std::ptr::null_mut(),
                0,
            )
        };
        if read != 0 {
            return Err(std::io::Error::last_os_error());
        }
        limit.rlim_max.min(per_process.unsigned_abs().into())
    };
    if limit.rlim_cur < target {
        limit.rlim_cur = target;
        if unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &raw const limit) } != 0 {
            return Err(std::io::Error::last_os_error());
        }
    }
    Ok(limit.rlim_cur)
}

/// Signal a single pid. Returns true only when the signal was delivered,
/// proving the pid was alive at signal time.
#[must_use]
pub fn kill_pid(pid: i32, signal: Signal) -> bool {
    if pid <= 0 {
        return false;
    }
    let sig = match signal {
        Signal::Term => libc::SIGTERM,
        Signal::Kill => libc::SIGKILL,
    };
    unsafe { libc::kill(pid, sig) == 0 }
}

/// Kill a process and all its children: the process group first (`bash()`
/// children run detached in a new group), then the bare pid as fallback.
/// Returns true when either signal was delivered (TS `killProcessTree`).
#[must_use]
pub fn kill_process_group_or_pid(pid: i32) -> bool {
    if pid <= 0 {
        return false;
    }
    unsafe {
        if libc::kill(-pid, libc::SIGKILL) == 0 {
            return true;
        }
    }
    unsafe { libc::kill(pid, libc::SIGKILL) == 0 }
}

/// Cheap `kill(pid, 0)` existence probe; counts zombies as existing.
#[must_use]
pub fn pid_exists(pid: u32) -> bool {
    if pid == 0 {
        return false;
    }
    unsafe { libc::kill(pid as i32, 0) == 0 }
}

/// The kernel-held process handle (`pidfd_open`): pins the exact process
/// behind the pid, so a signal through it ([`pidfd_signal`]) reaches that
/// process even if the numeric pid is recycled afterwards. The caller
/// treats an unobtainable handle as never-signal: a missed stop is
/// recoverable, a wrong one is not.
///
/// # Errors
///
/// Returns the open failure verbatim: `ESRCH` names a process that is
/// already gone, `Unsupported` a platform with no pidfd arm.
#[cfg(target_os = "linux")]
pub fn open_pidfd(pid: u32) -> std::io::Result<i32> {
    // `SYS_pidfd_open`/`SYS_pidfd_send_signal` share their numbers across
    // x86_64 and aarch64 (the Linux arches this workspace ships). pidfd is a
    // Linux syscall family; the macOS libc crate carries no `SYS_pidfd_*`.
    let fd = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0) };
    if fd < 0 {
        Err(std::io::Error::last_os_error())
    } else {
        Ok(fd as i32)
    }
}

/// macOS has no pidfd: the handle is unobtainable.
///
/// # Errors
///
/// Always `Unsupported`.
#[cfg(target_os = "macos")]
pub fn open_pidfd(_pid: u32) -> std::io::Result<i32> {
    Err(std::io::ErrorKind::Unsupported.into())
}

/// Signal through the kernel-held handle (`pidfd_send_signal`): the
/// signal reaches the pinned process and nothing else. The handle
/// CLOSES on drop by the caller (`close(fd)` via [`close_pidfd`]).
#[cfg(target_os = "linux")]
#[must_use]
pub fn pidfd_signal(fd: i32, signal: Signal) -> bool {
    let signum = match signal {
        Signal::Term => libc::SIGTERM,
        Signal::Kill => libc::SIGKILL,
    };
    unsafe {
        libc::syscall(
            libc::SYS_pidfd_send_signal,
            fd,
            signum,
            std::ptr::null::<u8>(),
            0,
        ) == 0
    }
}

#[cfg(target_os = "macos")]
#[must_use]
pub fn pidfd_signal(_fd: i32, _signal: Signal) -> bool {
    false
}

/// Release a kernel-held handle obtained from [`open_pidfd`].
pub fn close_pidfd(fd: i32) {
    unsafe {
        libc::close(fd);
    }
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
    use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
    use tokio::io::{unix::AsyncFd, Interest};

    let fd = match open_pidfd(pid) {
        Ok(fd) => fd,
        Err(error) if error.raw_os_error() == Some(libc::ESRCH) => return Ok(()),
        Err(error) => return Err(error),
    };
    // SAFETY: `open_pidfd` returned a fresh descriptor this call owns
    // (and closes on drop, on every path).
    let fd = AsyncFd::with_interest(unsafe { OwnedFd::from_raw_fd(fd) }, Interest::READABLE)?;
    // Every wake is confirmed by a zero-timeout poll (AsyncFd readiness
    // can be spurious).
    loop {
        let mut ready = fd.readable().await?;
        if let Ok(result) = ready.try_io(|fd| {
            let mut probe = libc::pollfd {
                fd: fd.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            };
            // SAFETY: polls one descriptor this call owns, without
            // blocking.
            match unsafe { libc::poll(&raw mut probe, 1, 0) } {
                1 => Ok(()),
                0 => Err(std::io::ErrorKind::WouldBlock.into()),
                _ => Err(std::io::Error::last_os_error()),
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
    use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
    use tokio::io::{unix::AsyncFd, Interest};

    // SAFETY: `kqueue()` takes no arguments.
    let kq = unsafe { libc::kqueue() };
    if kq < 0 {
        return Err(std::io::Error::last_os_error());
    }
    // SAFETY: a fresh descriptor this call owns (and closes on drop, on
    // every path).
    let kq = unsafe { OwnedFd::from_raw_fd(kq) };
    // The block drops the `kevent` value (its `udata` raw pointer is
    // `!Send`) before the first `.await`.
    {
        let change = libc::kevent {
            ident: pid as libc::uintptr_t,
            filter: libc::EVFILT_PROC,
            flags: libc::EV_ADD,
            fflags: libc::NOTE_EXIT,
            data: 0,
            udata: std::ptr::null_mut(),
        };
        // SAFETY: registers one change and reads no events; `change`
        // outlives the call. With no event space, an attach failure comes
        // back as -1/errno (kevent(2)), not an `EV_ERROR` event.
        if unsafe {
            libc::kevent(
                kq.as_raw_fd(),
                &raw const change,
                1,
                std::ptr::null_mut(),
                0,
                std::ptr::null(),
            )
        } < 0
        {
            // `ESRCH` means the pid names no attachable process (reaped,
            // or already past its exit ref-drain - XNU runs the drain
            // before the exit knote fires): the exit already happened.
            // Every other errno (EMFILE, ENOMEM, ...) is a watch that
            // could not register; the caller falls back.
            let error = std::io::Error::last_os_error();
            return match error.raw_os_error() {
                Some(libc::ESRCH) => Ok(()),
                _ => Err(error),
            };
        }
    }
    let kq = AsyncFd::with_interest(kq, Interest::READABLE)?;
    // Only the exit knote is registered, so a drained event is the exit.
    loop {
        let mut ready = kq.readable().await?;
        if let Ok(result) = ready.try_io(|kq| {
            let zero = libc::timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            let mut event = libc::kevent {
                ident: 0,
                filter: 0,
                flags: 0,
                fflags: 0,
                data: 0,
                udata: std::ptr::null_mut(),
            };
            // SAFETY: drains one event with a zero timeout; `event` and
            // `zero` outlive the call.
            match unsafe {
                libc::kevent(
                    kq.as_raw_fd(),
                    std::ptr::null(),
                    0,
                    &raw mut event,
                    1,
                    &raw const zero,
                )
            } {
                1 => Ok(()),
                0 => Err(std::io::ErrorKind::WouldBlock.into()),
                _ => Err(std::io::Error::last_os_error()),
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
