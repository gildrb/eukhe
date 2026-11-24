//! Process start times and the uptime clock (port of omp
//! `crates/natives/src/desktop/macos/process.rs` and `control/macos.rs`).

use std::mem;

/// When process `pid` started, in microseconds since the epoch.
pub(crate) fn started(pid: i32) -> Option<u64> {
    let mut info: libc::proc_bsdinfo = unsafe_zeroed();
    let size = i32::try_from(mem::size_of::<libc::proc_bsdinfo>()).ok()?;
    // SAFETY: `info` is a writable `proc_bsdinfo` of exactly `size` bytes,
    // the buffer PROC_PIDTBSDINFO fills.
    let written = unsafe {
        libc::proc_pidinfo(
            pid,
            libc::PROC_PIDTBSDINFO,
            0,
            std::ptr::from_mut(&mut info).cast(),
            size,
        )
    };
    (written == size)
        .then(|| {
            info.pbi_start_tvsec
                .checked_mul(1_000_000)?
                .checked_add(info.pbi_start_tvusec)
        })
        .flatten()
}

/// Nanoseconds of `CLOCK_UPTIME_RAW`, the clock Quartz event timestamps
/// and `WindowServer`'s front-process requests use.
pub(crate) fn uptime_ns() -> u64 {
    let mut time = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    // SAFETY: `time` is writable for the call, which keeps no pointer.
    unsafe { libc::clock_gettime(libc::CLOCK_UPTIME_RAW, &raw mut time) };
    u64::try_from(time.tv_sec)
        .unwrap_or(0)
        .saturating_mul(1_000_000_000)
        .saturating_add(u64::try_from(time.tv_nsec).unwrap_or(0))
}

fn unsafe_zeroed() -> libc::proc_bsdinfo {
    // SAFETY: `proc_bsdinfo` is plain integers and byte arrays, for which
    // all-zero is a valid value.
    unsafe { mem::zeroed() }
}
