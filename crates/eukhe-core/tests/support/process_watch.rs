//! Waits on processes the test does not own (a kernel behind its manager).

use std::time::{Duration, Instant};

/// True while a live (non-zombie) process with this pid exists: the
/// platform probe, which reads `/proc` where it is mounted and falls back
/// to `kill(pid, 0)` plus `ps` (macOS has no `/proc`).
pub fn process_alive(pid: i32) -> bool {
    let Ok(pid) = u32::try_from(pid) else {
        return false;
    };
    eukhe_types::platform::process::is_process_alive(pid).expect("the process liveness probe")
}

/// Poll until the pid leaves the live-process table (teardown kills are
/// synchronous, but the kernel may be mid-boot when its owner drops, so the
/// settle budget covers the boot finishing first).
pub async fn await_process_gone(pid: i32) {
    let deadline = Instant::now() + Duration::from_mins(1);
    while process_alive(pid) {
        assert!(
            Instant::now() < deadline,
            "kernel pid {pid} outlived the drop of its owner (teardown gap)"
        );
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
}
