//! Waits on processes the test does not own (a kernel behind its manager).

use std::time::{Duration, Instant};

/// True while a live (non-zombie) process with this pid exists.
pub fn process_alive(pid: i32) -> bool {
    if pid <= 0 {
        return false;
    }
    std::fs::read_to_string(format!("/proc/{pid}/stat"))
        .ok()
        .and_then(|raw| {
            // pid (comm) state ...
            let close = raw.rfind(')')?;
            raw[close + 1..]
                .trim_start()
                .chars()
                .next()
                .map(|state| state != 'Z' && state != 'X')
        })
        .unwrap_or(false)
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
