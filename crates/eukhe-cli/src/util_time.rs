//! Timestamp helpers for the update flow's status and intent files
//! (`YYYY-MM-DDTHH:MM:SS.mmmZ`, the TS `new Date().toISOString()` shape).

use std::time::{SystemTime, UNIX_EPOCH};

/// Milliseconds since the Unix epoch.
#[must_use]
pub fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |duration| duration.as_millis() as u64)
}

/// The current instant as ISO-8601 with millisecond precision (the TS
/// `toISOString()` shape the status file records).
#[must_use]
pub fn now_iso8601() -> String {
    eukhe_daemon::util::iso_from_unix_ms(now_ms())
}

/// A duration as a status line reads it: `42ms`, `3.4s`, `2m 10s`,
/// `1h 5m`. Compact, one decimal below a minute.
#[must_use]
pub fn compact_duration(ms: u64) -> String {
    if ms < 1_000 {
        format!("{ms}ms")
    } else if ms < 60_000 {
        // Display only: the tenth of a second loses far below the unit.
        #[allow(clippy::cast_precision_loss)]
        let seconds = ms as f64 / 1_000.0;
        format!("{seconds:.1}s")
    } else if ms < 3_600_000 {
        let minutes = ms / 60_000;
        let seconds = (ms % 60_000) / 1_000;
        if seconds == 0 {
            format!("{minutes}m")
        } else {
            format!("{minutes}m {seconds}s")
        }
    } else {
        let hours = ms / 3_600_000;
        let minutes = (ms % 3_600_000) / 60_000;
        if minutes == 0 {
            format!("{hours}h")
        } else {
            format!("{hours}h {minutes}m")
        }
    }
}
