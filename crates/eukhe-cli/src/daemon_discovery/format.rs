//! Output rendering for the discovery commands: the daemon table (TS
//! `cli/daemon-ps-format.ts`) and the chalk-colored action lines of
//! `daemon-ps.ts`. Colors follow chalk's auto-detection: styled output only
//! when stdout is a terminal and `NO_COLOR` is unset. Piped output (the
//! differential corpus) is plain.

use super::{DaemonInfo, DaemonStatus};
use crate::styling::{Sgr, Styling};

/// The wire name of a status (TS serializes the kebab-case literal).
fn status_name(status: DaemonStatus) -> String {
    match status {
        DaemonStatus::Current => "current".to_string(),
        DaemonStatus::Stale => "stale".to_string(),
        DaemonStatus::Unreachable => "unreachable".to_string(),
        DaemonStatus::OrphanFile => "orphan-file".to_string(),
    }
}

/// The discovered-daemon table (TS `formatDaemonListTable`): socket, pid,
/// version, status, sessions, uptime; the default socket is starred with a
/// footnote.
pub(crate) fn format_daemon_list_table(daemons: &[DaemonInfo], styling: Styling) -> String {
    let headers = ["socket", "pid", "version", "status", "sessions", "uptime"];
    let rows: Vec<[String; 6]> = daemons
        .iter()
        .map(|daemon| {
            [
                if daemon.is_default {
                    format!("{} *", daemon.socket_path.display())
                } else {
                    daemon.socket_path.display().to_string()
                },
                daemon.pid.map(|pid| pid.to_string()).unwrap_or_default(),
                daemon.version.clone().unwrap_or_default(),
                color_status(styling, daemon.status, &status_name(daemon.status)),
                daemon
                    .session_count
                    .map(|count| count.to_string())
                    .unwrap_or_default(),
                format_uptime(daemon.uptime_seconds),
            ]
        })
        .collect();
    let widths: Vec<usize> = headers
        .iter()
        .enumerate()
        .map(|(column, header)| {
            rows.iter()
                .map(|row| eukhe_tui::width::str_width(&row[column]))
                .chain([header.len()])
                .max()
                .unwrap_or(0)
        })
        .collect();
    // Two spaces between columns (TS `formatTable`).
    let mut lines = vec![headers
        .iter()
        .enumerate()
        .map(|(column, header)| pad_end(header, widths[column]))
        .collect::<Vec<_>>()
        .join("  ")];
    for row in &rows {
        lines.push(
            row.iter()
                .enumerate()
                .map(|(column, value)| pad_end(value, widths[column]))
                .collect::<Vec<_>>()
                .join("  "),
        );
    }
    let table = lines.join("\n");
    if daemons.iter().any(|daemon| daemon.is_default) {
        format!(
            "{table}\n\n{}",
            styling.paint(Sgr::Dim, "* default background service")
        )
    } else {
        table
    }
}

/// The status cell carries its severity color (TS `colorStatus`); the column
/// width math runs on the visible text, not the escape codes.
fn color_status(styling: Styling, status: DaemonStatus, value: &str) -> String {
    let code = match status {
        DaemonStatus::Current => Sgr::Green,
        DaemonStatus::Stale => Sgr::Yellow,
        DaemonStatus::Unreachable => Sgr::Red,
        DaemonStatus::OrphanFile => Sgr::Dim,
    };
    styling.paint(code, value)
}

/// Compact uptime (TS `formatUptime`): seconds, minutes, hours, days, weeks.
pub(crate) fn format_uptime(uptime_seconds: Option<u64>) -> String {
    let Some(seconds) = uptime_seconds else {
        return String::new();
    };
    if seconds < 60 {
        return format!("{seconds}s");
    }
    let minutes = seconds / 60;
    if minutes < 60 {
        return format!("{minutes}m");
    }
    let hours = minutes / 60;
    if hours < 24 {
        return format!("{hours}h");
    }
    let days = hours / 24;
    if days < 7 {
        return format!("{days}d");
    }
    format!("{}w", days / 7)
}

/// Pad to a display width (TS `padEnd`); escape codes take no columns.
fn pad_end(text: &str, width: usize) -> String {
    let length = eukhe_tui::width::str_width(text);
    if length >= width {
        text.to_string()
    } else {
        format!("{text}{}", " ".repeat(width - length))
    }
}

/// The reap report: green `reaped` lines then dim `kept` lines
/// (TS `runReap` text output).
pub(crate) fn print_reap_report(reaped: &[(String, String)], skipped: &[(String, String)]) {
    if reaped.is_empty() && skipped.is_empty() {
        println!("No background services found.");
        return;
    }
    let styling = Styling::for_stdout();
    for (socket_path, action) in reaped {
        println!(
            "{}",
            styling.paint(Sgr::Green, &format!("reaped {socket_path}: {action}"))
        );
    }
    for (socket_path, reason) in skipped {
        println!(
            "{}",
            styling.paint(Sgr::Dim, &format!("kept   {socket_path}: {reason}"))
        );
    }
}

/// The shutdown report: green `stopped` lines then red `failed` lines
/// (TS `runShutdownAllConverging` text output).
pub(crate) fn print_shutdown_report(stopped: &[(String, String)], failed: &[(String, String)]) {
    if stopped.is_empty() && failed.is_empty() {
        println!("No background services found.");
        return;
    }
    let styling = Styling::for_stdout();
    for (socket_path, action) in stopped {
        println!(
            "{}",
            styling.paint(Sgr::Green, &format!("stopped {socket_path}: {action}"))
        );
    }
    for (socket_path, reason) in failed {
        println!(
            "{}",
            styling.paint(Sgr::Red, &format!("failed  {socket_path}: {reason}"))
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn daemon(socket: &str, status: DaemonStatus, is_default: bool) -> DaemonInfo {
        DaemonInfo {
            socket_path: std::path::PathBuf::from(socket),
            pid: Some(42),
            uptime_seconds: Some(3_700),
            version: Some("0.1.0".to_string()),
            protocol_version: Some(7),
            schema_id: Some("schema".to_string()),
            build_id: None,
            executable_path: None,
            pid_source: Some(super::super::PidSource::Listener),
            session_count: Some(2),
            status,
            is_default,
            has_tracked_workers: None,
        }
    }

    #[test]
    fn table_matches_the_ts_layout() {
        let table = format_daemon_list_table(
            &[
                daemon("/tmp/eukhe-1000/daemon.sock", DaemonStatus::Current, true),
                daemon("/tmp/other.sock", DaemonStatus::Stale, false),
            ],
            Styling::Plain,
        );
        // Column widths: socket 29 (the starred default path), pid 3,
        // version 7, status 7, sessions 8, uptime 6; two-space gutters.
        let expected_header = [
            ("socket", 29),
            ("pid", 3),
            ("version", 7),
            ("status", 7),
            ("sessions", 8),
            ("uptime", 6),
        ]
        .iter()
        .map(|(header, width)| format!("{header}{}", " ".repeat(width - header.len())))
        .collect::<Vec<_>>()
        .join("  ");
        let mut lines = table.split('\n');
        assert_eq!(lines.next().unwrap(), expected_header);
        assert!(lines
            .next()
            .unwrap()
            .starts_with("/tmp/eukhe-1000/daemon.sock *  42   0.1.0"));
        // The footnote names the default service.
        assert!(table.ends_with("* default background service"));
    }

    #[test]
    fn uptime_matches_the_ts_buckets() {
        assert_eq!(format_uptime(None), "");
        assert_eq!(format_uptime(Some(59)), "59s");
        assert_eq!(format_uptime(Some(60)), "1m");
        assert_eq!(format_uptime(Some(3_700)), "1h");
        assert_eq!(format_uptime(Some(90_000)), "1d");
        assert_eq!(format_uptime(Some(700_000)), "1w");
    }
}
