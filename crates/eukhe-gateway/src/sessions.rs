//! The saved root sessions the phone picks from: the `list_saved_sessions`
//! rows, the routing mode, and the `/sessions` lines.

pub(crate) use eukhe_client::saved_sessions::SavedSession;

/// How many sessions `/sessions` shows.
pub(crate) const LISTED_SESSIONS: usize = 9;

/// The longest session title `/sessions` shows, in characters.
const TITLE_CHARS: usize = 40;

/// The name of the root session (`Route::Root`): the gateway finds it by
/// this name after every restart, and names the session it creates so.
pub(crate) const ROOT_SESSION_NAME: &str = "root";

/// Which session the phone's messages go to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Route {
    /// The newest root session when each message arrives (the session the
    /// CLI used last).
    Follow,
    /// One session, chosen with `/use N` or made with `/new`.
    Pinned(SessionRef),
    /// The persistent root session named [`ROOT_SESSION_NAME`] (with
    /// `gateway.rootHeartbeat` set): made when missing, kept alive by its
    /// heartbeat.
    Root,
}

/// The route the phone's messages take at start and after `/latest`: the
/// root session when `gateway.rootHeartbeat` is set, else the newest
/// session.
pub(crate) fn home_route(root_heartbeat: Option<&str>) -> Route {
    match root_heartbeat {
        Some(_) => Route::Root,
        None => Route::Follow,
    }
}

/// The root session among the saved root sessions (newest first): the
/// newest one named [`ROOT_SESSION_NAME`].
pub(crate) fn root_session(sessions: &[SavedSession]) -> Option<&SavedSession> {
    sessions
        .iter()
        .find(|saved| saved.name.as_deref() == Some(ROOT_SESSION_NAME))
}

/// One session's identity and storage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SessionRef {
    pub(crate) id: String,
    pub(crate) path: String,
}

impl From<&SavedSession> for SessionRef {
    fn from(saved: &SavedSession) -> Self {
        Self {
            id: saved.id.clone(),
            path: saved.path.clone(),
        }
    }
}

/// A title on one line, at most [`TITLE_CHARS`] characters.
pub(crate) fn short_title(title: &str) -> String {
    let flat = title.split_whitespace().collect::<Vec<_>>().join(" ");
    if flat.chars().count() > TITLE_CHARS {
        let cut: String = flat.chars().take(TITLE_CHARS - 1).collect();
        format!("{cut}…")
    } else {
        flat
    }
}

/// One `/sessions` line: `N. <title> | <cwd basename> | <age>`, with a
/// leading `*` on the bound session.
pub(crate) fn session_line(
    number: usize,
    saved: &SavedSession,
    bound: Option<&SessionRef>,
    now_ms: u64,
) -> String {
    let marker = if bound.is_some_and(|bound| bound.id == saved.id) {
        "*"
    } else {
        ""
    };
    let title = saved
        .title
        .as_deref()
        .map_or_else(|| "(no title)".to_string(), short_title);
    let dir = std::path::Path::new(&saved.cwd).file_name().map_or_else(
        || saved.cwd.clone(),
        |name| name.to_string_lossy().into_owned(),
    );
    let age = if let Some(modified_ms) = unix_ms(&saved.modified) {
        let minutes = now_ms.saturating_sub(modified_ms) / 60_000;
        if minutes < 60 {
            format!("{minutes}m")
        } else if minutes < 24 * 60 {
            format!("{}h", minutes / 60)
        } else {
            format!("{}d", minutes / (24 * 60))
        }
    } else {
        tracing::warn!(modified = %saved.modified, path = %saved.path, "undatable session");
        "age unknown".to_string()
    };
    format!("{marker}{number}. {title} | {dir} | {age}")
}

/// Epoch milliseconds of an RFC 3339 UTC timestamp
/// (`YYYY-MM-DDTHH:MM:SS[.fff]Z`, the daemon's form); `None` otherwise.
fn unix_ms(iso: &str) -> Option<u64> {
    let field = |range: std::ops::Range<usize>| iso.get(range)?.parse::<u64>().ok();
    let separators = iso.as_bytes();
    if separators.len() < 20
        || separators[4] != b'-'
        || separators[7] != b'-'
        || separators[10] != b'T'
        || separators[13] != b':'
        || separators[16] != b':'
        || !iso.ends_with('Z')
    {
        return None;
    }
    let (year, month, day) = (field(0..4)?, field(5..7)?, field(8..10)?);
    let (hour, minute, second) = (field(11..13)?, field(14..16)?, field(17..19)?);
    let millis = match iso.get(19..iso.len() - 1)? {
        "" => 0,
        fraction => {
            let digits = fraction.strip_prefix('.')?;
            let padded = format!("{digits:0<3}");
            padded.get(..3)?.parse::<u64>().ok()?
        }
    };
    if year < 1970 || !(1..=12).contains(&month) || !(1..=31).contains(&day) || hour > 23 {
        return None;
    }
    if minute > 59 || second > 60 {
        return None;
    }
    // Days from the civil date (Howard Hinnant's `days_from_civil`), for
    // years from 1970 on: the March-based year keeps February last.
    let shifted_year = if month <= 2 { year - 1 } else { year };
    let era = shifted_year / 400;
    let year_of_era = shifted_year - era * 400;
    let march_month = (month + 9) % 12;
    let day_of_year = (153 * march_month + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    let days = (era * 146_097 + day_of_era).checked_sub(719_468)?;
    Some((((days * 24 + hour) * 60 + minute) * 60 + second) * 1000 + millis)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `gateway.rootHeartbeat` routes the phone to the root session; unset,
    /// to the newest session, as before the setting.
    #[test]
    fn the_root_heartbeat_routes_to_the_root_session() {
        assert_eq!(home_route(Some("every 30 minutes")), Route::Root);
        assert_eq!(home_route(None), Route::Follow);
    }

    /// The root session is the newest one named `root`; a session whose
    /// first message is `root` is not it.
    #[test]
    fn the_root_session_is_found_by_its_name() {
        let saved = |id: &str, name: Option<&str>, title: &str| SavedSession {
            id: id.to_string(),
            path: format!("/s/{id}"),
            cwd: "/home/u".to_string(),
            name: name.map(str::to_string),
            title: Some(title.to_string()),
            modified: "2026-11-01T08:00:00Z".to_string(),
        };
        let sessions = [
            saved("first", None, ROOT_SESSION_NAME),
            saved("newer", Some(ROOT_SESSION_NAME), ROOT_SESSION_NAME),
            saved("older", Some(ROOT_SESSION_NAME), ROOT_SESSION_NAME),
        ];
        assert_eq!(root_session(&sessions), Some(&sessions[1]));
        assert_eq!(root_session(&sessions[..1]), None);
    }
}
