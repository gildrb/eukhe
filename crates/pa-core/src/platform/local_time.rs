//! Local wall-clock time: an instant broken down in the process time zone
//! (`TZ`, else the system zone). The chat memory files its log by local day
//! and reports message times in local time (`memory` module).

use std::io;
use std::time::{SystemTime, UNIX_EPOCH};

/// One instant broken down in the local time zone.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LocalTime {
    pub year: i64,
    /// 1-12.
    pub month: u32,
    /// 1-31.
    pub day: u32,
    pub hour: u32,
    pub minute: u32,
    pub second: u32,
    pub millisecond: u32,
    /// Seconds east of UTC at this instant.
    pub offset_seconds: i64,
}

impl LocalTime {
    /// The local calendar day, `YYYY-MM-DD`.
    #[must_use]
    pub fn date(&self) -> String {
        format!("{:04}-{:02}-{:02}", self.year, self.month, self.day)
    }

    /// RFC 3339 with milliseconds and the local offset, for example
    /// `2026-10-05T09:32:11.123+02:00`.
    #[must_use]
    pub fn rfc3339(&self) -> String {
        let sign = if self.offset_seconds < 0 { '-' } else { '+' };
        let offset = self.offset_seconds.unsigned_abs();
        format!(
            "{}T{:02}:{:02}:{:02}.{:03}{sign}{:02}:{:02}",
            self.date(),
            self.hour,
            self.minute,
            self.second,
            self.millisecond,
            offset / 3600,
            offset % 3600 / 60,
        )
    }
}

/// The local time of `instant`.
///
/// # Errors
///
/// Returns an error when the instant precedes the Unix epoch, does not fit
/// the platform's `time_t`, or the platform cannot convert it.
pub fn local_time(instant: SystemTime) -> io::Result<LocalTime> {
    let since_epoch = instant
        .duration_since(UNIX_EPOCH)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidInput, error))?;
    let seconds = i64::try_from(since_epoch.as_secs())
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidInput, error))?;
    let fields = broken_down(seconds)?;
    let local_seconds = days_from_civil(fields.year, fields.month, fields.day) * 86_400
        + i64::from(fields.hour) * 3600
        + i64::from(fields.minute) * 60
        + i64::from(fields.second);
    Ok(LocalTime {
        year: fields.year,
        month: fields.month,
        day: fields.day,
        hour: fields.hour,
        minute: fields.minute,
        second: fields.second,
        millisecond: since_epoch.subsec_millis(),
        offset_seconds: local_seconds - seconds,
    })
}

/// Calendar fields of one instant, before the offset is derived.
struct Fields {
    year: i64,
    month: u32,
    day: u32,
    hour: u32,
    minute: u32,
    second: u32,
}

#[cfg(unix)]
fn broken_down(seconds: i64) -> io::Result<Fields> {
    let time: libc::time_t = seconds
        .try_into()
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidInput, error))?;
    // SAFETY: `libc::tm` is a plain C struct; all-zero bytes are a valid
    // value for every field (integers and a nullable zone pointer).
    let mut tm: libc::tm = unsafe { std::mem::zeroed() };
    // SAFETY: `localtime_r` reads `time` and writes only `tm`; both
    // pointers are valid for the duration of the call.
    let result = unsafe { libc::localtime_r(&raw const time, &raw mut tm) };
    if result.is_null() {
        return Err(io::Error::last_os_error());
    }
    let field = |value: libc::c_int| {
        u32::try_from(value).map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
    };
    Ok(Fields {
        year: i64::from(tm.tm_year) + 1900,
        month: field(tm.tm_mon)? + 1,
        day: field(tm.tm_mday)?,
        hour: field(tm.tm_hour)?,
        minute: field(tm.tm_min)?,
        second: field(tm.tm_sec)?,
    })
}

#[cfg(not(unix))]
fn broken_down(_seconds: i64) -> io::Result<Fields> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "local time conversion is implemented for Unix platforms only",
    ))
}

/// Parse a UTC ISO-8601 instant, `YYYY-MM-DDTHH:MM:SS[.fff]Z` (the form
/// session files store). `None` for any other shape.
#[must_use]
pub fn parse_utc_iso(text: &str) -> Option<SystemTime> {
    let text = text.strip_suffix('Z')?;
    let (date, time) = text.split_once('T')?;
    let mut date_parts = date.split('-');
    let year: i64 = date_parts.next()?.parse().ok()?;
    let month: u32 = date_parts.next()?.parse().ok()?;
    let day: u32 = date_parts.next()?.parse().ok()?;
    if date_parts.next().is_some() || !(1..=12).contains(&month) || !(1..=31).contains(&day) {
        return None;
    }
    let (clock, fraction) = time.split_once('.').unwrap_or((time, ""));
    let mut clock_parts = clock.split(':');
    let hour: i64 = clock_parts.next()?.parse().ok()?;
    let minute: i64 = clock_parts.next()?.parse().ok()?;
    let second: i64 = clock_parts.next()?.parse().ok()?;
    if clock_parts.next().is_some() || hour > 23 || minute > 59 || second > 60 {
        return None;
    }
    let millis: u64 = if fraction.is_empty() {
        0
    } else {
        let digits: String = fraction
            .chars()
            .chain(std::iter::repeat('0'))
            .take(3)
            .collect();
        digits.parse().ok()?
    };
    let seconds = days_from_civil(year, month, day) * 86_400 + hour * 3600 + minute * 60 + second;
    let seconds = u64::try_from(seconds).ok()?;
    UNIX_EPOCH.checked_add(std::time::Duration::from_millis(
        seconds.checked_mul(1000)?.checked_add(millis)?,
    ))
}

/// Days since 1970-01-01 of a proleptic Gregorian date (Howard Hinnant's
/// `days_from_civil`).
fn days_from_civil(year: i64, month: u32, day: u32) -> i64 {
    let year = if month <= 2 { year - 1 } else { year };
    let era = if year >= 0 { year } else { year - 399 } / 400;
    let year_of_era = year - era * 400;
    let month = i64::from(month);
    let shifted_month = if month > 2 { month - 3 } else { month + 9 };
    let day_of_year = (153 * shifted_month + 2) / 5 + i64::from(day) - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn days_from_civil_matches_known_dates() {
        assert_eq!(days_from_civil(1970, 1, 1), 0);
        assert_eq!(days_from_civil(2000, 3, 1), 11_017);
        assert_eq!(days_from_civil(2026, 10, 5), 20_731);
    }

    #[test]
    fn parses_utc_iso_instants() {
        let instant = parse_utc_iso("2026-10-05T07:48:47.036Z").unwrap();
        let millis = instant.duration_since(UNIX_EPOCH).unwrap().as_millis();
        assert_eq!(
            millis,
            (20_731 * 86_400 + 7 * 3600 + 48 * 60 + 47) * 1000 + 36
        );
        assert!(parse_utc_iso("2026-10-05T07:48:47").is_none());
        assert!(parse_utc_iso("2026-13-05T07:48:47Z").is_none());
        assert_eq!(
            parse_utc_iso("1970-01-01T00:00:01Z"),
            UNIX_EPOCH.checked_add(std::time::Duration::from_secs(1))
        );
    }

    #[test]
    fn rfc3339_renders_offset_and_milliseconds() {
        let time = LocalTime {
            year: 2026,
            month: 10,
            day: 5,
            hour: 9,
            minute: 3,
            second: 7,
            millisecond: 45,
            offset_seconds: -(3 * 3600 + 30 * 60),
        };
        assert_eq!(time.rfc3339(), "2026-10-05T09:03:07.045-03:30");
        assert_eq!(time.date(), "2026-10-05");
    }

    #[cfg(unix)]
    #[test]
    fn local_time_offset_is_whole_minutes() {
        let time = local_time(SystemTime::now()).unwrap();
        assert_eq!(time.offset_seconds % 60, 0);
        assert!((1..=12).contains(&time.month));
    }
}
