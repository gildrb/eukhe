//! JavaScript built-in semantics the AWS SDK credential providers rely on:
//! `parseInt`, `Date.now()`, `new Date(string)`, `Date.prototype.toISOString`,
//! `String(error)`, property reads on parsed JSON, Node `path.join`, and the
//! Node `fs` error messages.

use std::io;
use std::time::{SystemTime, UNIX_EPOCH};

use eukhe_types::pi_ai::JsonValue;

use super::super::sigv4::civil_from_unix;
use crate::utils::diagnostics::{error_name, ErrorObject, Thrown};
use crate::utils::js::is_js_whitespace;

/// `Date.now()`: milliseconds since the Unix epoch.
pub(crate) fn now_ms() -> f64 {
    let elapsed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    // Millisecond timestamps stay far below 2^53.
    #[allow(
        clippy::cast_precision_loss,
        reason = "epoch milliseconds fit in an f64 mantissa"
    )]
    let millis = elapsed.as_millis() as f64;
    millis
}

/// JS `parseInt(text, radix)` for radix 10 (`Some(10)`) or the default radix
/// (`None`: a `0x`/`0X` prefix selects 16). `NaN` when no digit parses.
pub(crate) fn js_parse_int(text: &str, radix: Option<u32>) -> f64 {
    let text = text.trim_start_matches(is_js_whitespace);
    let (negative, rest) = match text.as_bytes().first() {
        Some(b'-') => (true, &text[1..]),
        Some(b'+') => (false, &text[1..]),
        _ => (false, text),
    };
    let (radix, digits) = match radix {
        None if rest.starts_with("0x") || rest.starts_with("0X") => (16, &rest[2..]),
        Some(radix) => (radix, rest),
        None => (10, rest),
    };
    let mut value: Option<f64> = None;
    for c in digits.chars() {
        let Some(digit) = c.to_digit(radix) else {
            break;
        };
        value = Some(value.unwrap_or(0.0) * f64::from(radix) + f64::from(digit));
    }
    match value {
        Some(value) if negative => -value,
        Some(value) => value,
        None => f64::NAN,
    }
}

/// Days since the Unix epoch of a proleptic Gregorian civil date (Howard
/// Hinnant's `days_from_civil`).
fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let year = if month <= 2 { year - 1 } else { year };
    let era = year.div_euclid(400);
    let year_of_era = year - era * 400;
    let month_index = (month + 9) % 12;
    let day_of_year = (153 * month_index + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}

fn is_leap_year(year: i64) -> bool {
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
}

fn days_in_month(year: i64, month: i64) -> i64 {
    match month {
        2 if is_leap_year(year) => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

/// `MakeDate` in milliseconds; `None` outside the JS time range (±8.64e15 ms).
fn make_time_ms(year: i64, month: i64, day: i64, hms: (i64, i64, i64), millis: i64) -> Option<f64> {
    let (hour, minute, second) = hms;
    let total = days_from_civil(year, month, day) * 86_400_000
        + hour * 3_600_000
        + minute * 60_000
        + second * 1000
        + millis;
    #[allow(
        clippy::cast_precision_loss,
        reason = "JS time values are within ±8.64e15"
    )]
    let total = total as f64;
    (total.abs() <= 8.64e15).then_some(total)
}

/// A run of exactly `count` ASCII digits at the start of `text`.
fn fixed_digits(text: &str, count: usize) -> Option<(i64, &str)> {
    let digits = text.get(..count)?;
    if !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    Some((digits.parse().ok()?, &text[count..]))
}

/// The leading milliseconds of a fraction (`.5` → 500, `.123456` → 123).
fn fraction_millis(digits: &str) -> i64 {
    let mut millis = 0;
    for (index, byte) in digits.bytes().take(3).enumerate() {
        let scale = [100, 10, 1][index];
        millis += i64::from(byte - b'0') * scale;
    }
    millis
}

/// JS `Date.parse` for the ECMAScript date-time string format
/// (`YYYY[-MM[-DD]][THH:mm[:ss[.sss]][Z|±HH:mm]]`). Date-only forms are UTC;
/// date-times without an offset are read as UTC as well (JS reads them as
/// local time; the credential files the SDK writes always carry `Z`).
/// `NaN` for any other text.
pub(crate) fn js_date_parse(text: &str) -> f64 {
    parse_date_time_string(text).unwrap_or(f64::NAN)
}

fn parse_date_time_string(text: &str) -> Option<f64> {
    let (year, mut rest) = match text.as_bytes().first() {
        Some(b'+' | b'-') => {
            let (value, rest) = fixed_digits(&text[1..], 6)?;
            if text.starts_with('-') {
                if value == 0 {
                    return None;
                }
                (-value, rest)
            } else {
                (value, rest)
            }
        }
        _ => fixed_digits(text, 4)?,
    };
    let mut month = 1;
    let mut day = 1;
    if let Some(after) = rest.strip_prefix('-') {
        let (value, after) = fixed_digits(after, 2)?;
        month = value;
        rest = after;
        if let Some(after) = rest.strip_prefix('-') {
            let (value, after) = fixed_digits(after, 2)?;
            day = value;
            rest = after;
        }
    }
    if !(1..=12).contains(&month) || day < 1 || day > days_in_month(year, month) {
        return None;
    }
    let (mut hour, mut minute, mut second, mut millis) = (0, 0, 0, 0);
    let mut offset_minutes = 0;
    if let Some(after) = rest.strip_prefix(['T', 't']) {
        let (value, after) = fixed_digits(after, 2)?;
        hour = value;
        let after = after.strip_prefix(':')?;
        let (value, after) = fixed_digits(after, 2)?;
        minute = value;
        rest = after;
        if let Some(after) = rest.strip_prefix(':') {
            let (value, after) = fixed_digits(after, 2)?;
            second = value;
            rest = after;
            if let Some(after) = rest.strip_prefix('.') {
                let end = after
                    .bytes()
                    .position(|byte| !byte.is_ascii_digit())
                    .unwrap_or(after.len());
                if end == 0 {
                    return None;
                }
                millis = fraction_millis(&after[..end]);
                rest = &after[end..];
            }
        }
        if let Some(after) = rest.strip_prefix(['Z', 'z']) {
            rest = after;
        } else if let Some(sign) = rest.chars().next().filter(|c| matches!(c, '+' | '-')) {
            let (offset_hour, after) = fixed_digits(&rest[1..], 2)?;
            let after = after.strip_prefix(':')?;
            let (offset_minute, after) = fixed_digits(after, 2)?;
            if offset_hour > 23 || offset_minute > 59 {
                return None;
            }
            let magnitude = offset_hour * 60 + offset_minute;
            offset_minutes = if sign == '-' { -magnitude } else { magnitude };
            rest = after;
        }
        let end_of_day = hour == 24 && minute == 0 && second == 0 && millis == 0;
        if !(hour < 24 || end_of_day) || minute > 59 || second > 59 {
            return None;
        }
    }
    if !rest.is_empty() {
        return None;
    }
    make_time_ms(
        year,
        month,
        day,
        (hour, minute - offset_minutes, second),
        millis,
    )
}

/// `parseRfc3339DateTime` of `@smithy/core/serde`: `YYYY-MM-DDTHH:mm:ss[.f+]Z`
/// with field range checks.
///
/// # Errors
///
/// The SDK's `TypeError` / `Error` messages for malformed or out-of-range values.
pub(crate) fn parse_rfc3339_date_time(value: &str) -> Result<f64, ErrorObject> {
    let invalid = || ErrorObject::named("TypeError", "Invalid RFC-3339 date-time value");
    let (year, rest) = fixed_digits(value, 4).ok_or_else(invalid)?;
    let rest = rest.strip_prefix('-').ok_or_else(invalid)?;
    let (month, rest) = fixed_digits(rest, 2).ok_or_else(invalid)?;
    let rest = rest.strip_prefix('-').ok_or_else(invalid)?;
    let (day, rest) = fixed_digits(rest, 2).ok_or_else(invalid)?;
    let rest = rest.strip_prefix(['T', 't']).ok_or_else(invalid)?;
    let (hour, rest) = fixed_digits(rest, 2).ok_or_else(invalid)?;
    let rest = rest.strip_prefix(':').ok_or_else(invalid)?;
    let (minute, rest) = fixed_digits(rest, 2).ok_or_else(invalid)?;
    let rest = rest.strip_prefix(':').ok_or_else(invalid)?;
    let (second, mut rest) = fixed_digits(rest, 2).ok_or_else(invalid)?;
    let mut millis = 0;
    if let Some(after) = rest.strip_prefix('.') {
        let end = after
            .bytes()
            .position(|byte| !byte.is_ascii_digit())
            .unwrap_or(after.len());
        if end == 0 {
            return Err(invalid());
        }
        millis = fraction_millis(&after[..end]);
        rest = &after[end..];
    }
    if !matches!(rest, "Z" | "z") {
        return Err(invalid());
    }
    let range = |value: i64, name: &str, lower: i64, upper: i64| {
        if (lower..=upper).contains(&value) {
            Ok(())
        } else {
            Err(ErrorObject::new(format!(
                "{name} must be between {lower} and {upper}, inclusive"
            )))
        }
    };
    range(month, "month", 1, 12)?;
    range(day, "day", 1, 31)?;
    let month_days = days_in_month(year, month);
    if day > month_days {
        const MONTH_NAMES: [&str; 12] = [
            "January",
            "February",
            "March",
            "April",
            "May",
            "June",
            "July",
            "August",
            "September",
            "October",
            "November",
            "December",
        ];
        let index = usize::try_from(month - 1).unwrap_or_default();
        return Err(ErrorObject::named(
            "TypeError",
            format!("Invalid day for {} in {year}: {day}", MONTH_NAMES[index]),
        ));
    }
    range(hour, "hours", 0, 23)?;
    range(minute, "minutes", 0, 59)?;
    range(second, "seconds", 0, 60)?;
    make_time_ms(year, month, day, (hour, minute, second), millis).ok_or_else(invalid)
}

/// `new Date(value)` of a parsed JSON value: numbers are time values, strings
/// parse, everything else is an invalid date.
pub(crate) fn js_date_from_json(value: &JsonValue) -> f64 {
    match value {
        JsonValue::Number(number) => number.as_f64().unwrap_or(f64::NAN),
        JsonValue::String(text) => js_date_parse(text),
        JsonValue::Bool(true) => 1.0,
        JsonValue::Bool(false) | JsonValue::Null => 0.0,
        JsonValue::Array(_) | JsonValue::Object(_) => f64::NAN,
    }
}

/// `Date.prototype.toISOString()`.
///
/// # Errors
///
/// `RangeError: Invalid time value` for an invalid date.
pub(crate) fn to_iso_string(time_ms: f64) -> Result<String, ErrorObject> {
    if !time_ms.is_finite() || time_ms.abs() > 8.64e15 {
        return Err(ErrorObject::named("RangeError", "Invalid time value"));
    }
    #[allow(
        clippy::cast_possible_truncation,
        reason = "finite and within ±8.64e15"
    )]
    let time_ms = time_ms.floor() as i64;
    let seconds = time_ms.div_euclid(1000);
    let millis = time_ms.rem_euclid(1000);
    let days = seconds.div_euclid(86_400);
    let second_of_day = seconds.rem_euclid(86_400);
    let (year, month, day, ..) = if days >= 0 {
        civil_from_unix(u64::try_from(seconds).unwrap_or_default())
    } else {
        civil_from_negative_days(days)
    };
    let hour = second_of_day / 3600;
    let minute = second_of_day % 3600 / 60;
    let second = second_of_day % 60;
    let year_text = if (0..=9999).contains(&year) {
        format!("{year:04}")
    } else if year < 0 {
        format!("-{:06}", -year)
    } else {
        format!("+{year:06}")
    };
    Ok(format!(
        "{year_text}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}.{millis:03}Z"
    ))
}

/// Civil date of a day count before the epoch (Howard Hinnant's
/// `civil_from_days`), shaped like [`civil_from_unix`].
fn civil_from_negative_days(days: i64) -> (i64, u32, u32, u32, u32, u32) {
    let shifted = days + 719_468;
    let era = shifted.div_euclid(146_097);
    let day_of_era = shifted - era * 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_index = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_index + 2) / 5 + 1;
    let month = if month_index < 10 {
        month_index + 3
    } else {
        month_index - 9
    };
    let year = year_of_era + era * 400 + i64::from(month <= 2);
    (
        year,
        u32::try_from(month).unwrap_or_default(),
        u32::try_from(day).unwrap_or_default(),
        0,
        0,
        0,
    )
}

/// JS `String(error)`: `name: message`, or the name alone for an empty message.
pub(crate) fn js_error_string(error: &Thrown) -> String {
    let name = error_name(error.as_ref());
    let message = error.to_string();
    if message.is_empty() {
        name
    } else {
        format!("{name}: {message}")
    }
}

/// The JS truthiness of a parsed JSON value.
pub(crate) fn json_truthy(value: Option<&JsonValue>) -> bool {
    match value {
        None | Some(JsonValue::Null | JsonValue::Bool(false)) => false,
        Some(JsonValue::Number(number)) => number.as_f64().is_some_and(|n| n != 0.0 && !n.is_nan()),
        Some(JsonValue::String(text)) => !text.is_empty(),
        Some(JsonValue::Bool(true) | JsonValue::Array(_) | JsonValue::Object(_)) => true,
    }
}

/// JS `value[key]` on a parsed JSON value: objects yield the property, other
/// primitives `undefined`.
///
/// # Errors
///
/// The `TypeError` JS throws when reading a property of `null`.
pub(crate) fn json_property<'a>(
    value: &'a JsonValue,
    key: &str,
) -> Result<Option<&'a JsonValue>, ErrorObject> {
    match value {
        JsonValue::Null => Err(ErrorObject::named(
            "TypeError",
            format!("Cannot read properties of null (reading '{key}')"),
        )),
        JsonValue::Object(object) => Ok(object.get(key)),
        JsonValue::Array(_) | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::String(_) => {
            Ok(None)
        }
    }
}

/// Node `path.join(base, rest)` with POSIX normalization.
pub(crate) fn node_path_join(parts: &[&str]) -> String {
    let joined = parts
        .iter()
        .filter(|part| !part.is_empty())
        .copied()
        .collect::<Vec<_>>()
        .join("/");
    if joined.is_empty() {
        return ".".to_owned();
    }
    let absolute = joined.starts_with('/');
    let trailing_slash = joined.ends_with('/');
    let mut segments: Vec<&str> = Vec::new();
    for segment in joined.split('/') {
        match segment {
            "" | "." => {}
            ".." => {
                if segments.last().is_some_and(|last| *last != "..") {
                    segments.pop();
                } else if !absolute {
                    segments.push("..");
                }
            }
            other => segments.push(other),
        }
    }
    let mut normalized = segments.join("/");
    if absolute {
        normalized.insert(0, '/');
    }
    if normalized.is_empty() {
        return ".".to_owned();
    }
    if trailing_slash && !normalized.ends_with('/') {
        normalized.push('/');
    }
    normalized
}

/// The Node `fs` error for a failed `syscall` on `path` (`ENOENT: no such file
/// or directory, open '<path>'`).
pub(crate) fn node_fs_error(error: &io::Error, syscall: &str, path: &str) -> Thrown {
    let code_and_text = match error.kind() {
        io::ErrorKind::NotFound => Some(("ENOENT", "no such file or directory")),
        io::ErrorKind::PermissionDenied => Some(("EACCES", "permission denied")),
        io::ErrorKind::IsADirectory => Some(("EISDIR", "illegal operation on a directory")),
        _ => None,
    };
    let message = match code_and_text {
        // Node reports EISDIR from the `read` that follows a successful `open`.
        Some(("EISDIR", text)) => format!("EISDIR: {text}, read"),
        Some((code, text)) => format!("{code}: {text}, {syscall} '{path}'"),
        None => format!("{error}, {syscall} '{path}'"),
    };
    ErrorObject::new(message).thrown()
}
