//! ISO-8601 UTC timestamps (JS `Date.prototype.toISOString` form) and their
//! parse back to unix milliseconds.

/// The current time as an ISO-8601 UTC timestamp with millisecond
/// precision, like `new Date().toISOString()`.
#[must_use]
pub fn format_iso_now() -> String {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default();
    format_iso(i64::try_from(now.as_millis()).unwrap_or(i64::MAX))
}

/// Format unix milliseconds as an ISO-8601 UTC timestamp.
#[must_use]
pub fn format_iso(millis: i64) -> String {
    let days = millis.div_euclid(86_400_000);
    let time_ms = millis.rem_euclid(86_400_000);
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    let hour = time_ms / 3_600_000;
    let minute = (time_ms / 60_000) % 60;
    let second = (time_ms / 1_000) % 60;
    let ms = time_ms % 1_000;
    format!("{y:04}-{m:02}-{d:02}T{hour:02}:{minute:02}:{second:02}.{ms:03}Z")
}

/// ISO-8601 timestamp -> unix milliseconds (best effort, UTC assumed; `0`
/// when it does not parse).
#[must_use]
pub fn timestamp_to_millis(timestamp: &str) -> u64 {
    timeparse(timestamp).unwrap_or(0)
}

fn timeparse(timestamp: &str) -> Option<u64> {
    // Minimal ISO-8601 parser for the formats the product writes:
    // YYYY-MM-DDTHH:MM:SS(.fff)?(Z|+HH:MM|+HHMM)?
    let bytes = timestamp.as_bytes();
    if bytes.len() < 19 {
        return None;
    }
    let num = |from: usize, to: usize| -> Option<i64> {
        std::str::from_utf8(&bytes[from..to]).ok()?.parse().ok()
    };
    let (year, month, day) = (num(0, 4)?, num(5, 7)?, num(8, 10)?);
    let (hour, minute, second) = (num(11, 13)?, num(14, 16)?, num(17, 19)?);
    // days from civil epoch
    let days = civil_days(year, month, day)?;
    let mut millis = ((days * 86_400) + hour * 3_600 + minute * 60 + second) * 1_000;
    let mut rest = &timestamp[19..];
    if rest.starts_with('.') {
        let fraction_end = rest[1..]
            .find(|c: char| !c.is_ascii_digit())
            .map_or(rest.len(), |idx| idx + 1);
        let fraction = &rest[1..fraction_end];
        let millis_part: u64 = fraction
            .chars()
            .take(3)
            .collect::<String>()
            .parse()
            .unwrap_or(0);
        millis += millis_part as i64;
        rest = &rest[fraction_end..];
    }
    if let Some(offset) = rest.strip_prefix('+') {
        let (h, m) = parse_offset(offset)?;
        millis -= h * 3_600_000 + m * 60_000;
    } else if let Some(offset) = rest.strip_prefix('-') {
        let (h, m) = parse_offset(offset)?;
        millis += h * 3_600_000 + m * 60_000;
    }
    Some(millis.max(0) as u64)
}

fn parse_offset(offset: &str) -> Option<(i64, i64)> {
    let offset = offset.trim_end_matches('Z').trim();
    if offset.is_empty() {
        return Some((0, 0));
    }
    let (h, m) = offset.split_once(':').unwrap_or((offset, "0"));
    Some((h.parse().ok()?, m.parse().ok()?))
}

fn civil_days(year: i64, month: i64, day: i64) -> Option<i64> {
    if !(1..=12).contains(&month) || !(1..=31).contains(&day) {
        return None;
    }
    let y = if month <= 2 { year - 1 } else { year };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let mp = if month > 2 { month - 3 } else { month + 9 };
    let doy = (153 * mp + 2) / 5 + day - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    Some(era * 146_097 + doe - 719_468)
}

#[cfg(test)]
mod tests {
    #[test]
    fn iso_format_round_trips() {
        let stamp = super::format_iso(1_704_067_200_012);
        assert_eq!(stamp, "2024-01-01T00:00:00.012Z");
        assert_eq!(super::timestamp_to_millis(&stamp), 1_704_067_200_012);
    }
}
