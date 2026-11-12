//! The `/heartbeat` command language (TS `parseHeartbeatCommand` and
//! `normalizeHeartbeatSchedule` in core/cron-jobs.ts): the client parses the
//! command it sends, the daemon normalizes the schedule a `heartbeat_set`
//! carries, and the cron core shares the duration-unit vocabulary.

/// The schedule a heartbeat set without one runs on.
pub const DEFAULT_HEARTBEAT_SCHEDULE: &str = "every 5m";

const ONE_SECOND_MS: u64 = 1000;
const ONE_MINUTE_MS: u64 = 60 * ONE_SECOND_MS;

const USAGE: &str = "Usage: /heartbeat [--every <interval>] [--steer|--follow-up] <instruction>";
const INVALID_DELIVERY: &str = "Heartbeat delivery mode must be \"steer\" or \"follow_up\"";

/// Parsed `/heartbeat` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParsedHeartbeatCommand {
    Status,
    Pause,
    Resume,
    Clear,
    Set {
        schedule: String,
        instruction: String,
        /// The wire delivery mode (`steer` / `follow_up`); `None` leaves
        /// the daemon's default.
        delivery_mode: Option<&'static str>,
    },
}

/// The milliseconds one duration unit spans; seconds only where
/// `allow_seconds` (recurring intervals, not one-shot delays).
#[must_use]
pub fn unit_multiplier(unit: &str, allow_seconds: bool) -> Option<u64> {
    let unit = unit.trim();
    let seconds = allow_seconds && matches!(unit, "s" | "sec" | "secs" | "second" | "seconds");
    if seconds {
        return Some(ONE_SECOND_MS);
    }
    if matches!(unit, "m" | "min" | "mins" | "minute" | "minutes") {
        return Some(ONE_MINUTE_MS);
    }
    if matches!(unit, "h" | "hr" | "hrs" | "hour" | "hours") {
        return Some(60 * ONE_MINUTE_MS);
    }
    if matches!(unit, "d" | "day" | "days") {
        return Some(24 * 60 * ONE_MINUTE_MS);
    }
    None
}

/// `<digits> <unit?>` with the unit optionally attached (`10m`, `10 m`).
#[must_use]
pub fn split_amount_unit(rest: &str) -> Option<(u64, &str)> {
    let rest = rest.trim();
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    if digits.is_empty() {
        return None;
    }
    let digits_len = digits.len();
    let unit = rest[digits_len..].trim();
    let amount: u64 = digits.parse().ok()?;
    if !unit.is_empty()
        && !rest[digits_len..].starts_with(char::is_whitespace)
        && !unit.chars().all(|c| c.is_ascii_alphabetic())
    {
        return None;
    }
    Some((amount, unit))
}

/// TS `normalizeHeartbeatSchedule`: no schedule is the default one, and a
/// bare duration (`10m`) is the interval `every 10m`.
#[must_use]
pub fn normalize_heartbeat_schedule(input: Option<&str>) -> String {
    let text = input.map(str::trim).filter(|text| !text.is_empty());
    let Some(text) = text else {
        return DEFAULT_HEARTBEAT_SCHEDULE.to_string();
    };
    if let Some((_, unit)) = split_amount_unit(text) {
        if !unit.is_empty() && unit_multiplier(unit, true).is_some() {
            return format!("every {text}");
        }
    }
    text.to_string()
}

/// Parse a `/heartbeat ...` command body.
///
/// # Errors
///
/// Returns an error when the command body is malformed: an unknown delivery
/// mode is given, an `--every` option is used without an interval value, or
/// the command ends with no instruction to set.
pub fn parse_heartbeat_command(input: &str) -> anyhow::Result<ParsedHeartbeatCommand> {
    let text = input
        .strip_prefix("/heartbeat")
        .filter(|rest| rest.chars().next().is_none_or(char::is_whitespace))
        .map_or_else(|| input.trim(), str::trim_start)
        .trim_end();
    if text.is_empty() || text == "status" {
        return Ok(ParsedHeartbeatCommand::Status);
    }
    if text == "pause" {
        return Ok(ParsedHeartbeatCommand::Pause);
    }
    if text == "resume" {
        return Ok(ParsedHeartbeatCommand::Resume);
    }
    if text == "clear" || text == "stop" {
        return Ok(ParsedHeartbeatCommand::Clear);
    }
    let leading = consume_delivery_option(text)?;
    let mut delivery_mode = leading.0;
    let rest = leading.1;

    if let Some(option) = consume_every_option(&rest)? {
        let trailing = consume_delivery_option(&option.1)?;
        delivery_mode = trailing.0.or(delivery_mode);
        if trailing.1.is_empty() {
            anyhow::bail!(USAGE);
        }
        return Ok(ParsedHeartbeatCommand::Set {
            schedule: normalize_heartbeat_schedule(Some(&option.0)),
            instruction: trailing.1,
            delivery_mode,
        });
    }
    if let Some(leading_schedule) = consume_leading_every_schedule(&rest) {
        let trailing = consume_delivery_option(&leading_schedule.1)?;
        delivery_mode = trailing.0.or(delivery_mode);
        if trailing.1.is_empty() {
            anyhow::bail!(USAGE);
        }
        return Ok(ParsedHeartbeatCommand::Set {
            schedule: normalize_heartbeat_schedule(Some(&leading_schedule.0)),
            instruction: trailing.1,
            delivery_mode,
        });
    }
    let rest = rest.trim();
    if rest.is_empty() {
        anyhow::bail!(USAGE);
    }
    Ok(ParsedHeartbeatCommand::Set {
        schedule: DEFAULT_HEARTBEAT_SCHEDULE.to_string(),
        instruction: rest.to_string(),
        delivery_mode,
    })
}

fn consume_delivery_option(text: &str) -> anyhow::Result<(Option<&'static str>, String)> {
    let mut rest = text.trim().to_string();
    let lower = rest.to_lowercase();
    if lower == "--deliver" || lower.ends_with(" --deliver") {
        anyhow::bail!(INVALID_DELIVERY);
    }
    let mut delivery_mode = None;
    while let Some((mode, remaining)) = consume_leading_delivery_flag(&rest)? {
        delivery_mode = Some(mode);
        rest = remaining.trim().to_string();
    }
    let mut trailing_delivery_mode = None;
    while let Some((mode, remaining)) = consume_trailing_delivery_flag(&rest)? {
        // Consume all trailing flags but keep the rightmost (textually latest).
        trailing_delivery_mode = trailing_delivery_mode.or(Some(mode));
        rest = remaining.trim().to_string();
    }
    Ok((trailing_delivery_mode.or(delivery_mode), rest))
}

fn consume_leading_delivery_flag(text: &str) -> anyhow::Result<Option<(&'static str, String)>> {
    let trimmed = text.trim_start();
    let Some(after_dash) = trimmed.strip_prefix("--") else {
        return Ok(None);
    };
    if let Some(value) = after_dash.strip_prefix("deliver") {
        let value = value
            .strip_prefix('=')
            .map(String::from)
            .or_else(|| value.strip_prefix(char::is_whitespace).map(String::from))
            .unwrap_or_default();
        if value.is_empty() {
            anyhow::bail!(INVALID_DELIVERY);
        }
        let (token, remainder) = split_first_token(&value);
        let mode = parse_delivery_mode_token(token)?;
        return Ok(Some((mode, remainder.to_string())));
    }
    for (token, mode) in [
        ("steer", "steer"),
        ("follow-up", "follow_up"),
        ("follow_up", "follow_up"),
    ] {
        if let Some(rest) = after_dash.strip_prefix(token) {
            check_standalone(after_dash, token)?;
            return Ok(Some((mode, rest.to_string())));
        }
    }
    Ok(None)
}

fn check_standalone(rest: &str, token: &str) -> anyhow::Result<()> {
    let after = &rest[token.len()..];
    if !after.is_empty() && !after.starts_with(char::is_whitespace) {
        anyhow::bail!(INVALID_DELIVERY);
    }
    Ok(())
}

fn split_first_token(value: &str) -> (&str, &str) {
    match value.find(char::is_whitespace) {
        Some(index) => (&value[..index], value[index..].trim_start()),
        None => (value, ""),
    }
}

fn consume_trailing_delivery_flag(text: &str) -> anyhow::Result<Option<(&'static str, String)>> {
    let lower = text.to_lowercase();
    if let Some(index) = lower.rfind(" --deliver ") {
        let token = text[index + " --deliver ".len()..].trim();
        if !token.is_empty() && !token.contains(char::is_whitespace) {
            return Ok(Some((
                parse_delivery_mode_token(token)?,
                text[..index].to_string(),
            )));
        }
    }
    if let Some(index) = lower.rfind(" --deliver=") {
        let token = text[index + " --deliver=".len()..].trim();
        if !token.is_empty() && !token.contains(char::is_whitespace) {
            return Ok(Some((
                parse_delivery_mode_token(token)?,
                text[..index].to_string(),
            )));
        }
    }
    for token in ["--follow-up", "--follow_up", "--steer"] {
        if let Some(index) = lower.rfind(&format!(" {token}")) {
            if index + token.len() + 1 == text.len() {
                return Ok(Some((
                    parse_delivery_mode_token(&token[2..])?,
                    text[..index].to_string(),
                )));
            }
        }
    }
    Ok(None)
}

fn parse_delivery_mode_token(token: &str) -> anyhow::Result<&'static str> {
    let normalized = token.to_lowercase().replace('-', "_");
    match normalized.as_str() {
        "steer" => Ok("steer"),
        "follow_up" => Ok("follow_up"),
        _ => Err(anyhow::anyhow!(INVALID_DELIVERY)),
    }
}

fn consume_every_option(text: &str) -> anyhow::Result<Option<(String, String)>> {
    let trimmed = text.trim_start();
    let Some(rest) = trimmed.strip_prefix("--every") else {
        return Ok(None);
    };
    let rest = match rest.strip_prefix('=') {
        Some(value) => value.to_string(),
        None => match rest.strip_prefix(char::is_whitespace) {
            Some(value) => value.to_string(),
            // No separator: "--everyfoo" is not an every option.
            None if !rest.is_empty() => return Ok(None),
            None => String::new(),
        },
    };
    // Quoted or bare interval value.
    let (interval, remainder): (String, String) = if let Some(stripped) = rest.strip_prefix('"') {
        match stripped.find('"') {
            Some(index) => (
                stripped[..index].to_string(),
                stripped[index + 1..].to_string(),
            ),
            None => (stripped.to_string(), String::new()),
        }
    } else if let Some(stripped) = rest.strip_prefix('\'') {
        match stripped.find('\'') {
            Some(index) => (
                stripped[..index].to_string(),
                stripped[index + 1..].to_string(),
            ),
            None => (stripped.to_string(), String::new()),
        }
    } else {
        let (token, rest) = split_first_token(&rest);
        (token.to_string(), rest.to_string())
    };
    if interval.is_empty() {
        anyhow::bail!(USAGE);
    }
    Ok(Some((interval, remainder.trim_start().to_string())))
}

fn consume_leading_every_schedule(text: &str) -> Option<(String, String)> {
    let lower = text.to_lowercase();
    for prefix in ["every ", "each "] {
        if let Some(rest) = lower.strip_prefix(prefix) {
            let first_token = rest.split_whitespace().next()?;
            let Some((_, unit)) = split_amount_unit(first_token) else {
                continue;
            };
            if unit.is_empty() || unit_multiplier(unit, true).is_none() {
                continue;
            }
            let consumed = (prefix.len() + first_token.len()).min(text.len());
            let remainder = text[consumed..].trim();
            // Strip a standalone "--" separator, never a flag.
            let remainder = remainder
                .strip_prefix("--")
                .filter(|after| after.is_empty() || after.starts_with(char::is_whitespace))
                .map_or(remainder, str::trim)
                .trim()
                .to_string();
            let interval = format!("{} {}", prefix.trim(), first_token);
            return Some((interval, remainder));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The `Set` a valid instruction parses to, as (schedule, instruction, delivery mode).
    fn parsed_set(input: &str) -> (String, String, Option<&'static str>) {
        match parse_heartbeat_command(input).unwrap() {
            ParsedHeartbeatCommand::Set {
                schedule,
                instruction,
                delivery_mode,
            } => (schedule, instruction, delivery_mode),
            other => panic!("expected set for {input:?}, got {other:?}"),
        }
    }

    fn set(
        schedule: &str,
        instruction: &str,
        delivery_mode: Option<&'static str>,
    ) -> (String, String, Option<&'static str>) {
        (schedule.to_string(), instruction.to_string(), delivery_mode)
    }

    #[test]
    fn heartbeat_command_parses_the_subcommands() {
        use ParsedHeartbeatCommand::*;
        assert_eq!(parse_heartbeat_command("status").unwrap(), Status);
        assert_eq!(parse_heartbeat_command("/heartbeat").unwrap(), Status);
        assert_eq!(
            parse_heartbeat_command("/heartbeat status").unwrap(),
            Status
        );
        assert_eq!(parse_heartbeat_command("/heartbeat pause").unwrap(), Pause);
        assert_eq!(
            parse_heartbeat_command("/heartbeat resume").unwrap(),
            Resume
        );
        assert_eq!(parse_heartbeat_command("/heartbeat stop").unwrap(), Clear);
        assert_eq!(parse_heartbeat_command("/heartbeat clear").unwrap(), Clear);
    }

    #[test]
    fn heartbeat_command_parses_the_schedule_forms() {
        // Bare instruction uses the default schedule.
        assert_eq!(
            parsed_set("/heartbeat check the build"),
            set("every 5m", "check the build", None)
        );
        // --every with bare and quoted values.
        assert_eq!(
            parsed_set("/heartbeat --every 10m keep going"),
            set("every 10m", "keep going", None)
        );
        assert_eq!(
            parsed_set("/heartbeat --every=\"15 m\" watch things"),
            set("every 15 m", "watch things", None)
        );
        // Leading schedule form, as the command hint advertises it.
        assert_eq!(
            parsed_set("/heartbeat every 2h sweep logs"),
            set("every 2h", "sweep logs", None)
        );
        assert_eq!(
            parsed_set("every 1m say hi"),
            set("every 1m", "say hi", None)
        );
        assert_eq!(
            parsed_set("every 1m --follow-up say hi"),
            set("every 1m", "say hi", Some("follow_up"))
        );
    }

    #[test]
    fn heartbeat_command_parses_the_delivery_flags() {
        // Leading, trailing, and --deliver forms.
        for (input, mode) in [
            ("/heartbeat --steer --every 5m ping", "steer"),
            ("/heartbeat --every 5m ping --follow-up", "follow_up"),
            ("/heartbeat --deliver=steer --every 5m ping", "steer"),
            (
                "/heartbeat --deliver follow_up --every 5m ping",
                "follow_up",
            ),
        ] {
            assert_eq!(
                parsed_set(input),
                set("every 5m", "ping", Some(mode)),
                "{input}"
            );
        }
    }

    #[test]
    fn heartbeat_command_rejects_like_the_ts_command() {
        // Missing instruction and a bad delivery mode are the TS errors.
        for (input, error) in [
            ("/heartbeat --every 10m", USAGE),
            ("/heartbeat every 1m", USAGE),
            ("/heartbeat --deliver loud ping", INVALID_DELIVERY),
        ] {
            assert_eq!(
                parse_heartbeat_command(input).unwrap_err().to_string(),
                error,
                "{input}"
            );
        }
    }

    #[test]
    fn heartbeat_schedules_normalize() {
        assert_eq!(normalize_heartbeat_schedule(None), "every 5m");
        assert_eq!(normalize_heartbeat_schedule(Some("  ")), "every 5m");
        assert_eq!(normalize_heartbeat_schedule(Some("10m")), "every 10m");
        assert_eq!(
            normalize_heartbeat_schedule(Some("90 seconds")),
            "every 90 seconds"
        );
        assert_eq!(normalize_heartbeat_schedule(Some("* * * * *")), "* * * * *");
    }
}
