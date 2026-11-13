//! `eukhe usage`: the plan quota of each provider with a stored login, read
//! from the provider's plan usage endpoint: each window's used share and
//! reset time.

use std::time::{Duration, UNIX_EPOCH};

use eukhe_ai::quota::{
    fetch_plan_quota, CredentialKind, PlanCredential, PlanQuota, QuotaError, QuotaWindow,
};
use eukhe_core::auth::{AuthCredential, AuthStorage};
use eukhe_core::platform::{local_time, LocalTime};
use serde_json::json;

use crate::config::APP_NAME;

/// How the answer prints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Output {
    Text,
    Json,
}

/// One provider's answer.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Answer {
    Quota(PlanQuota),
    /// An API key: metered per request, no plan quota.
    ApiKey,
    /// A login whose provider reports no plan quota.
    NoQuota,
    /// The login's token could not be had (an expired login whose refresh
    /// failed).
    NoToken(String),
    Failed(QuotaError),
}

/// Run the `usage` command; returns the process exit code.
pub fn run_usage_command(args: &[String]) -> i32 {
    let output = match args {
        [] => Output::Text,
        [flag] if flag == "--json" => Output::Json,
        [other, ..] => {
            eprintln!("Error: unexpected argument: {other}");
            eprintln!("Run \"{APP_NAME} help usage\" for usage.");
            return 2;
        }
    };
    let Ok(runtime) = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    else {
        eprintln!("Error: could not start the provider runtime.");
        return 1;
    };
    let mut auth = AuthStorage::create(crate::config::get_agent_dir());
    let mut answers = Vec::new();
    for provider in auth.list() {
        if provider.starts_with("mcp:") {
            continue;
        }
        let answer = answer(&mut auth, &runtime, &provider);
        answers.push((provider, answer));
    }
    let failed = answers
        .iter()
        .any(|(_, answer)| matches!(answer, Answer::Failed(_) | Answer::NoToken(_)));
    println!(
        "{}",
        match output {
            Output::Text => render_text(&answers, crate::util_time::now_ms(), &local_clock),
            Output::Json => render_json(&answers),
        }
    );
    i32::from(failed)
}

/// Read one provider's plan quota with its stored login.
fn answer(auth: &mut AuthStorage, runtime: &tokio::runtime::Runtime, provider: &str) -> Answer {
    let resolved = auth.get_api_key_with_source_token(provider, false);
    let Some(access) = resolved.api_key else {
        return Answer::NoToken(
            resolved
                .refresh_error
                .map_or_else(|| "no token".to_owned(), |error| error.to_string()),
        );
    };
    let stored = auth.get_all().credential(provider);
    let (refresh, account_id, enterprise_url) = match &stored {
        Some(AuthCredential::Oauth {
            refresh,
            account_id,
            enterprise_url,
            ..
        }) => (
            refresh.as_deref().filter(|token| !token.is_empty()),
            account_id.as_deref(),
            enterprise_url.as_deref(),
        ),
        Some(AuthCredential::ApiKey { .. } | AuthCredential::McpStaticToken { .. }) | None => {
            (None, None, None)
        }
    };
    let kind = match resolved.credential_type {
        Some("oauth") => CredentialKind::OAuth,
        _ => CredentialKind::ApiKey,
    };
    let credential = PlanCredential {
        kind,
        access: &access,
        refresh,
        account_id,
        enterprise_url,
    };
    match runtime.block_on(fetch_plan_quota(provider, &credential)) {
        Ok(Some(quota)) => Answer::Quota(quota),
        Ok(None) if kind == CredentialKind::ApiKey => Answer::ApiKey,
        Ok(None) => Answer::NoQuota,
        Err(error) => Answer::Failed(error),
    }
}

/// A permille share as a percentage: `37%`, `81.5%`.
fn percent(permille: u32) -> String {
    match permille % 10 {
        0 => format!("{}%", permille / 10),
        tenth => format!("{}.{tenth}%", permille / 10),
    }
}

/// An instant broken down in the local time zone; `None` when the zone
/// cannot convert it.
type LocalClock<'a> = &'a dyn Fn(u64) -> Option<LocalTime>;

/// The local time zone of this process.
fn local_clock(epoch_ms: u64) -> Option<LocalTime> {
    local_time(UNIX_EPOCH + Duration::from_millis(epoch_ms)).ok()
}

/// The local calendar day of an instant, counted from 1970-01-01.
#[allow(
    clippy::cast_possible_wrap,
    reason = "epoch seconds stay far inside the i64 range"
)]
fn local_day(epoch_ms: u64, local: &LocalTime) -> i64 {
    ((epoch_ms / 1_000) as i64 + local.offset_seconds).div_euclid(86_400)
}

/// A wait as `2h 15m`, or `2d 3h` from a day up.
fn wait(ms: u64) -> String {
    const DAY_MS: u64 = 86_400_000;
    if ms < DAY_MS {
        return crate::util_time::compact_duration(ms);
    }
    match (ms / DAY_MS, ms % DAY_MS / 3_600_000) {
        (days, 0) => format!("{days}d"),
        (days, hours) => format!("{days}d {hours}h"),
    }
}

/// When a window resets, in local time: `19:35` today, `Sat 14:00` within
/// the week, `2026-08-01 14:00` later.
fn reset_text(at_ms: u64, now_ms: u64, clock: LocalClock<'_>) -> String {
    const WEEKDAYS: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
    let wait_text = at_ms
        .checked_sub(now_ms)
        .filter(|ms| *ms > 0)
        .map(|ms| format!(" (in {})", wait(ms)));
    let verb = if wait_text.is_some() {
        "resets"
    } else {
        "reset"
    };
    let wait_text = wait_text.unwrap_or_default();
    let (Some(at), Some(now)) = (clock(at_ms), clock(now_ms)) else {
        return format!("{verb}{wait_text}");
    };
    let time = format!("{:02}:{:02}", at.hour, at.minute);
    let day = local_day(at_ms, &at);
    let when = match day - local_day(now_ms, &now) {
        0 => time,
        1..=6 => {
            let weekday = usize::try_from((day + 4).rem_euclid(7)).unwrap_or_default();
            format!("{} {time}", WEEKDAYS[weekday])
        }
        _ => format!("{} {time}", at.date()),
    };
    format!("{verb} {when}{wait_text}")
}

fn window_line(window: &QuotaWindow, width: usize, now_ms: u64, clock: LocalClock<'_>) -> String {
    let reset = window.resets_at_ms.map_or_else(String::new, |at| {
        format!(", {}", reset_text(at, now_ms, clock))
    });
    format!(
        "  {:width$}  {} used{reset}",
        window.label,
        percent(window.used_permille)
    )
}

fn render_text(answers: &[(String, Answer)], now_ms: u64, clock: LocalClock<'_>) -> String {
    if answers.is_empty() {
        return "No stored logins.".to_owned();
    }
    answers
        .iter()
        .map(|(provider, answer)| match answer {
            Answer::Quota(quota) => {
                let width = quota
                    .windows
                    .iter()
                    .map(|window| window.label.chars().count())
                    .max()
                    .unwrap_or(0);
                let plan = quota
                    .plan
                    .as_ref()
                    .map_or_else(String::new, |plan| format!(" (plan {plan})"));
                std::iter::once(format!("{provider}{plan}"))
                    .chain(
                        quota
                            .windows
                            .iter()
                            .map(|window| window_line(window, width, now_ms, clock)),
                    )
                    .collect::<Vec<_>>()
                    .join("\n")
            }
            Answer::ApiKey => format!("{provider}: API key, no plan quota"),
            Answer::NoQuota => format!("{provider}: no readable plan quota"),
            Answer::NoToken(reason) => format!("{provider}: login unusable: {reason}"),
            Answer::Failed(error) => format!("{provider}: {error}"),
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn render_json(answers: &[(String, Answer)]) -> String {
    let providers: Vec<serde_json::Value> = answers
        .iter()
        .map(|(provider, answer)| match answer {
            Answer::Quota(quota) => {
                let mut quota = json!(quota);
                for window in quota["windows"].as_array_mut().into_iter().flatten() {
                    if let Some(at) = window["resetsAtMs"].as_u64() {
                        window["resetsAt"] = json!(eukhe_daemon::util::iso_from_unix_ms(at));
                    }
                }
                json!({ "provider": provider, "quota": quota })
            }
            Answer::ApiKey => {
                json!({ "provider": provider, "quota": null, "credential": "api_key" })
            }
            Answer::NoQuota => json!({ "provider": provider, "quota": null }),
            Answer::NoToken(reason) => {
                json!({ "provider": provider, "quota": null, "error": reason })
            }
            Answer::Failed(error) => {
                json!({ "provider": provider, "quota": null, "error": error.to_string() })
            }
        })
        .collect();
    json!({ "providers": providers }).to_string()
}

#[cfg(test)]
mod tests;
