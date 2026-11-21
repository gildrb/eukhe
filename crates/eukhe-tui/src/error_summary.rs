//! Error-detail normalization and collapsing, a port of the TS
//! `collapsible-error.ts`: multi-line provider/tool errors render as a
//! one-line summary (the last non-stack-context line) while conversation
//! detail is below `all`, and expand to the full text in `all` mode.

use crate::theme::{Theme, ThemeColor};
use crate::width::{str_width, wrap_line};
use crate::{Line, Span};

/// `normalizeErrorDetails`: strip ANSI, normalize newlines, trim the end.
#[must_use]
pub fn normalize_error_details(text: &str) -> String {
    let stripped = strip_ansi(text);
    let unified = stripped.replace("\r\n", "\n").replace('\r', "\n");
    unified.trim_end().to_string()
}

/// `stripAnsi`: remove every escape sequence (the exact TS utils.ts:899
/// scanner -- see [`crate::ansi::strip_ansi`]).
#[must_use]
pub fn strip_ansi(text: &str) -> String {
    crate::ansi::strip_ansi(text)
}

/// `shouldCollapseErrorDetails`: multi-line errors collapse.
#[must_use]
pub fn should_collapse_error_details(text: &str) -> bool {
    normalize_error_details(text).contains('\n')
}

/// The report the daemon appends to a request that ended on an expired
/// login (eukhe-core `models::registry`).
const LOGIN_EXPIRED_REPORT: &str = "The stored login expired and its refresh failed.";

/// The fix that the end report of a run with no usable login and no other
/// signed-in provider names (eukhe-core `durable::fallback::end_report`).
const LOGIN_FIX: &str = "Fix: run eukhe and type /login";

/// `formatInlineLoginRecoveryMessage` (TS assistant-message.ts): an error
/// whose normalized text ends with `\n\n` + the expired-login report renders
/// as one inline line -- `{base} - {report}` with `base` the suffix-stripped,
/// end-trimmed remainder. `None` keeps the normal error paths: no suffix,
/// an empty base, or a base that would itself collapse (multi-line).
#[must_use]
pub fn format_inline_login_recovery_message(text: &str) -> Option<String> {
    let normalized = normalize_error_details(text);
    let base = normalized
        .strip_suffix(&format!("\n\n{LOGIN_EXPIRED_REPORT}"))?
        .trim_end();
    if base.is_empty() || should_collapse_error_details(base) {
        return None;
    }
    Some(format!("{base} - {LOGIN_EXPIRED_REPORT}"))
}

/// The provider a missing-credentials failure names: the pi-ai wording
/// `No API key for provider: <provider>` (every provider transport throws
/// it before the request leaves).
const MISSING_KEY_PREFIX: &str = "No API key for provider: ";

/// The words the quota park's failure texts share (`Session parked until
/// <time> ...`, `Session is parked until <time> ...`, eukhe-core
/// `quota_parked_final_error` and `quota_already_parked_final_error`).
const PARKED_MARKER: &str = " parked until ";

/// Whether an error is a provider's server error (a 5xx status) while it
/// checked the login (`503 credential validation failed`): a fault on the
/// provider's side, not a rejected login (that is a 401).
fn is_login_check_fault(normalized: &str) -> bool {
    normalized
        .to_ascii_lowercase()
        .contains("credential validation")
        && normalized
            .split(|c: char| !c.is_ascii_digit())
            .any(|digits| digits.len() == 3 && digits.starts_with('5'))
}

/// What a failed turn's error row reports after the failure: how the turn
/// ended, never a step for the user to take (a run falls over to another
/// configured model by itself; a row that remains is the run's end). A
/// quota park says the turn goes on by itself at the reset; a provider that
/// failed to check the login (`provider`: its name, when the row knows it)
/// says whose fault it is; a missing key names its provider; every other
/// failure says no other configured model took the turn. An error that
/// already carries the expired-login report or the end report of a run
/// with no usable login gets none.
#[must_use]
pub fn failure_report(error: &str, provider: Option<&str>) -> Option<String> {
    let normalized = normalize_error_details(error);
    if normalized.contains(LOGIN_EXPIRED_REPORT) || normalized.contains(LOGIN_FIX) {
        return None;
    }
    if normalized.contains(PARKED_MARKER) {
        return Some("The turn goes on by itself at the reset.".to_string());
    }
    if is_login_check_fault(&normalized) {
        let provider = provider
            .map(str::trim)
            .filter(|provider| !provider.is_empty())
            .unwrap_or("The provider");
        return Some(format!(
            "{provider} could not check the login: a fault on its side."
        ));
    }
    let provider = normalized
        .split_once(MISSING_KEY_PREFIX)
        .and_then(|(_, rest)| rest.split_whitespace().next())
        .map(|provider| provider.trim_end_matches(['.', ',', ';', '"', '\'']))
        .filter(|provider| !provider.is_empty());
    Some(match provider {
        Some(provider) => {
            format!("{provider} has no credentials, and no other configured model took the turn.")
        }
        None => "No other configured model took the turn.".to_string(),
    })
}

/// `startsStackContext` (trimmed line): the leading rows of a traceback.
fn starts_stack_context(line: &str) -> bool {
    line.starts_with("Traceback ")
        || (line.starts_with("File ") && line.contains(", line "))
        || (line.starts_with("Cell In[") && line.contains(", line "))
        || line.starts_with("---->")
}

/// `isStackContextLine` (raw line, keeps leading whitespace).
fn is_stack_context_line(raw: &str) -> bool {
    starts_stack_context(raw.trim_start()) || raw.starts_with(' ') || raw.starts_with('\t')
}

/// `summarizeErrorDetails`: the first line, or the last non-stack-context
/// line when the error opens with a traceback.
#[must_use]
pub fn summarize_error_details(text: &str) -> String {
    let normalized = normalize_error_details(text);
    let lines: Vec<&str> = normalized
        .split('\n')
        .filter(|line| !line.trim().is_empty())
        .collect();
    if lines.is_empty() {
        return "Error".to_string();
    }
    if lines.len() > 1 && starts_stack_context(lines[0].trim()) {
        for line in lines.iter().rev() {
            if !is_stack_context_line(line) {
                return line.trim().to_string();
            }
        }
        return "Error".to_string();
    }
    lines[0].trim().to_string()
}

fn display_content(text: &str, summary: Option<&str>, expanded: bool) -> Option<String> {
    let text = normalize_error_details(text);
    if text.is_empty() {
        return None;
    }
    let collapsed = should_collapse_error_details(&text);
    let content = if collapsed && !expanded {
        let summary = match summary {
            Some(summary) => normalize_error_details(summary),
            None => summarize_error_details(&text),
        };
        format!("{summary} ")
    } else {
        text
    };
    Some(content)
}

/// The collapsible error rows (`CollapsibleErrorComponent.render`): the
/// summary line while collapsed, the full text expanded; every row
/// one-space indented, wrapped at `width - 1`, padded with plain spaces.
#[must_use]
pub fn render_collapsible_error(
    text: &str,
    summary: Option<&str>,
    expanded: bool,
    color: ThemeColor,
    theme: &Theme,
    width: usize,
) -> Vec<Line> {
    let Some(content) = display_content(text, summary, expanded) else {
        return Vec::new();
    };
    let style = theme.fg_style(color);
    let content_width = width.saturating_sub(1).max(1);
    let mut out: Vec<Line> = Vec::new();
    for raw in content.split('\n') {
        let styled: Line = if raw.is_empty() {
            Vec::new()
        } else {
            vec![Span::styled(raw.to_string(), style)]
        };
        for mut line in wrap_line(&styled, content_width) {
            let mut row: Line = vec![Span::raw(" ")];
            row.append(&mut line);
            let used: usize = row.iter().map(|s| str_width(&s.content)).sum();
            if used < width {
                row.push(Span::raw(" ".repeat(width - used)));
            }
            out.push(row);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strip_and_summarize() {
        let text = "Traceback (most recent call last):\n  File \"x.py\", line 1\nValueError: boom";
        assert_eq!(summarize_error_details(text), "ValueError: boom");
        assert!(should_collapse_error_details(text));
        assert!(!should_collapse_error_details("single line"));
        assert_eq!(normalize_error_details("a\r\nb\u{1b}[31m"), "a\nb");
        assert_eq!(
            strip_ansi("\u{1b}]8;;http://x\u{1b}\\link\u{1b}]8;;\u{1b}\\"),
            "link"
        );
    }

    #[test]
    fn inline_login_recovery_merges_suffix_terminated_errors() {
        // The exact daemon wording.
        assert_eq!(
            format_inline_login_recovery_message(
                "OAuth token refresh failed for \"local-inference\": invalid_grant\n\nThe stored login expired and its refresh failed."
            )
            .as_deref(),
            Some(
                "OAuth token refresh failed for \"local-inference\": invalid_grant - The stored login expired and its refresh failed."
            )
        );
        // The base is suffix-stripped and end-trimmed; ANSI and CRLF
        // normalize away first (`normalizeErrorDetails`).
        assert_eq!(
            format_inline_login_recovery_message(
                "Auth failed. \r\n\r\nThe stored login expired and its refresh failed.\u{1b}[0m"
            )
            .as_deref(),
            Some("Auth failed. - The stored login expired and its refresh failed.")
        );
    }

    #[test]
    fn inline_login_recovery_keeps_the_normal_error_paths() {
        // No suffix at all.
        assert_eq!(
            format_inline_login_recovery_message("Authentication failed for \"local-inference\"."),
            None
        );
        // Suffix not at the end.
        assert_eq!(
            format_inline_login_recovery_message(
                "Auth failed.\n\nThe stored login expired and its refresh failed.\nProvider degraded."
            ),
            None
        );
        // Bare report without the blank-line separator.
        assert_eq!(
            format_inline_login_recovery_message(
                "The stored login expired and its refresh failed."
            ),
            None
        );
        // Empty base: the report alone stays collapsible.
        assert_eq!(
            format_inline_login_recovery_message(
                "\n\nThe stored login expired and its refresh failed."
            ),
            None
        );
        // Multi-line base falls back to the collapsible path.
        assert_eq!(
            format_inline_login_recovery_message(
                "Auth failed\nfor provider.\n\nThe stored login expired and its refresh failed."
            ),
            None
        );
    }

    /// The row reports how the turn ended and never asks the user for a
    /// step: a missing key names its provider; a provider that failed to
    /// check the login says whose fault it is; a park goes on by itself;
    /// any other failure had no configured model to take the turn; an
    /// error carrying the expired-login report or the end report of a run
    /// with no usable login gets none.
    #[test]
    fn failure_report_says_how_the_turn_ended() {
        let reports = [
            failure_report("Error: No API key for provider: cloudflare-ai-gateway", None),
            failure_report(
                "! Error: Retry failed after 2 attempts: No API key for provider: anthropic.",
                None,
            ),
            failure_report("Error: 529 overloaded", None),
            // The owner's row: the provider's login check failed on its side.
            failure_report(
                "! Error: Retry failed after 3 attempts: 503 credential validation failed",
                Some("Anthropic"),
            ),
            failure_report("Error: 503 credential validation failed", None),
            // A 4xx that names credentials is no fault of the provider.
            failure_report("Error: 401 credential validation failed", Some("Anthropic")),
            failure_report(
                "Provider requested a 172800s wait before retrying (above retry.provider.maxRetryDelayMs=15000ms). Session parked until 2026-10-23T14:05:00.000Z and will resume automatically (retry.provider.waitForUsage.pauseUntilReset): 429 rate limit",
                None,
            ),
            failure_report(
                "Auth failed.\n\nThe stored login expired and its refresh failed.",
                None,
            ),
            failure_report(
                "The run ended: anthropic has no usable login (OAuth refresh failed for anthropic: 400), and no other signed-in provider can take the run. Fix: run eukhe and type /login anthropic",
                None,
            ),
        ];
        assert_eq!(
            reports,
            [
                Some(
                    "cloudflare-ai-gateway has no credentials, and no other configured model took the turn."
                        .to_string()
                ),
                Some(
                    "anthropic has no credentials, and no other configured model took the turn."
                        .to_string()
                ),
                Some("No other configured model took the turn.".to_string()),
                Some("Anthropic could not check the login: a fault on its side.".to_string()),
                Some("The provider could not check the login: a fault on its side.".to_string()),
                Some("No other configured model took the turn.".to_string()),
                Some("The turn goes on by itself at the reset.".to_string()),
                None,
                None,
            ]
        );
    }
}
