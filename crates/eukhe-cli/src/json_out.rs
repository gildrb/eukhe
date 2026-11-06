//! JSON output: the machine format is a contract. A `--json` result is one
//! document on stdout — pretty-printed on a terminal, compact single-line
//! when stdout is piped — and a `--json` failure is one single-line error
//! document on stderr with stdout left empty. Serialization never passes
//! silently: an error comes back to the caller, which prints it and fails.

use std::io::IsTerminal as _;

/// Serialize `value` for stdout: pretty 2-space JSON on a TTY, compact
/// single-line JSON otherwise. The error is the caller's `Error:` text.
pub(crate) fn json_document<T: serde::Serialize>(value: &T) -> Result<String, String> {
    if std::io::stdout().is_terminal() {
        serde_json::to_string_pretty(value).map_err(|error| error.to_string())
    } else {
        serde_json::to_string(value).map_err(|error| error.to_string())
    }
}

/// Print one JSON document on stdout (the `--json` result contract).
///
/// # Errors
///
/// The document does not serialize (a contract bug, reported to the caller).
pub(crate) fn print_json_document<T: serde::Serialize>(value: &T) -> Result<(), String> {
    println!("{}", json_document(value)?);
    Ok(())
}

/// The single-line JSON error document a `--json` run prints on stderr
/// when it fails: `status` (`error` or `action_required` when only a
/// human step is missing), a stable `snake_case` `reason`, and the human
/// headline in `message`.
pub(crate) fn json_error_line(status: &str, reason: &str, message: &str) -> String {
    serde_json::json!({
        "status": status,
        "reason": reason,
        "message": message,
    })
    .to_string()
}

/// Print the JSON error document for a `--json` failure.
pub(crate) fn print_json_error(status: &str, reason: &str, message: &str) {
    eprintln!("{}", json_error_line(status, reason, message));
}
