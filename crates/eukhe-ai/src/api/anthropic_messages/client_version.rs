//! The client version of subscription (OAuth) requests: the
//! `claude-cli/<version> (external, cli)` User-Agent and the billing
//! header's `cc_version`. Anthropic refuses a model the version is too old
//! for: `400 invalid_request_error`, error code
//! `claude_code_version_too_old`, its message naming the version the model
//! requires ("version 2.1.300 or newer is required"). A refusal naming a
//! newer version than the request sent sends the request again with it, and
//! the provider's [`ClientVersion`] keeps that version for its later
//! requests; a refusal past that is reported with its cause
//! ([`refusal_message`]).

use std::sync::{Arc, Mutex, PoisonError};

/// The version sent first: the client's newest npm release, `2.1.325`.
pub(crate) const PINNED: &str = "2.1.325";

/// The client version one provider's subscription requests send: [`PINNED`],
/// or the newest version a refusal named. Clones share it; each provider
/// built with `anthropic_messages_api` owns one, so a session's later
/// requests send the version its first refused request learned.
#[derive(Debug, Clone)]
pub struct ClientVersion(Arc<Mutex<String>>);

impl Default for ClientVersion {
    fn default() -> Self {
        Self(Arc::new(Mutex::new(PINNED.to_owned())))
    }
}

impl ClientVersion {
    /// The version the next request sends.
    pub(crate) fn current(&self) -> String {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    /// Keeps `required` when it is newer than the version held (concurrent
    /// refusals never move it back).
    pub(crate) fn learn(&self, required: &str) {
        let mut held = self.0.lock().unwrap_or_else(PoisonError::into_inner);
        if semver(required) > semver(&held) {
            required.clone_into(&mut *held);
        }
    }
}

/// The error code of the refusal.
const TOO_OLD_CODE: &str = "claude_code_version_too_old";

/// The text that follows the required version in the refusal's message.
const REQUIRED_SUFFIX: &str = " or newer is required";

/// What a failed request's error says about the version it sent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Refusal {
    /// The failure is not a version refusal.
    Other,
    /// Refused, naming a version newer than the one sent: retry with it.
    Retry { required: String },
    /// Refused with no newer version to retry with: none named, or one the
    /// request already sent.
    Final { required: Option<String> },
}

/// The refusal in the failure text `error` of a request that sent `sent`.
pub(crate) fn refusal(error: &str, sent: &str) -> Refusal {
    if !error.contains(TOO_OLD_CODE) {
        return Refusal::Other;
    }
    match required_version(error) {
        Some(required) if semver(required) > semver(sent) => Refusal::Retry {
            required: required.to_owned(),
        },
        required => Refusal::Final {
            required: required.map(str::to_owned),
        },
    }
}

/// The user-facing error of a final refusal: the cause, then the
/// provider's error `detail`.
pub(crate) fn refusal_message(sent: &str, required: Option<&str>, detail: &str) -> String {
    let requirement = required.map_or_else(String::new, |required| {
        format!(" (it requires {required} or newer)")
    });
    format!(
        "Anthropic refused the subscription request: client version {sent} is too old for this model{requirement}. Run `eukhe update`. Provider error: {detail}"
    )
}

/// The `X.Y.Z` before " or newer is required", when it is a version.
fn required_version(error: &str) -> Option<&str> {
    let lower = error.to_ascii_lowercase();
    let end = lower.find(REQUIRED_SUFFIX)?;
    let start = error[..end].rfind(' ').map_or(0, |space| space + 1);
    let version = &error[start..end];
    semver(version).map(|_| version)
}

/// `X.Y.Z` as numbers, compared part by part.
fn semver(version: &str) -> Option<(u64, u64, u64)> {
    let mut parts = version.split('.').map(str::parse::<u64>);
    match (parts.next(), parts.next(), parts.next(), parts.next()) {
        (Some(Ok(major)), Some(Ok(minor)), Some(Ok(patch)), None) => Some((major, minor, patch)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const REFUSAL: &str = r#"400 {"type":"error","error":{"type":"invalid_request_error","message":"Claude Code 2.1.280 does not support this model; version 2.1.300 or newer is required.","details":{"error_code":"claude_code_version_too_old"}}}"#;

    #[test]
    fn a_refusal_naming_a_newer_version_retries_with_it() {
        assert_eq!(
            refusal(REFUSAL, "2.1.280"),
            Refusal::Retry {
                required: "2.1.300".to_owned()
            }
        );
    }

    #[test]
    fn a_refusal_of_the_named_version_or_without_one_is_final() {
        assert_eq!(
            refusal(REFUSAL, "2.1.300"),
            Refusal::Final {
                required: Some("2.1.300".to_owned())
            }
        );
        assert_eq!(
            refusal(
                r#"400 {"details":{"error_code":"claude_code_version_too_old"}}"#,
                "2.1.321"
            ),
            Refusal::Final { required: None }
        );
    }

    #[test]
    fn other_errors_are_not_refusals() {
        assert_eq!(
            refusal(r#"400 {"error":{"message":"stop"}}"#, "2.1.321"),
            Refusal::Other
        );
    }

    #[test]
    fn versions_compare_by_number() {
        assert!(semver("2.1.1000") > semver("2.1.321"));
        assert_eq!(semver("2.1"), None);
        assert_eq!(semver("v2.1.3"), None);
    }

    #[test]
    fn a_learned_version_only_moves_forward_and_clones_share_it() {
        let version = ClientVersion::default();
        let shared = version.clone();
        version.learn("9.0.0");
        shared.learn("3.0.0");
        assert_eq!(shared.current(), "9.0.0");
    }
}
