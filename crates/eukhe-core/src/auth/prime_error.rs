//! Why a Prime API exchange failed: the transport ([`PrimeHttpError`]),
//! the access check ([`PrimeCheckError`]), the team list
//! ([`PrimeTeamsError`]) and the whole login ([`PrimeLoginError`]). Each
//! keeps the status and body the API answered; the login panel renders
//! the text once.

use super::failure_text::{response_snippet, transport_failure};
use super::prime_inference::{read_response_message, PrimeAccessFailure};

/// Why one Prime API request gave no answer.
#[derive(Debug, thiserror::Error)]
pub enum PrimeHttpError {
    /// The HTTP client could not be built.
    #[error("{0}")]
    Client(#[source] reqwest::Error),
    /// The request ran past its timeout.
    #[error("Prime Inference request timed out after {timeout_ms} ms")]
    TimedOut {
        timeout_ms: u64,
        #[source]
        source: reqwest::Error,
    },
    /// The request failed in transport (its cause chain renders).
    #[error("{}", transport_failure(.0))]
    Transport(#[source] reqwest::Error),
    /// The response body could not be read.
    #[error("{0}")]
    Body(#[source] reqwest::Error),
}

/// Why the `whoami` access check could not run.
#[derive(Debug, thiserror::Error)]
pub enum PrimeCheckError {
    #[error(transparent)]
    Http(#[from] PrimeHttpError),
    /// The body is not a JSON object.
    #[error(
        "Prime whoami returned an invalid response (HTTP {status}): {}",
        response_snippet(body)
    )]
    Invalid {
        status: u16,
        body: String,
        #[source]
        source: Option<serde_json::Error>,
    },
}

/// Why the team list could not be read.
#[derive(Debug, thiserror::Error)]
pub enum PrimeTeamsError {
    #[error(transparent)]
    Http(#[from] PrimeHttpError),
    /// The API answered a non-2xx status.
    #[error(
        "Failed to fetch Prime teams (HTTP {status}): {}",
        read_response_message(*status, body)
    )]
    Status { status: u16, body: String },
    /// The body is not a JSON object.
    #[error(
        "Prime teams returned an invalid response (HTTP {status}): {}",
        response_snippet(body)
    )]
    Invalid {
        status: u16,
        body: String,
        #[source]
        source: Option<serde_json::Error>,
    },
    /// The body carries no `data` array.
    #[error("Prime teams response missing team data")]
    MissingTeams,
}

/// Why the Prime Inference login gave no key.
#[derive(Debug, thiserror::Error)]
pub enum PrimeLoginError {
    #[error(transparent)]
    Http(#[from] PrimeHttpError),
    /// An access check could not run.
    #[error(transparent)]
    Check(#[from] PrimeCheckError),
    /// The resulting key lacks Prime Inference access.
    #[error("Prime API key does not have Prime Inference access ({})", .0.format())]
    Denied(PrimeAccessFailure),
    /// The RSA keypair could not be generated.
    #[error("{0}")]
    KeyPair(#[source] rsa::Error),
    /// The public key could not be encoded as PEM.
    #[error("{0}")]
    PublicKey(#[source] rsa::pkcs8::spki::Error),
    /// The challenge request answered a non-2xx status.
    #[error(
        "Failed to generate Prime login challenge (HTTP {status}): {}",
        read_response_message(*status, body)
    )]
    ChallengeStatus { status: u16, body: String },
    /// The challenge body is not a JSON object.
    #[error(
        "Prime login challenge returned an invalid response (HTTP {status}): {}",
        response_snippet(body)
    )]
    ChallengeInvalid {
        status: u16,
        body: String,
        #[source]
        source: Option<serde_json::Error>,
    },
    /// The challenge body lacks the challenge or the status token.
    #[error("Prime login challenge response missing required fields")]
    ChallengeFields,
    /// The status poll answered 404.
    #[error("Prime login challenge expired")]
    Expired,
    /// The status poll answered another non-2xx status.
    #[error(
        "Failed to check Prime login status (HTTP {status}): {}",
        read_response_message(*status, body)
    )]
    PollStatus { status: u16, body: String },
    /// The status body is not a JSON object.
    #[error(
        "Prime login status returned an invalid response (HTTP {status}): {}",
        response_snippet(body)
    )]
    PollInvalid {
        status: u16,
        body: String,
        #[source]
        source: Option<serde_json::Error>,
    },
    #[error("Prime login challenge result could not be decoded")]
    ResultDecode(#[source] base64::DecodeError),
    #[error("Prime login challenge result could not be decrypted")]
    ResultDecrypt(#[source] rsa::Error),
    #[error("Prime login challenge result is not UTF-8")]
    ResultUtf8(#[source] std::string::FromUtf8Error),
}
