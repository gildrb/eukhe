//! `ModelsError`: the error the `Models` collection and its helpers throw.

use std::error::Error;
use std::fmt;

use super::diagnostics::{format_thrown_value, Thrown};

/// What kind of operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ModelsErrorCode {
    ModelSource,
    ModelValidation,
    Provider,
    Stream,
    Auth,
    Oauth,
}

impl ModelsErrorCode {
    /// The TS code string.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ModelSource => "model_source",
            Self::ModelValidation => "model_validation",
            Self::Provider => "provider",
            Self::Stream => "stream",
            Self::Auth => "auth",
            Self::Oauth => "oauth",
        }
    }
}

impl fmt::Display for ModelsErrorCode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// TS `class ModelsError extends Error` (`name: "ModelsError"`).
#[derive(Debug, Clone)]
pub struct ModelsError {
    pub code: ModelsErrorCode,
    /// The message, already carrying the cause's detail (callers surface the
    /// message only).
    pub message: String,
    pub cause: Option<Thrown>,
}

impl ModelsError {
    /// An error without a cause.
    #[must_use]
    pub fn new(code: ModelsErrorCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            cause: None,
        }
    }

    /// An error caused by `cause`; the cause's text is appended to the message
    /// unless the message already contains it.
    #[must_use]
    pub fn with_cause(code: ModelsErrorCode, message: impl Into<String>, cause: Thrown) -> Self {
        let message = with_cause_detail(message.into(), &cause);
        Self {
            code,
            message,
            cause: Some(cause),
        }
    }
}

impl fmt::Display for ModelsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl Error for ModelsError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.cause
            .as_deref()
            .map(|cause| cause as &(dyn Error + 'static))
    }
}

/// Callers surface `error.message` only, so keep the underlying reason in it.
fn with_cause_detail(message: String, cause: &Thrown) -> String {
    let formatted = format_thrown_value(cause);
    let detail = super::js::js_trim(&formatted);
    if detail.is_empty() || message.contains(detail) {
        return message;
    }
    format!("{message}: {detail}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::diagnostics::{ErrorObject, ThrownValue};

    #[test]
    fn keeps_the_cause_detail_in_the_message() {
        let error = ModelsError::with_cause(
            ModelsErrorCode::ModelSource,
            "Failed to load models",
            ErrorObject::new(" ENOENT: no such file ").thrown(),
        );
        assert_eq!(
            error.to_string(),
            "Failed to load models: ENOENT: no such file"
        );
        assert!(error.source().is_some());
        assert_eq!(error.code.as_str(), "model_source");
    }

    #[test]
    fn skips_empty_or_repeated_cause_detail() {
        let repeated = ModelsError::with_cause(
            ModelsErrorCode::Provider,
            "Request failed: timeout",
            ThrownValue::string("timeout").thrown(),
        );
        assert_eq!(repeated.message, "Request failed: timeout");
        let empty = ModelsError::with_cause(
            ModelsErrorCode::Stream,
            "Stream failed",
            ThrownValue::string("  ").thrown(),
        );
        assert_eq!(empty.message, "Stream failed");
        assert!(ModelsError::new(ModelsErrorCode::Oauth, "x")
            .cause
            .is_none());
    }
}
