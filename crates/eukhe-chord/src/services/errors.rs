//! Service errors that may cross a remote boundary (port of
//! `services/errors.ts`).

use std::fmt;
use std::sync::Arc;

/// The codes a [`RemoteServiceError`] may carry across a service boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RemoteServiceErrorCode {
    /// `"service_not_allowed"`.
    ServiceNotAllowed,
    /// `"service_not_found"`.
    ServiceNotFound,
    /// `"service_mode_mismatch"`.
    ServiceModeMismatch,
    /// `"service_member_not_found"`.
    ServiceMemberNotFound,
    /// `"service_member_mismatch"`.
    ServiceMemberMismatch,
    /// `"service_instance_not_found"`.
    ServiceInstanceNotFound,
    /// `"service_stale_instance"`.
    ServiceStaleInstance,
    /// `"service_invalid_value"`.
    ServiceInvalidValue,
}

/// Every [`RemoteServiceErrorCode`] in TS declaration order
/// (`REMOTE_SERVICE_ERROR_CODES`).
pub const REMOTE_SERVICE_ERROR_CODES: [RemoteServiceErrorCode; 8] = [
    RemoteServiceErrorCode::ServiceNotAllowed,
    RemoteServiceErrorCode::ServiceNotFound,
    RemoteServiceErrorCode::ServiceModeMismatch,
    RemoteServiceErrorCode::ServiceMemberNotFound,
    RemoteServiceErrorCode::ServiceMemberMismatch,
    RemoteServiceErrorCode::ServiceInstanceNotFound,
    RemoteServiceErrorCode::ServiceStaleInstance,
    RemoteServiceErrorCode::ServiceInvalidValue,
];

impl RemoteServiceErrorCode {
    /// The wire string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ServiceNotAllowed => "service_not_allowed",
            Self::ServiceNotFound => "service_not_found",
            Self::ServiceModeMismatch => "service_mode_mismatch",
            Self::ServiceMemberNotFound => "service_member_not_found",
            Self::ServiceMemberMismatch => "service_member_mismatch",
            Self::ServiceInstanceNotFound => "service_instance_not_found",
            Self::ServiceStaleInstance => "service_stale_instance",
            Self::ServiceInvalidValue => "service_invalid_value",
        }
    }

    /// Parse a wire string (TS `isRemoteServiceErrorCode`).
    #[must_use]
    pub fn parse(value: &str) -> Option<Self> {
        REMOTE_SERVICE_ERROR_CODES
            .into_iter()
            .find(|code| code.as_str() == value)
    }
}

impl fmt::Display for RemoteServiceErrorCode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// Whether `value` is a remote service error code string.
#[must_use]
pub fn is_remote_service_error_code(value: &str) -> bool {
    RemoteServiceErrorCode::parse(value).is_some()
}

/// A service failure with a code that may cross a remote boundary. Its JS
/// `name` is `"RemoteServiceError"`.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("{message}")]
pub struct RemoteServiceError {
    code: RemoteServiceErrorCode,
    message: Arc<str>,
}

impl RemoteServiceError {
    /// The JS error `name`.
    pub const NAME: &'static str = "RemoteServiceError";

    /// A new error.
    #[must_use]
    pub fn new(code: RemoteServiceErrorCode, message: impl Into<Arc<str>>) -> Self {
        Self {
            code,
            message: message.into(),
        }
    }

    /// The code.
    #[must_use]
    pub fn code(&self) -> RemoteServiceErrorCode {
        self.code
    }

    /// The message.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}
