//! Legacy extension OAuth callback types, retained only for coding-agent
//! extension compatibility. Port of `compat/extension-oauth-types.ts`.

use std::fmt;

use eukhe_chord::context::AbortSignal;
use futures::future::BoxFuture;
use serde::{Deserialize, Serialize};

pub use crate::auth::OAuthCredentials;
use crate::utils::diagnostics::Thrown;

/// Legacy extension OAuth prompt.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OAuthPrompt {
    pub message: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub placeholder: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allow_empty: Option<bool>,
}

/// Legacy extension OAuth authorization link.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OAuthAuthInfo {
    pub url: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instructions: Option<String>,
}

/// Legacy extension OAuth device-code notification.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OAuthDeviceCodeInfo {
    pub user_code: String,
    pub verification_uri: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub interval_seconds: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expires_in_seconds: Option<f64>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OAuthSelectOption {
    pub id: String,
    pub label: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OAuthSelectPrompt {
    pub message: String,
    pub options: Vec<OAuthSelectOption>,
}

/// Callback surface retained only for coding-agent extension compatibility:
/// TS `OAuthLoginCallbacks`. Optional TS callbacks are methods returning
/// `None` when absent.
pub trait OAuthLoginCallbacks: Send + Sync {
    fn on_auth(&self, info: OAuthAuthInfo);
    fn on_device_code(&self, info: OAuthDeviceCodeInfo);
    fn on_prompt(&self, prompt: OAuthPrompt) -> BoxFuture<'_, Result<String, Thrown>>;
    /// Optional in TS; the default ignores progress.
    fn on_progress(&self, message: &str) {
        let _ = message;
    }
    /// Absent by default.
    fn on_manual_code_input(&self) -> Option<BoxFuture<'_, Result<String, Thrown>>> {
        None
    }
    fn on_select(&self, prompt: OAuthSelectPrompt)
        -> BoxFuture<'_, Result<Option<String>, Thrown>>;
    fn signal(&self) -> Option<AbortSignal> {
        None
    }
}

impl fmt::Debug for dyn OAuthLoginCallbacks {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("OAuthLoginCallbacks")
            .finish_non_exhaustive()
    }
}
