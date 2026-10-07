//! Image-generation request and result types.

use serde::{Deserialize, Serialize};

use super::content::UserContentBlock;
use super::string_enum::string_enum;
use super::usage::Usage;
use super::{ImageApi, ProviderId};

/// TS `ImagesInputContent = TextContent | ImageContent`.
pub type ImagesInputContent = UserContentBlock;

/// TS `ImagesOutputContent = TextContent | ImageContent`.
pub type ImagesOutputContent = UserContentBlock;

/// Input of an image-generation request.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImagesContext {
    pub input: Vec<ImagesInputContent>,
}

string_enum! {
    /// Why an image-generation request stopped.
    pub enum ImagesStopReason {
        Stop => "stop",
        Error => "error",
        Aborted => "aborted",
    }
}

/// Result of an image-generation request.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AssistantImages {
    pub api: ImageApi,
    pub provider: ProviderId,
    pub model: String,
    pub output: Vec<ImagesOutputContent>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub response_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub usage: Option<Usage>,
    pub stop_reason: ImagesStopReason,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error_message: Option<String>,
    /// Unix timestamp in milliseconds.
    pub timestamp: u64,
}
