//! Structured classifier request and result types.

use indexmap::IndexMap;
use serde::ser::SerializeMap;
use serde::{Deserialize, Serialize, Serializer};

use super::string_enum::string_enum;
use super::usage::Usage;
use super::{ClassifierApi, ImageContent, JsonObject, ProviderId};

/// Criteria of a boolean question.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassifierBoolCriteria {
    #[serde(rename = "true")]
    pub when_true: String,
    #[serde(rename = "false")]
    pub when_false: String,
}

/// TS `ClassifierQuestion`, tagged by `type`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ClassifierQuestion {
    /// Pick one of the named choices.
    #[serde(rename = "choice")]
    Choice {
        instructions: String,
        criteria: IndexMap<String, String>,
    },
    /// Score along the ordered criteria.
    #[serde(rename = "score")]
    Score {
        instructions: String,
        criteria: Vec<String>,
    },
    /// Answer true or false.
    #[serde(rename = "bool")]
    Bool {
        instructions: String,
        criteria: ClassifierBoolCriteria,
    },
}

/// Input of a classifier request.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ClassifierContext {
    pub state: JsonObject,
    /// Images judged together with `state`. Only models whose `input`
    /// includes `"image"` accept them; other models return an error result.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub images: Option<Vec<ImageContent>>,
    pub questions: IndexMap<String, ClassifierQuestion>,
}

/// Serialize a probability map with JS number formatting.
fn serialize_probabilities<S: Serializer>(
    probabilities: &IndexMap<String, f64>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    struct JsNumber(f64);
    impl Serialize for JsNumber {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            super::js_number::serialize(&self.0, serializer)
        }
    }
    let mut map = serializer.serialize_map(Some(probabilities.len()))?;
    for (key, value) in probabilities {
        map.serialize_entry(key, &JsNumber(*value))?;
    }
    map.end()
}

/// TS `ClassifierAnswer`, tagged by `type`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ClassifierAnswer {
    #[serde(rename = "choice")]
    Choice {
        choice: String,
        #[serde(serialize_with = "serialize_probabilities")]
        probabilities: IndexMap<String, f64>,
        #[serde(serialize_with = "super::js_number::serialize")]
        confidence: f64,
    },
    #[serde(rename = "score")]
    Score {
        #[serde(serialize_with = "super::js_number::serialize")]
        score: f64,
        #[serde(serialize_with = "super::js_number::serialize")]
        confidence: f64,
    },
    #[serde(rename = "bool")]
    Bool {
        #[serde(serialize_with = "super::js_number::serialize")]
        probability: f64,
    },
}

string_enum! {
    /// Why a classifier request stopped.
    pub enum ClassifierStopReason {
        Stop => "stop",
        Error => "error",
        Aborted => "aborted",
    }
}

/// Result of a classifier request.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ClassifierResult {
    pub api: ClassifierApi,
    pub provider: ProviderId,
    pub model: String,
    pub answers: IndexMap<String, ClassifierAnswer>,
    /// Token usage and its cost at the model's catalog price, when the service reports token counts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub usage: Option<Usage>,
    pub stop_reason: ClassifierStopReason,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error_message: Option<String>,
    /// Unix timestamp in milliseconds.
    pub timestamp: u64,
}
