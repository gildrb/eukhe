//! Tool declarations sent to providers.

use indexmap::IndexMap;
use serde::de::Error as _;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::string_enum::string_enum;
use super::ToolSchema;

string_enum! {
    /// `OpenAI` grammar variants for constrained sampling.
    pub enum GrammarFormat {
        OpenAILark => "openai_lark",
        OpenAIRegex => "openai_regex",
    }
}

/// TS `Partial<Record<GrammarFormat, string>>`.
pub type GrammarVariants = IndexMap<GrammarFormat, String>;

string_enum! {
    /// How strictly a JSON-schema constrained-sampling request applies.
    pub enum JsonSchemaStrictness {
        Prefer => "prefer",
        Require => "require",
    }
}

/// Optional provider-side constrained sampling config for a tool.
///
/// `json_schema` roughly maps to `strict` in APIs that implement it as
/// JSON-schema constrained sampling. Grammar variants let callers provide
/// provider-specific encodings of the same intended language.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ConstrainedSamplingConfig {
    #[serde(rename = "json_schema")]
    JsonSchema { strict: JsonSchemaStrictness },
    #[serde(rename = "grammar")]
    Grammar { variants: GrammarVariants },
}

/// TS `false | ConstrainedSamplingConfig` (`Tool.constrainedSampling`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ToolConstrainedSampling {
    /// `false`: constrained sampling explicitly disabled.
    Disabled,
    Config(ConstrainedSamplingConfig),
}

impl Serialize for ToolConstrainedSampling {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Disabled => serializer.serialize_bool(false),
            Self::Config(config) => config.serialize(serializer),
        }
    }
}

impl<'de> Deserialize<'de> for ToolConstrainedSampling {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Wire {
            Flag(bool),
            Config(ConstrainedSamplingConfig),
        }
        match Wire::deserialize(deserializer)? {
            Wire::Flag(false) => Ok(Self::Disabled),
            Wire::Flag(true) => Err(D::Error::custom(
                "constrainedSampling must be false or a constrained sampling config",
            )),
            Wire::Config(config) => Ok(Self::Config(config)),
        }
    }
}

/// A tool definition. `parameters` is the tool's parameter schema: wire JSON
/// identical to what `TypeBox` serializes, plus its `TypeBox` markers when
/// built with `eukhe_pi_ai::typebox::Type`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Tool {
    pub name: String,
    pub description: String,
    pub parameters: ToolSchema,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub constrained_sampling: Option<ToolConstrainedSampling>,
}

/// A reference to a tool by name (`toolsRemoved`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ToolReference {
    pub name: String,
}
