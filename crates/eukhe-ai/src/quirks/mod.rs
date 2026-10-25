//! The quirks rulebook (docs/inference.md S6.1; model `bend/infer.bend`
//! section 1): which wire settings, thinking ladders and service tiers a
//! model family, a model, and a host need, as data.
//!
//! A rule says: at a layer (a model family, a model, a host), for a target
//! id of that layer, directive `d` has value `v`. [`compile`] rejects a rule
//! with an unknown directive, a value of the wrong type, and two rules of
//! one layer, target and directive with different values. A lookup takes
//! the rule of the highest layer that applies (host over model over
//! family). Rust parses each value and numbers targets, directives and
//! values; the compiled core (`bend/ffi_quirks.bend`, a stepper that keeps
//! the rulebook) decides what compiles and answers each lookup. With no
//! rule that applies the answer is [`Answer::Unknown`],
//! never a guess: the caller (a wire API's compat resolver) applies its
//! own default, and the explicit `model.compat` wins over both. The answer
//! does not depend on the order of the rules.
//!
//! A model's query names one target per layer ([`Rulebook::query`]):
//! - family: the one family whose pattern matches the model, and whose
//!   revision range (when it has one) holds for the revision that the
//!   model id names ([`revision`]; an id that names no revision has the
//!   revision 0). A model that two families match is the error
//!   [`FamilyOverlap`], never a choice between them: the shipped rulebook
//!   is checked against every model of the compiled catalog
//!   ([`Rulebook::check_catalog`]), and a model outside it that two
//!   families match names no family (each family directive is then
//!   Unknown), reported once per model id;
//! - model: the model id;
//! - host: the host that names the model's wire API (an API that only one
//!   host speaks), else the host that names its provider id, else the host
//!   with the longest URL fragment in its base URL (ties: the smaller host
//!   id). One host per model: the signals do not combine, so a provider
//!   host keeps its settings whatever its base URL. A host of scope
//!   `capabilities` serves only capability lookups ([`Lookup`]): it may set
//!   only capability directives, and a wire lookup skips it as if it named
//!   nothing, so it never changes a request's wire settings.
//!
//! The rulebook also holds the service tiers ([`service_tiers`],
//! docs/inference.md S6.8): a table of the tiers that a provider honors
//! over one wire API, for every model or for the models of one family;
//! and the prices that a catalog row does not carry
//! ([`service_tier_multiplier`], [`cache_write_1h_multiplier`]); and the
//! default model of each provider ([`provider_default_model`]).
//!
//! The shipped rulebook is `rulebook.json`, compiled into the binary and
//! compiled once on first use.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::{LazyLock, Mutex, PoisonError};

use eukhe_bend::rules::quirks as compiled;
use eukhe_bend::wire::WireError;
use eukhe_bend::{expect_core, Entry};
use regex::Regex;
use serde::Deserialize;
use serde_json::Value as JsonValue;

use crate::capabilities::{Capability, Dialect};
use crate::types::{
    MaxTokensField, Model, ModelThinkingLevel, SessionAffinityFormat, ThinkingFormat,
    ThinkingLevelMap,
};

mod prices;
mod provider_defaults;
mod revision;
mod tiers;

pub use prices::{cache_write_1h_multiplier, service_tier_multiplier};
pub use provider_defaults::{provider_default_model, provider_defaults};
pub use tiers::{service_tiers, supports_service_tier};

#[cfg(test)]
mod tests;

/// The layer of a rule. A higher layer wins.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Layer {
    Family,
    Model,
    Host,
}

impl Layer {
    const fn index(self) -> usize {
        match self {
            Self::Family => 0,
            Self::Model => 1,
            Self::Host => 2,
        }
    }

    /// The layer as the compiled core reads it.
    const fn compiled(self) -> compiled::Layer {
        match self {
            Self::Family => compiled::Layer::Family,
            Self::Model => compiled::Layer::Model,
            Self::Host => compiled::Layer::Host,
        }
    }
}

impl fmt::Display for Layer {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Family => "family",
            Self::Model => "model",
            Self::Host => "host",
        })
    }
}

/// A setting a rule can give. Each directive takes one [`ValueKind`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Directive {
    /// openai-completions: the host accepts the `store` field.
    Store,
    /// openai-completions: the host accepts the `developer` role.
    DeveloperRole,
    /// openai-completions: model id prefixes that accept the `developer`
    /// role on this host even when `developer_role` is false.
    DeveloperRolePrefixes,
    /// openai-completions: the host accepts `reasoning_effort`.
    ReasoningEffort,
    /// openai-completions: the field that carries the output cap.
    MaxTokensField,
    /// openai-completions: assistant messages need `reasoning_content`.
    ReasoningContentOnAssistant,
    /// openai-completions: the reasoning request format.
    ThinkingFormat,
    /// openai-completions: model id prefixes that take Anthropic-style
    /// `cache_control` marks on this host.
    AnthropicCacheControlPrefixes,
    /// The host takes session-affinity headers.
    SessionAffinityHeaders,
    /// The session-affinity header format.
    SessionAffinityFormat,
    /// The host accepts long (1h) prompt-cache retention.
    LongCacheRetention,
    /// The host accepts strict JSON-schema tools.
    StrictTools,
    /// The most tools one request may send with strict schemas.
    StrictCap,
    /// Google: the model enforces required parameters in the `VALIDATED`
    /// function-calling mode (Gemini 3 and later).
    GoogleValidatedTools,
    /// openai-completions: the model renders the Qwen chat template.
    QwenChatTemplate,
    /// The model takes adaptive thinking (`thinking.type: adaptive` with an
    /// effort), on Bedrock and on Anthropic Messages. An explicit
    /// `compat.forceAdaptiveThinking` of the model wins over it.
    AdaptiveThinking,
    /// Bedrock: the adaptive model takes `thinking.block_binding`.
    ThinkingBlockBinding,
    /// Bedrock: the model takes `cachePoint` blocks (prompt caching).
    PromptCaching,
    /// `OpenAI` Responses: the model takes the explicit prompt-cache controls
    /// (`prompt_cache_breakpoint: {"mode": "explicit"}` on `input_text`
    /// items and `reasoning.context: "all_turns"`).
    ExplicitCacheBreakpoints,
    /// Google: the model takes the discrete `thinkingLevel` control (true)
    /// or the token `thinkingBudget` control (false).
    GoogleThinkingLevel,
    /// Google: the thinking budget of each level. `minimal` is the smallest
    /// budget the model accepts and `high` the largest.
    ThinkingBudgets,
    /// The host supports a native forced tool choice.
    ToolChoiceNative,
    /// Forcing a tool choice costs no prompt-cache invalidation.
    ToolChoiceFree,
    /// openai-completions: the server streams prompt-processing progress
    /// (`prompt_progress` chunks) when the request sets `return_progress`
    /// (llama.cpp `llama-server`). A server feature, not a wire setting: a
    /// host of scope `capabilities` may set it, and a capability lookup
    /// reads it.
    PromptProgress,
    /// The thinking ladder of a model (docs/inference.md S10): the levels
    /// it offers and their wire values, as a `thinkingLevelMap` (a level
    /// with a string is offered with that wire value, a `null` level is
    /// absent, a missing level keeps the default rule). A model's explicit
    /// `thinkingLevelMap` wins over it (`models::thinking_level_map`).
    ThinkingLadder,
    /// The endpoint dialect that serves a provider capability
    /// ([`Capability`]), or `false`: the host or model does not have it.
    Endpoint(Capability),
}

impl Directive {
    /// Every directive, in declaration order.
    pub const ALL: &'static [Self] = &[
        Self::Store,
        Self::DeveloperRole,
        Self::DeveloperRolePrefixes,
        Self::ReasoningEffort,
        Self::MaxTokensField,
        Self::ReasoningContentOnAssistant,
        Self::ThinkingFormat,
        Self::AnthropicCacheControlPrefixes,
        Self::SessionAffinityHeaders,
        Self::SessionAffinityFormat,
        Self::LongCacheRetention,
        Self::StrictTools,
        Self::StrictCap,
        Self::GoogleValidatedTools,
        Self::QwenChatTemplate,
        Self::AdaptiveThinking,
        Self::ThinkingBlockBinding,
        Self::PromptCaching,
        Self::ExplicitCacheBreakpoints,
        Self::GoogleThinkingLevel,
        Self::ThinkingBudgets,
        Self::ToolChoiceNative,
        Self::ToolChoiceFree,
        Self::PromptProgress,
        Self::ThinkingLadder,
        Self::Endpoint(Capability::CountTokens),
        Self::Endpoint(Capability::ListModels),
        Self::Endpoint(Capability::Embed),
        Self::Endpoint(Capability::GenerateImage),
        Self::Endpoint(Capability::Tokenize),
        Self::Endpoint(Capability::Usage),
        Self::Endpoint(Capability::WebSearch),
        Self::Endpoint(Capability::Compact),
    ];

    /// The name rules use.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Store => "store",
            Self::DeveloperRole => "developer_role",
            Self::DeveloperRolePrefixes => "developer_role_prefixes",
            Self::ReasoningEffort => "reasoning_effort",
            Self::MaxTokensField => "max_tokens_field",
            Self::ReasoningContentOnAssistant => "reasoning_content_on_assistant",
            Self::ThinkingFormat => "thinking_format",
            Self::AnthropicCacheControlPrefixes => "anthropic_cache_control_prefixes",
            Self::SessionAffinityHeaders => "session_affinity_headers",
            Self::SessionAffinityFormat => "session_affinity_format",
            Self::LongCacheRetention => "long_cache_retention",
            Self::StrictTools => "strict_tools",
            Self::StrictCap => "strict_cap",
            Self::GoogleValidatedTools => "google_validated_tools",
            Self::QwenChatTemplate => "qwen_chat_template",
            Self::AdaptiveThinking => "adaptive_thinking",
            Self::ThinkingBlockBinding => "thinking_block_binding",
            Self::PromptCaching => "prompt_caching",
            Self::ExplicitCacheBreakpoints => "explicit_cache_breakpoints",
            Self::GoogleThinkingLevel => "google_thinking_level",
            Self::ThinkingBudgets => "thinking_budgets",
            Self::ToolChoiceNative => "tool_choice_native",
            Self::ToolChoiceFree => "tool_choice_free",
            Self::PromptProgress => "prompt_progress",
            Self::ThinkingLadder => "thinking_ladder",
            Self::Endpoint(capability) => capability.as_str(),
        }
    }

    /// The directive's id in the compiled core: its index in [`Self::ALL`]
    /// (the core's known directives are `0 .. ALL.len()`).
    fn id(self) -> u64 {
        Self::ALL
            .iter()
            .position(|directive| *directive == self)
            .and_then(|index| u64::try_from(index).ok())
            .unwrap_or(u64::MAX)
    }

    /// The directive named `name`.
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL
            .iter()
            .copied()
            .find(|directive| directive.as_str() == name)
    }

    /// The capability this directive gives the endpoint of; `None` for a
    /// wire directive.
    #[must_use]
    pub const fn capability(self) -> Option<Capability> {
        match self {
            Self::Endpoint(capability) => Some(capability),
            Self::Store
            | Self::DeveloperRole
            | Self::DeveloperRolePrefixes
            | Self::ReasoningEffort
            | Self::MaxTokensField
            | Self::ReasoningContentOnAssistant
            | Self::ThinkingFormat
            | Self::AnthropicCacheControlPrefixes
            | Self::SessionAffinityHeaders
            | Self::SessionAffinityFormat
            | Self::LongCacheRetention
            | Self::StrictTools
            | Self::StrictCap
            | Self::GoogleValidatedTools
            | Self::QwenChatTemplate
            | Self::AdaptiveThinking
            | Self::ThinkingBlockBinding
            | Self::PromptCaching
            | Self::ExplicitCacheBreakpoints
            | Self::GoogleThinkingLevel
            | Self::ThinkingBudgets
            | Self::ToolChoiceNative
            | Self::ToolChoiceFree
            | Self::PromptProgress
            | Self::ThinkingLadder => None,
        }
    }

    /// The type of the directive's value.
    #[must_use]
    pub const fn kind(self) -> ValueKind {
        match self {
            Self::Store
            | Self::DeveloperRole
            | Self::ReasoningEffort
            | Self::ReasoningContentOnAssistant
            | Self::SessionAffinityHeaders
            | Self::LongCacheRetention
            | Self::StrictTools
            | Self::GoogleValidatedTools
            | Self::QwenChatTemplate
            | Self::AdaptiveThinking
            | Self::ThinkingBlockBinding
            | Self::PromptCaching
            | Self::ExplicitCacheBreakpoints
            | Self::GoogleThinkingLevel
            | Self::ToolChoiceNative
            | Self::ToolChoiceFree
            | Self::PromptProgress => ValueKind::Bool,
            Self::DeveloperRolePrefixes | Self::AnthropicCacheControlPrefixes => {
                ValueKind::Prefixes
            }
            Self::MaxTokensField => ValueKind::MaxTokensField,
            Self::ThinkingFormat => ValueKind::ThinkingFormat,
            Self::SessionAffinityFormat => ValueKind::SessionAffinityFormat,
            Self::StrictCap => ValueKind::Count,
            Self::ThinkingLadder => ValueKind::ThinkingLadder,
            Self::ThinkingBudgets => ValueKind::ThinkingBudgets,
            Self::Endpoint(capability) => ValueKind::Endpoint(capability),
        }
    }
}

/// The type of a directive's value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueKind {
    /// A JSON boolean.
    Bool,
    /// A JSON non-negative integer.
    Count,
    /// A JSON array of strings.
    Prefixes,
    /// A `MaxTokensField` wire string.
    MaxTokensField,
    /// A `ThinkingFormat` wire string.
    ThinkingFormat,
    /// A `SessionAffinityFormat` wire string.
    SessionAffinityFormat,
    /// A `thinkingLevelMap`: an object from level names to a wire string
    /// or `null`.
    ThinkingLadder,
    /// A `thinkingBudgets` object with all four levels set, each level at
    /// least the one before it (`minimal` ≤ `low` ≤ `medium` ≤ `high`).
    ThinkingBudgets,
    /// A [`Dialect`] wire string that implements the capability, or `false`.
    Endpoint(Capability),
}

impl ValueKind {
    /// `raw` as a value of this kind.
    #[must_use]
    pub fn parse(self, raw: &JsonValue) -> Option<Value> {
        match self {
            Self::Bool => raw.as_bool().map(Value::Bool),
            Self::Count => raw
                .as_u64()
                .and_then(|count| u32::try_from(count).ok())
                .map(Value::Count),
            Self::Prefixes => raw
                .as_array()?
                .iter()
                .map(|item| item.as_str().map(str::to_owned))
                .collect::<Option<Vec<_>>>()
                .map(Value::Prefixes),
            Self::MaxTokensField => raw
                .as_str()
                .and_then(MaxTokensField::parse)
                .map(Value::MaxTokensField),
            Self::ThinkingFormat => raw
                .as_str()
                .and_then(ThinkingFormat::parse)
                .map(Value::ThinkingFormat),
            Self::SessionAffinityFormat => raw
                .as_str()
                .and_then(SessionAffinityFormat::parse)
                .map(Value::SessionAffinityFormat),
            Self::ThinkingLadder => ThinkingLevelMap::deserialize(raw)
                .ok()
                .map(Value::ThinkingLadder),
            Self::ThinkingBudgets => LevelBudgets::deserialize(raw)
                .ok()
                .filter(|budgets| {
                    budgets.minimal <= budgets.low
                        && budgets.low <= budgets.medium
                        && budgets.medium <= budgets.high
                })
                .map(Value::ThinkingBudgets),
            Self::Endpoint(capability) => match raw {
                JsonValue::Bool(false) => Some(Value::Endpoint(None)),
                JsonValue::String(name) => Dialect::parse(name)
                    .filter(|dialect| dialect.endpoint(capability).is_some())
                    .map(|dialect| Value::Endpoint(Some(dialect))),
                JsonValue::Null
                | JsonValue::Bool(true)
                | JsonValue::Number(_)
                | JsonValue::Array(_)
                | JsonValue::Object(_) => None,
            },
        }
    }
}

/// A directive's value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Count(u32),
    Prefixes(Vec<String>),
    MaxTokensField(MaxTokensField),
    ThinkingFormat(ThinkingFormat),
    SessionAffinityFormat(SessionAffinityFormat),
    /// A thinking ladder ([`Directive::ThinkingLadder`]).
    ThinkingLadder(ThinkingLevelMap),
    /// Thinking budgets ([`Directive::ThinkingBudgets`]).
    ThinkingBudgets(LevelBudgets),
    /// The dialect of a capability endpoint; `None`: unsupported.
    Endpoint(Option<Dialect>),
}

/// The token budgets of the four budget levels (`xhigh` and `max` take
/// `high`). A rule's budgets are ordered: each level is at least the one
/// before it, so `minimal` is the smallest budget and `high` the largest.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LevelBudgets {
    pub minimal: u64,
    pub low: u64,
    pub medium: u64,
    pub high: u64,
}

/// The answer of a lookup.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Answer<'a> {
    /// The value of the highest rule that applies.
    Known(&'a Value),
    /// No rule applies.
    Unknown,
}

/// One rule before compilation: one directive of one rulebook entry.
#[derive(Debug, Clone, PartialEq)]
pub struct RawRule {
    pub layer: Layer,
    pub target: String,
    pub directive: String,
    pub value: JsonValue,
}

/// Why a rulebook does not compile.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum QuirksError {
    #[error("the {layer} rule for `{target}` sets the unknown directive `{directive}`")]
    UnknownDirective {
        layer: Layer,
        target: String,
        directive: String,
    },
    #[error(
        "the {layer} rule for `{target}` sets `{directive}` to {value}, which is not a {kind:?}"
    )]
    BadValue {
        layer: Layer,
        target: String,
        directive: String,
        value: JsonValue,
        kind: ValueKind,
    },
    #[error("two {layer} rules for `{target}` set `{directive}` to {first} and {second}")]
    Clash {
        layer: Layer,
        target: String,
        directive: String,
        first: JsonValue,
        second: JsonValue,
    },
    #[error("the rulebook is not valid: {0}")]
    Format(String),
    #[error("family `{family}` has a bad pattern: {reason}")]
    BadPattern { family: String, reason: String },
    #[error("family `{family}` has a bad revision range: {reason}")]
    BadRevision { family: String, reason: String },
    #[error("two {layer} definitions have the id `{id}`")]
    DuplicateId { layer: Layer, id: String },
    #[error("`{key}` names two hosts: `{first}` and `{second}`")]
    SharedKey {
        key: String,
        first: String,
        second: String,
    },
    #[error("a {layer} rule targets `{target}`, which no {layer} definition names")]
    UndefinedTarget { layer: Layer, target: String },
    #[error("a service tier entry names the family `{family}`, which no family definition names")]
    UndefinedTierFamily { family: String },
    #[error("host `{host}` serves capability lookups only, but its rule sets `{directive}`")]
    WireDirectiveOnCapabilityHost { host: String, directive: String },
    #[error(transparent)]
    FamilyOverlap(#[from] FamilyOverlap),
}

/// What a host lookup is for ([`Rulebook::query`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lookup {
    /// The wire settings of a request: hosts of scope `capabilities` do not
    /// apply.
    Wire,
    /// The capability endpoints of a provider: every host applies.
    Capabilities,
}

/// Which lookups a host serves.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
enum HostScope {
    /// Wire and capability lookups.
    #[default]
    All,
    /// Capability lookups only: the host never changes a request's wire
    /// settings, and its rules may set only capability directives.
    Capabilities,
}

/// Two families that match one model ([`Rulebook::query`]).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("model `{model}` matches two families: `{first}` and `{second}`")]
pub struct FamilyOverlap {
    pub model: String,
    pub first: String,
    pub second: String,
}

/// Compiled rules: the compiled core keeps them (`bend/ffi_quirks.bend`)
/// and answers each lookup; Rust keeps the ids it gave the targets and the
/// values.
#[derive(Debug)]
pub struct Rules {
    book: Mutex<compiled::Book>,
    /// Per layer, the id of each target (from 1: 0 is no target).
    targets: [HashMap<String, u64>; 3],
    /// The value of each value id.
    values: Vec<Value>,
}

/// The value id of `value` in `values`, added when it is new: equal values
/// share an id, so the core sees two rules of one value as one value.
fn value_id(values: &mut Vec<Value>, value: Value) -> u64 {
    let index = values
        .iter()
        .position(|known| *known == value)
        .unwrap_or_else(|| {
            values.push(value);
            values.len() - 1
        });
    u64::try_from(index).unwrap_or(u64::MAX)
}

/// Compile `rules` in the compiled core: every directive known, every value
/// of its directive's type (parsed here), and no two rules of one layer,
/// target and directive with different values. The result does not depend
/// on the order of `rules`.
///
/// # Errors
///
/// Every rule that breaks one of those, in rule order: a clash names the
/// rule and the first later rule it clashes with.
pub fn compile(rules: &[RawRule]) -> Result<Rules, Vec<QuirksError>> {
    let mut targets: [HashMap<String, u64>; 3] = Default::default();
    let mut unknown: HashMap<&str, u64> = HashMap::new();
    let mut values = Vec::new();
    let mut facts = Vec::with_capacity(rules.len());
    // The index in `rules` of each rule of `facts`.
    let mut sources = Vec::with_capacity(rules.len());
    let mut errors: Vec<(usize, QuirksError)> = Vec::new();
    let known_count = Directive::ALL.len() as u64;
    for (index, rule) in rules.iter().enumerate() {
        let (directive, value) = if let Some(directive) = Directive::parse(&rule.directive) {
            let Some(value) = directive.kind().parse(&rule.value) else {
                errors.push((
                    index,
                    QuirksError::BadValue {
                        layer: rule.layer,
                        target: rule.target.clone(),
                        directive: rule.directive.clone(),
                        value: rule.value.clone(),
                        kind: directive.kind(),
                    },
                ));
                continue;
            };
            (directive.id(), value_id(&mut values, value))
        } else {
            // A name past the known directives: the core rejects it.
            let next = known_count + unknown.len() as u64;
            (*unknown.entry(&rule.directive).or_insert(next), 0)
        };
        let ids = &mut targets[rule.layer.index()];
        let next = ids.len() as u64 + 1;
        let target = *ids.entry(rule.target.clone()).or_insert(next);
        facts.push(compiled::Rule {
            layer: rule.layer.compiled(),
            target,
            directive,
            value,
        });
        sources.push(index);
    }
    let known: Vec<u64> = (0..known_count).collect();
    let (book, verdicts) = expect_core(Entry::Quirks, compiled::Book::open(&known, &facts));
    for (verdict, &index) in verdicts.into_iter().zip(&sources) {
        let rule = &rules[index];
        match verdict {
            compiled::Verdict::Fine => {}
            compiled::Verdict::UnknownDirective => errors.push((
                index,
                QuirksError::UnknownDirective {
                    layer: rule.layer,
                    target: rule.target.clone(),
                    directive: rule.directive.clone(),
                },
            )),
            compiled::Verdict::ClashesWith(other) => {
                let other = expect_core(
                    Entry::Quirks,
                    sources.get(other).ok_or(WireError::Malformed {
                        at: 0,
                        expected: "the index of a rule",
                    }),
                );
                errors.push((
                    index,
                    QuirksError::Clash {
                        layer: rule.layer,
                        target: rule.target.clone(),
                        directive: rule.directive.clone(),
                        first: rule.value.clone(),
                        second: rules[*other].value.clone(),
                    },
                ));
            }
        }
    }
    errors.sort_by_key(|(index, _)| *index);
    match book {
        Some(book) if errors.is_empty() => Ok(Rules {
            book: Mutex::new(book),
            targets,
            values,
        }),
        Some(_) | None => Err(errors.into_iter().map(|(_, error)| error).collect()),
    }
}

impl Rules {
    /// The value of `directive` for `query`, as the compiled core looks it
    /// up: the rule of the highest layer whose target the query names;
    /// [`Answer::Unknown`] when none does.
    #[must_use]
    pub fn lookup(&self, query: &Query<'_>, directive: Directive) -> Answer<'_> {
        let id = |layer: Layer, target: Option<&str>| {
            target
                .and_then(|target| self.targets[layer.index()].get(target))
                .copied()
                .unwrap_or(0)
        };
        let query = compiled::Query {
            family: id(Layer::Family, query.family),
            model: id(Layer::Model, Some(query.model)),
            host: id(Layer::Host, query.host),
        };
        let value = expect_core(
            Entry::Quirks,
            self.book
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .lookup(query, directive.id()),
        );
        match value {
            Some(value) => Answer::Known(expect_core(
                Entry::Quirks,
                usize::try_from(value)
                    .ok()
                    .and_then(|value| self.values.get(value))
                    .ok_or(WireError::Malformed {
                        at: 0,
                        expected: "a value id of the rulebook",
                    }),
            )),
            None => Answer::Unknown,
        }
    }
}

/// The target a query names at each layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Query<'a> {
    pub family: Option<&'a str>,
    pub model: &'a str,
    pub host: Option<&'a str>,
}

/// The fields of a model that a rulebook query reads: the id and name
/// (the family), the wire API, the provider and the base URL (the host).
/// Both model types give one ([`Model`] and the registry's
/// `eukhe_types::ai::Model`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModelKey<'a> {
    pub id: &'a str,
    pub name: &'a str,
    pub api: &'a str,
    pub provider: &'a str,
    pub base_url: &'a str,
}

impl<'a> From<&'a Model> for ModelKey<'a> {
    fn from(model: &'a Model) -> Self {
        Self {
            id: &model.id,
            name: &model.name,
            api: &model.api,
            provider: &model.provider,
            base_url: &model.base_url,
        }
    }
}

impl<'a> From<&'a eukhe_types::ai::Model> for ModelKey<'a> {
    fn from(model: &'a eukhe_types::ai::Model) -> Self {
        Self {
            id: &model.id,
            name: &model.name,
            api: &model.api,
            provider: &model.provider,
            base_url: &model.base_url,
        }
    }
}

/// The thinking defaults (docs/inference.md S10, the ladder 0). The
/// ladders are the levels a model offers where its ladder gives no entry,
/// in the wire API's own form: `reasoning` serves a reasoning model,
/// `plain` a model without reasoning (whose ladder has no effect).
/// `budgets` are the token budgets of the levels where neither the user's
/// `thinkingBudgets` nor a rule of the model gives one.
#[derive(Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ThinkingDefaults {
    pub reasoning: Vec<ModelThinkingLevel>,
    pub plain: Vec<ModelThinkingLevel>,
    #[serde(default)]
    pub budgets: LevelBudgets,
}

/// What a family pattern is matched against.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
enum MatchOn {
    /// The lowercased model id.
    Id,
    /// The lowercased model id and name, each also with separator runs
    /// (`[\s_.:]+`) replaced by `-` ([`match_candidates`]).
    Names,
}

/// A family's revision condition: the revision that the model id names
/// after `prefix` ([`revision::of`]; none is 0) is in `range`.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RevisionEntry {
    prefix: String,
    range: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FamilyEntry {
    id: String,
    on: MatchOn,
    #[serde(rename = "match")]
    pattern: String,
    #[serde(default)]
    revision: Option<RevisionEntry>,
    /// A regex that excludes a model the `match` pattern matches (on the
    /// same candidates), so two families stay disjoint without a lookahead.
    #[serde(default)]
    except: Option<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct HostEntry {
    id: String,
    #[serde(default)]
    apis: Vec<String>,
    #[serde(default)]
    providers: Vec<String>,
    #[serde(default)]
    urls: Vec<String>,
    #[serde(default)]
    scope: HostScope,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RuleEntry {
    layer: Layer,
    target: String,
    set: serde_json::Map<String, JsonValue>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RulebookEntry {
    families: Vec<FamilyEntry>,
    hosts: Vec<HostEntry>,
    rules: Vec<RuleEntry>,
    #[serde(default)]
    service_tiers: Vec<tiers::TierEntry>,
    #[serde(default)]
    thinking_defaults: ThinkingDefaults,
    #[serde(default)]
    service_tier_prices: prices::TierPrices,
    #[serde(default)]
    cache_write_1h_prices: prices::LongWritePrices,
    #[serde(default)]
    provider_defaults: provider_defaults::ProviderDefaults,
}

#[derive(Debug)]
struct Family {
    id: String,
    on: MatchOn,
    pattern: Regex,
    /// The pattern that excludes a model `pattern` matches.
    except: Option<Regex>,
    /// The revision prefix (lowercase) and the range the revision is in.
    revision: Option<(String, revision::Range)>,
}

/// A rulebook: the families, the hosts, the compiled rules, the service
/// tiers, the default thinking ladders, the prices that a catalog row
/// does not carry and the default model of each provider.
#[derive(Debug)]
pub struct Rulebook {
    /// Sorted by id, so a [`QuirksError::FamilyOverlap`] names its two
    /// families in id order.
    families: Vec<Family>,
    by_api: HashMap<String, String>,
    by_provider: HashMap<String, String>,
    /// URL fragment (lowercase) and host id.
    by_url: Vec<(String, String)>,
    /// The hosts of scope `capabilities`.
    capability_hosts: HashSet<String>,
    rules: Rules,
    service_tiers: Vec<tiers::TierEntry>,
    thinking_defaults: ThinkingDefaults,
    service_tier_prices: prices::TierPrices,
    cache_write_1h_prices: prices::LongWritePrices,
    provider_defaults: provider_defaults::ProviderDefaults,
}

/// `/[\s_.:]+/g`.
static SEPARATORS: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"[\s_.:]+").unwrap_or_else(|_| unreachable!("static regex")));

/// TS `getModelMatchCandidates`: the lowercased id (and name), each also
/// with separator runs replaced by `-`.
pub(crate) fn match_candidates(model_id: &str, model_name: &str) -> Vec<String> {
    let values: &[&str] = if model_name.is_empty() {
        &[model_id]
    } else {
        &[model_id, model_name]
    };
    values
        .iter()
        .flat_map(|value| {
            let lower = value.to_lowercase();
            let dashed = SEPARATORS.replace_all(&lower, "-").into_owned();
            [lower, dashed]
        })
        .collect()
}

/// Insert `key → host` into `map`; a key that names two hosts is an error.
fn claim(map: &mut HashMap<String, String>, key: &str, host: &str, errors: &mut Vec<QuirksError>) {
    if let Some(first) = map.get(key) {
        errors.push(QuirksError::SharedKey {
            key: key.to_owned(),
            first: first.clone(),
            second: host.to_owned(),
        });
    } else {
        map.insert(key.to_owned(), host.to_owned());
    }
}

static SHIPPED: LazyLock<Rulebook> = LazyLock::new(|| {
    let catalog = crate::models_generated::MODELS
        .values()
        .flat_map(|models| models.values());
    Rulebook::from_json(include_str!("rulebook.json"))
        .and_then(|book| book.check_catalog(catalog).map(|()| book))
        .unwrap_or_else(|errors| {
            let errors: Vec<String> = errors.iter().map(ToString::to_string).collect();
            panic!(
                "the shipped quirks rulebook does not compile: {}",
                errors.join("; ")
            )
        })
});

/// The model ids whose family overlap [`Quirks::of`] has reported.
static REPORTED_OVERLAPS: LazyLock<Mutex<HashSet<String>>> =
    LazyLock::new(|| Mutex::new(HashSet::new()));

impl Rulebook {
    /// The rulebook shipped in the binary (`quirks/rulebook.json`).
    ///
    /// # Panics
    ///
    /// When the shipped rulebook does not compile, or two of its families
    /// match one model of the compiled catalog; its test
    /// (`quirks::tests::the_shipped_rulebook_compiles`) keeps that from
    /// shipping.
    #[must_use]
    pub fn shipped() -> &'static Self {
        &SHIPPED
    }

    /// Parse and compile a rulebook: `families` (`id`, `on`: `id` or
    /// `names`, `match`: a regex), `hosts` (`id`, `apis`, `providers`,
    /// `urls`, `scope`: `all` (default) or `capabilities`), and `rules`
    /// (`layer`, `target`, `set`: directive → value). Unknown fields are
    /// errors.
    ///
    /// # Errors
    ///
    /// When the text is not a rulebook, a pattern is not a regex, a
    /// revision range does not parse, two definitions share an id, two
    /// hosts share an API or a provider, a family or host rule or a
    /// service tier entry targets an undefined id, a host of scope
    /// `capabilities` gets a wire directive, or the rules do not
    /// [`compile`].
    #[allow(clippy::too_many_lines)] // one parse-and-check pass; each check is a short loop
    pub fn from_json(text: &str) -> Result<Self, Vec<QuirksError>> {
        let entry: RulebookEntry = serde_json::from_str(text)
            .map_err(|error| vec![QuirksError::Format(error.to_string())])?;
        let mut errors = Vec::new();
        let mut families: Vec<Family> = Vec::new();
        for family in entry.families {
            if families.iter().any(|known| known.id == family.id) {
                errors.push(QuirksError::DuplicateId {
                    layer: Layer::Family,
                    id: family.id,
                });
                continue;
            }
            let revision = match family.revision {
                Some(RevisionEntry { prefix, range }) => match revision::Range::parse(&range) {
                    Ok(range) => Some((prefix.to_lowercase(), range)),
                    Err(reason) => {
                        errors.push(QuirksError::BadRevision {
                            family: family.id,
                            reason,
                        });
                        continue;
                    }
                },
                None => None,
            };
            let except = family.except.as_deref().map(Regex::new).transpose();
            match (Regex::new(&family.pattern), except) {
                (Ok(pattern), Ok(except)) => families.push(Family {
                    id: family.id,
                    on: family.on,
                    pattern,
                    except,
                    revision,
                }),
                (Err(error), _) | (Ok(_), Err(error)) => errors.push(QuirksError::BadPattern {
                    family: family.id,
                    reason: error.to_string(),
                }),
            }
        }
        families.sort_by(|left, right| left.id.cmp(&right.id));
        let mut host_ids: Vec<&str> = Vec::new();
        let mut by_api = HashMap::new();
        let mut by_provider = HashMap::new();
        let mut by_url = Vec::new();
        let mut capability_hosts = HashSet::new();
        for host in &entry.hosts {
            if host_ids.contains(&host.id.as_str()) {
                errors.push(QuirksError::DuplicateId {
                    layer: Layer::Host,
                    id: host.id.clone(),
                });
                continue;
            }
            host_ids.push(&host.id);
            if host.scope == HostScope::Capabilities {
                capability_hosts.insert(host.id.clone());
            }
            for api in &host.apis {
                claim(&mut by_api, api, &host.id, &mut errors);
            }
            for provider in &host.providers {
                claim(&mut by_provider, provider, &host.id, &mut errors);
            }
            by_url.extend(
                host.urls
                    .iter()
                    .map(|url| (url.to_lowercase(), host.id.clone())),
            );
        }
        let raw: Vec<RawRule> = entry
            .rules
            .into_iter()
            .flat_map(|rule| {
                let RuleEntry { layer, target, set } = rule;
                set.into_iter().map(move |(directive, value)| RawRule {
                    layer,
                    target: target.clone(),
                    directive,
                    value,
                })
            })
            .collect();
        let rules = match compile(&raw) {
            Ok(rules) => {
                let mut undefined = HashSet::new();
                let mut wire_on_capabilities = HashSet::new();
                for rule in &raw {
                    let defined = match rule.layer {
                        Layer::Family => families.iter().any(|family| family.id == rule.target),
                        Layer::Model => true,
                        Layer::Host => host_ids.contains(&rule.target.as_str()),
                    };
                    if !defined && undefined.insert((rule.layer, rule.target.as_str())) {
                        errors.push(QuirksError::UndefinedTarget {
                            layer: rule.layer,
                            target: rule.target.clone(),
                        });
                    }
                    let wire = Directive::parse(&rule.directive).is_some_and(|directive| {
                        directive.capability().is_none() && directive != Directive::PromptProgress
                    });
                    if rule.layer == Layer::Host
                        && wire
                        && capability_hosts.contains(&rule.target)
                        && wire_on_capabilities
                            .insert((rule.target.as_str(), rule.directive.as_str()))
                    {
                        errors.push(QuirksError::WireDirectiveOnCapabilityHost {
                            host: rule.target.clone(),
                            directive: rule.directive.clone(),
                        });
                    }
                }
                Some(rules)
            }
            Err(compile_errors) => {
                errors.extend(compile_errors);
                None
            }
        };
        errors.extend(
            entry
                .service_tiers
                .iter()
                .filter_map(|tier| tier.family.as_ref())
                .filter(|target| !families.iter().any(|family| &&family.id == target))
                .map(|target| QuirksError::UndefinedTierFamily {
                    family: target.clone(),
                }),
        );
        match rules {
            Some(rules) if errors.is_empty() => Ok(Self {
                families,
                by_api,
                by_provider,
                by_url,
                capability_hosts,
                rules,
                service_tiers: entry.service_tiers,
                thinking_defaults: entry.thinking_defaults,
                service_tier_prices: entry.service_tier_prices,
                cache_write_1h_prices: entry.cache_write_1h_prices,
                provider_defaults: entry.provider_defaults,
            }),
            Some(_) | None => Err(errors),
        }
    }

    /// The targets `model` names for `lookup` (see the module docs).
    ///
    /// # Errors
    ///
    /// [`FamilyOverlap`] when two families match `model`.
    pub fn query<'a>(
        &'a self,
        model: &'a Model,
        lookup: Lookup,
    ) -> Result<Query<'a>, FamilyOverlap> {
        Ok(Query {
            family: self.family(&model.id, &model.name)?,
            model: &model.id,
            host: self.host(model.into(), lookup),
        })
    }

    /// The one family that matches the model with id `id` and name `name`
    /// (see the module docs); `None` when no family does.
    ///
    /// # Errors
    ///
    /// [`FamilyOverlap`] when two families match the model.
    pub fn family(&self, id: &str, name: &str) -> Result<Option<&str>, FamilyOverlap> {
        let lower_id = id.to_lowercase();
        let mut candidates: Option<Vec<String>> = None;
        let mut matching = self.families.iter().filter(|family| {
            let mut matches = |pattern: &Regex| match family.on {
                MatchOn::Id => pattern.is_match(&lower_id),
                MatchOn::Names => candidates
                    .get_or_insert_with(|| match_candidates(id, name))
                    .iter()
                    .any(|candidate| pattern.is_match(candidate)),
            };
            matches(&family.pattern)
                && !family.except.as_ref().is_some_and(&mut matches)
                && family.revision.as_ref().is_none_or(|(prefix, range)| {
                    range.holds(revision::of(id, prefix).unwrap_or_default())
                })
        });
        let family = matching.next();
        if let (Some(first), Some(second)) = (family, matching.next()) {
            return Err(FamilyOverlap {
                model: id.to_owned(),
                first: first.id.clone(),
                second: second.id.clone(),
            });
        }
        Ok(family.map(|family| family.id.as_str()))
    }

    /// The host `model` names for `lookup` (see the module docs): a host
    /// that does not serve `lookup` is skipped as if it named nothing.
    fn host(&self, model: ModelKey<'_>, lookup: Lookup) -> Option<&str> {
        let serves = |host: &&String| match lookup {
            Lookup::Capabilities => true,
            Lookup::Wire => !self.capability_hosts.contains(host.as_str()),
        };
        let base_url = model.base_url.to_lowercase();
        self.by_api
            .get(model.api)
            .filter(serves)
            .or_else(|| self.by_provider.get(model.provider).filter(serves))
            .or_else(|| {
                self.by_url
                    .iter()
                    .filter(|(fragment, host)| {
                        base_url.contains(fragment.as_str()) && serves(&host)
                    })
                    .max_by(|(left, left_host), (right, right_host)| {
                        left.len()
                            .cmp(&right.len())
                            .then_with(|| right_host.cmp(left_host))
                    })
                    .map(|(_, host)| host)
            })
            .map(String::as_str)
    }

    /// Check that no two families match one of `models`.
    ///
    /// # Errors
    ///
    /// A [`QuirksError::FamilyOverlap`] for each model two families match,
    /// in model order.
    pub fn check_catalog<'m>(
        &self,
        models: impl IntoIterator<Item = &'m Model>,
    ) -> Result<(), Vec<QuirksError>> {
        let errors: Vec<QuirksError> = models
            .into_iter()
            .filter_map(|model| self.query(model, Lookup::Wire).err().map(QuirksError::from))
            .collect();
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// As [`Rules::lookup`].
    #[must_use]
    pub fn lookup(&self, query: &Query<'_>, directive: Directive) -> Answer<'_> {
        self.rules.lookup(query, directive)
    }

    /// The default thinking ladders ([`ThinkingDefaults`]).
    #[must_use]
    pub const fn thinking_defaults(&self) -> &ThinkingDefaults {
        &self.thinking_defaults
    }
}

/// The shipped rulebook's family of the model with id `id` and name
/// `name`. A model that two families match names no family: the overlap is
/// logged as an error, once per model id.
fn shipped_family(id: &str, name: &str) -> Option<&'static str> {
    Rulebook::shipped()
        .family(id, name)
        .unwrap_or_else(|error| {
            let first_report = REPORTED_OVERLAPS
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .insert(id.to_owned());
            if first_report {
                tracing::error!(%error, "quirks: the model names no family");
            }
            None
        })
}

/// The shipped rulebook's answers for one model. Each getter is `None`
/// when no rule applies: the caller applies its own default.
#[derive(Debug, Clone, Copy)]
pub struct Quirks<'a> {
    query: Query<'a>,
}

impl<'a> Quirks<'a> {
    /// The shipped rulebook's wire query for `model`
    /// ([`Quirks::for_lookup`] with [`Lookup::Wire`]).
    #[must_use]
    pub fn of(model: impl Into<ModelKey<'a>>) -> Self {
        Self::for_lookup(model, Lookup::Wire)
    }

    /// The shipped rulebook's query for `model` and `lookup`. A model that
    /// two families match names no family: the overlap is logged as an
    /// error, once per model id.
    #[must_use]
    pub fn for_lookup(model: impl Into<ModelKey<'a>>, lookup: Lookup) -> Self {
        let model = model.into();
        Self {
            query: Query {
                family: shipped_family(model.id, model.name),
                model: model.id,
                host: Rulebook::shipped().host(model, lookup),
            },
        }
    }

    /// The targets this model names.
    #[must_use]
    pub const fn query(&self) -> Query<'a> {
        self.query
    }

    fn known(&self, directive: Directive) -> Option<&'static Value> {
        match Rulebook::shipped().lookup(&self.query, directive) {
            Answer::Known(value) => Some(value),
            Answer::Unknown => None,
        }
    }

    fn flag(&self, directive: Directive) -> Option<bool> {
        match self.known(directive)? {
            Value::Bool(flag) => Some(*flag),
            Value::Count(_)
            | Value::Prefixes(_)
            | Value::MaxTokensField(_)
            | Value::ThinkingFormat(_)
            | Value::SessionAffinityFormat(_)
            | Value::ThinkingLadder(_)
            | Value::ThinkingBudgets(_)
            | Value::Endpoint(_) => None,
        }
    }

    fn prefixes(&self, directive: Directive) -> Option<&'static [String]> {
        match self.known(directive)? {
            Value::Prefixes(prefixes) => Some(prefixes),
            Value::Bool(_)
            | Value::Count(_)
            | Value::MaxTokensField(_)
            | Value::ThinkingFormat(_)
            | Value::SessionAffinityFormat(_)
            | Value::ThinkingLadder(_)
            | Value::ThinkingBudgets(_)
            | Value::Endpoint(_) => None,
        }
    }

    /// [`Directive::Store`].
    #[must_use]
    pub fn store(&self) -> Option<bool> {
        self.flag(Directive::Store)
    }

    /// [`Directive::DeveloperRole`].
    #[must_use]
    pub fn developer_role(&self) -> Option<bool> {
        self.flag(Directive::DeveloperRole)
    }

    /// [`Directive::DeveloperRolePrefixes`].
    #[must_use]
    pub fn developer_role_prefixes(&self) -> Option<&'static [String]> {
        self.prefixes(Directive::DeveloperRolePrefixes)
    }

    /// [`Directive::ReasoningEffort`].
    #[must_use]
    pub fn reasoning_effort(&self) -> Option<bool> {
        self.flag(Directive::ReasoningEffort)
    }

    /// [`Directive::MaxTokensField`].
    #[must_use]
    pub fn max_tokens_field(&self) -> Option<MaxTokensField> {
        match self.known(Directive::MaxTokensField)? {
            Value::MaxTokensField(field) => Some(*field),
            Value::Bool(_)
            | Value::Count(_)
            | Value::Prefixes(_)
            | Value::ThinkingFormat(_)
            | Value::SessionAffinityFormat(_)
            | Value::ThinkingLadder(_)
            | Value::ThinkingBudgets(_)
            | Value::Endpoint(_) => None,
        }
    }

    /// [`Directive::ReasoningContentOnAssistant`].
    #[must_use]
    pub fn reasoning_content_on_assistant(&self) -> Option<bool> {
        self.flag(Directive::ReasoningContentOnAssistant)
    }

    /// [`Directive::ThinkingFormat`].
    #[must_use]
    pub fn thinking_format(&self) -> Option<ThinkingFormat> {
        match self.known(Directive::ThinkingFormat)? {
            Value::ThinkingFormat(format) => Some(*format),
            Value::Bool(_)
            | Value::Count(_)
            | Value::Prefixes(_)
            | Value::MaxTokensField(_)
            | Value::SessionAffinityFormat(_)
            | Value::ThinkingLadder(_)
            | Value::ThinkingBudgets(_)
            | Value::Endpoint(_) => None,
        }
    }

    /// [`Directive::AnthropicCacheControlPrefixes`].
    #[must_use]
    pub fn anthropic_cache_control_prefixes(&self) -> Option<&'static [String]> {
        self.prefixes(Directive::AnthropicCacheControlPrefixes)
    }

    /// [`Directive::SessionAffinityHeaders`].
    #[must_use]
    pub fn session_affinity_headers(&self) -> Option<bool> {
        self.flag(Directive::SessionAffinityHeaders)
    }

    /// [`Directive::SessionAffinityFormat`].
    #[must_use]
    pub fn session_affinity_format(&self) -> Option<SessionAffinityFormat> {
        match self.known(Directive::SessionAffinityFormat)? {
            Value::SessionAffinityFormat(format) => Some(*format),
            Value::Bool(_)
            | Value::Count(_)
            | Value::Prefixes(_)
            | Value::MaxTokensField(_)
            | Value::ThinkingFormat(_)
            | Value::ThinkingLadder(_)
            | Value::ThinkingBudgets(_)
            | Value::Endpoint(_) => None,
        }
    }

    /// [`Directive::LongCacheRetention`].
    #[must_use]
    pub fn long_cache_retention(&self) -> Option<bool> {
        self.flag(Directive::LongCacheRetention)
    }

    /// [`Directive::StrictTools`].
    #[must_use]
    pub fn strict_tools(&self) -> Option<bool> {
        self.flag(Directive::StrictTools)
    }

    /// [`Directive::StrictCap`].
    #[must_use]
    pub fn strict_cap(&self) -> Option<u32> {
        match self.known(Directive::StrictCap)? {
            Value::Count(cap) => Some(*cap),
            Value::Bool(_)
            | Value::Prefixes(_)
            | Value::MaxTokensField(_)
            | Value::ThinkingFormat(_)
            | Value::SessionAffinityFormat(_)
            | Value::ThinkingLadder(_)
            | Value::ThinkingBudgets(_)
            | Value::Endpoint(_) => None,
        }
    }

    /// [`Directive::Endpoint`]: the dialect that serves `capability`;
    /// `None` when no rule gives one or a rule says `false`. Ask it of a
    /// [`Lookup::Capabilities`] query: a wire query skips the hosts of
    /// scope `capabilities`.
    #[must_use]
    pub fn endpoint(&self, capability: Capability) -> Option<Dialect> {
        match self.known(Directive::Endpoint(capability))? {
            Value::Endpoint(dialect) => *dialect,
            Value::Bool(_)
            | Value::Count(_)
            | Value::Prefixes(_)
            | Value::MaxTokensField(_)
            | Value::ThinkingFormat(_)
            | Value::SessionAffinityFormat(_)
            | Value::ThinkingLadder(_)
            | Value::ThinkingBudgets(_) => None,
        }
    }

    /// [`Directive::GoogleValidatedTools`].
    #[must_use]
    pub fn google_validated_tools(&self) -> Option<bool> {
        self.flag(Directive::GoogleValidatedTools)
    }

    /// [`Directive::QwenChatTemplate`].
    #[must_use]
    pub fn qwen_chat_template(&self) -> Option<bool> {
        self.flag(Directive::QwenChatTemplate)
    }

    /// [`Directive::AdaptiveThinking`].
    #[must_use]
    pub fn adaptive_thinking(&self) -> Option<bool> {
        self.flag(Directive::AdaptiveThinking)
    }

    /// [`Directive::ThinkingBlockBinding`].
    #[must_use]
    pub fn thinking_block_binding(&self) -> Option<bool> {
        self.flag(Directive::ThinkingBlockBinding)
    }

    /// [`Directive::PromptCaching`].
    #[must_use]
    pub fn prompt_caching(&self) -> Option<bool> {
        self.flag(Directive::PromptCaching)
    }

    /// [`Directive::ExplicitCacheBreakpoints`].
    #[must_use]
    pub fn explicit_cache_breakpoints(&self) -> Option<bool> {
        self.flag(Directive::ExplicitCacheBreakpoints)
    }

    /// [`Directive::GoogleThinkingLevel`].
    #[must_use]
    pub fn google_thinking_level(&self) -> Option<bool> {
        self.flag(Directive::GoogleThinkingLevel)
    }

    /// [`Directive::ThinkingBudgets`].
    #[must_use]
    pub fn thinking_budgets(&self) -> Option<&'static LevelBudgets> {
        match self.known(Directive::ThinkingBudgets)? {
            Value::ThinkingBudgets(budgets) => Some(budgets),
            Value::Bool(_)
            | Value::Count(_)
            | Value::Prefixes(_)
            | Value::MaxTokensField(_)
            | Value::ThinkingFormat(_)
            | Value::SessionAffinityFormat(_)
            | Value::ThinkingLadder(_)
            | Value::Endpoint(_) => None,
        }
    }

    /// [`Directive::ToolChoiceNative`].
    #[must_use]
    pub fn tool_choice_native(&self) -> Option<bool> {
        self.flag(Directive::ToolChoiceNative)
    }

    /// [`Directive::ToolChoiceFree`].
    #[must_use]
    pub fn tool_choice_free(&self) -> Option<bool> {
        self.flag(Directive::ToolChoiceFree)
    }

    /// [`Directive::PromptProgress`]. Ask it of a [`Lookup::Capabilities`]
    /// query: the llama.cpp host has scope `capabilities`.
    #[must_use]
    pub fn prompt_progress(&self) -> Option<bool> {
        self.flag(Directive::PromptProgress)
    }

    /// [`Directive::ThinkingLadder`].
    #[must_use]
    pub fn thinking_ladder(&self) -> Option<&'static ThinkingLevelMap> {
        match self.known(Directive::ThinkingLadder)? {
            Value::ThinkingLadder(ladder) => Some(ladder),
            Value::Bool(_)
            | Value::Count(_)
            | Value::Prefixes(_)
            | Value::MaxTokensField(_)
            | Value::ThinkingFormat(_)
            | Value::SessionAffinityFormat(_)
            | Value::ThinkingBudgets(_)
            | Value::Endpoint(_) => None,
        }
    }
}
