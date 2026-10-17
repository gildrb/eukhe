//! The quirks rulebook (docs/inference.md S6.1; model `bend/infer.bend`
//! section 1): which wire settings a model family, a model, and a host
//! need, as data.
//!
//! A rule says: at a layer (a model family, a model, a host), for a target
//! id of that layer, directive `d` has value `v`. [`compile`] rejects a rule
//! with an unknown directive, a value of the wrong type, and two rules of
//! one layer, target and directive with different values. A lookup takes
//! the rule of the highest layer that applies (host over model over
//! family); with no rule that applies the answer is [`Answer::Unknown`],
//! never a guess: the caller (a wire API's compat resolver) applies its
//! own default, and the explicit `model.compat` wins over both. The answer
//! does not depend on the order of the rules.
//!
//! A model's query names one target per layer ([`Rulebook::query`]):
//! - family: the one family whose pattern matches the model. A model that
//!   two families match is the error [`FamilyOverlap`], never
//!   a choice between them: the shipped rulebook is checked against every
//!   model of the compiled catalog ([`Rulebook::check_catalog`]), and a
//!   model outside it that two families match names no family (each
//!   family directive is then Unknown), reported once per model id;
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
//! The shipped rulebook is `rulebook.json`, compiled into the binary and
//! compiled once on first use.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::sync::{LazyLock, Mutex, PoisonError};

use regex::Regex;
use serde::Deserialize;
use serde_json::Value as JsonValue;

use crate::capabilities::{Capability, Dialect};
use crate::types::{MaxTokensField, Model, SessionAffinityFormat, ThinkingFormat};

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
    /// Every layer, highest first: the lookup order.
    const BY_PRECEDENCE: [Self; 3] = [Self::Host, Self::Model, Self::Family];

    const fn index(self) -> usize {
        match self {
            Self::Family => 0,
            Self::Model => 1,
            Self::Host => 2,
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
    /// Bedrock: the model takes adaptive thinking.
    AdaptiveThinking,
    /// The host supports a native forced tool choice.
    ToolChoiceNative,
    /// Forcing a tool choice costs no prompt-cache invalidation.
    ToolChoiceFree,
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
        Self::ToolChoiceNative,
        Self::ToolChoiceFree,
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
            Self::ToolChoiceNative => "tool_choice_native",
            Self::ToolChoiceFree => "tool_choice_free",
            Self::Endpoint(capability) => capability.as_str(),
        }
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
            | Self::ToolChoiceNative
            | Self::ToolChoiceFree => None,
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
            | Self::ToolChoiceNative
            | Self::ToolChoiceFree => ValueKind::Bool,
            Self::DeveloperRolePrefixes | Self::AnthropicCacheControlPrefixes => {
                ValueKind::Prefixes
            }
            Self::MaxTokensField => ValueKind::MaxTokensField,
            Self::ThinkingFormat => ValueKind::ThinkingFormat,
            Self::SessionAffinityFormat => ValueKind::SessionAffinityFormat,
            Self::StrictCap => ValueKind::Count,
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
    /// The dialect of a capability endpoint; `None`: unsupported.
    Endpoint(Option<Dialect>),
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

/// The values one target of one layer gets.
type Settings = BTreeMap<Directive, (Value, JsonValue)>;

/// Compiled rules: per layer, per target, per directive, one value.
#[derive(Debug, Clone, Default)]
pub struct Rules {
    layers: [HashMap<String, Settings>; 3],
}

/// Compile `rules`: every directive known, every value of its directive's
/// type, and no two rules of one layer, target and directive with different
/// values. The result does not depend on the order of `rules`.
///
/// # Errors
///
/// Every rule that breaks one of those, in rule order.
pub fn compile(rules: &[RawRule]) -> Result<Rules, Vec<QuirksError>> {
    let mut compiled = Rules::default();
    let mut errors = Vec::new();
    for rule in rules {
        let Some(directive) = Directive::parse(&rule.directive) else {
            errors.push(QuirksError::UnknownDirective {
                layer: rule.layer,
                target: rule.target.clone(),
                directive: rule.directive.clone(),
            });
            continue;
        };
        let Some(value) = directive.kind().parse(&rule.value) else {
            errors.push(QuirksError::BadValue {
                layer: rule.layer,
                target: rule.target.clone(),
                directive: rule.directive.clone(),
                value: rule.value.clone(),
                kind: directive.kind(),
            });
            continue;
        };
        let settings = compiled.layers[rule.layer.index()]
            .entry(rule.target.clone())
            .or_default();
        match settings.get(&directive) {
            Some((first, first_raw)) => {
                if *first != value {
                    errors.push(QuirksError::Clash {
                        layer: rule.layer,
                        target: rule.target.clone(),
                        directive: rule.directive.clone(),
                        first: first_raw.clone(),
                        second: rule.value.clone(),
                    });
                }
            }
            None => {
                settings.insert(directive, (value, rule.value.clone()));
            }
        }
    }
    if errors.is_empty() {
        Ok(compiled)
    } else {
        Err(errors)
    }
}

impl Rules {
    /// The value of `directive` for `query`: the rule of the highest layer
    /// whose target the query names; [`Answer::Unknown`] when none does.
    #[must_use]
    pub fn lookup(&self, query: &Query<'_>, directive: Directive) -> Answer<'_> {
        Layer::BY_PRECEDENCE
            .iter()
            .find_map(|layer| {
                let target = query.target(*layer)?;
                self.layers[layer.index()]
                    .get(target)?
                    .get(&directive)
                    .map(|(value, _)| Answer::Known(value))
            })
            .unwrap_or(Answer::Unknown)
    }

    fn targets(&self, layer: Layer) -> impl Iterator<Item = &String> {
        self.layers[layer.index()].keys()
    }
}

/// The target a query names at each layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Query<'a> {
    pub family: Option<&'a str>,
    pub model: &'a str,
    pub host: Option<&'a str>,
}

impl<'a> Query<'a> {
    const fn target(&self, layer: Layer) -> Option<&'a str> {
        match layer {
            Layer::Family => self.family,
            Layer::Model => Some(self.model),
            Layer::Host => self.host,
        }
    }
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

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FamilyEntry {
    id: String,
    on: MatchOn,
    #[serde(rename = "match")]
    pattern: String,
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
}

#[derive(Debug)]
struct Family {
    id: String,
    on: MatchOn,
    pattern: Regex,
}

/// A rulebook: the families, the hosts, and the compiled rules.
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
    /// When the text is not a rulebook, a pattern is not a regex, two
    /// definitions share an id, two hosts share an API or a provider, a
    /// family or host rule targets an undefined id, a host of scope
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
            match Regex::new(&family.pattern) {
                Ok(pattern) => families.push(Family {
                    id: family.id,
                    on: family.on,
                    pattern,
                }),
                Err(error) => errors.push(QuirksError::BadPattern {
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
        let rules = compile(&raw).unwrap_or_else(|compile_errors| {
            errors.extend(compile_errors);
            Rules::default()
        });
        for target in rules.targets(Layer::Family) {
            if !families.iter().any(|family| &family.id == target) {
                errors.push(QuirksError::UndefinedTarget {
                    layer: Layer::Family,
                    target: target.clone(),
                });
            }
        }
        for target in rules.targets(Layer::Host) {
            if !host_ids.contains(&target.as_str()) {
                errors.push(QuirksError::UndefinedTarget {
                    layer: Layer::Host,
                    target: target.clone(),
                });
            }
            if capability_hosts.contains(target) {
                errors.extend(
                    rules.layers[Layer::Host.index()][target]
                        .keys()
                        .filter(|directive| directive.capability().is_none())
                        .map(|directive| QuirksError::WireDirectiveOnCapabilityHost {
                            host: target.clone(),
                            directive: directive.as_str().to_owned(),
                        }),
                );
            }
        }
        if errors.is_empty() {
            Ok(Self {
                families,
                by_api,
                by_provider,
                by_url,
                capability_hosts,
                rules,
            })
        } else {
            Err(errors)
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
        let lower_id = model.id.to_lowercase();
        let mut candidates: Option<Vec<String>> = None;
        let mut matching = self.families.iter().filter(|family| match family.on {
            MatchOn::Id => family.pattern.is_match(&lower_id),
            MatchOn::Names => candidates
                .get_or_insert_with(|| match_candidates(&model.id, &model.name))
                .iter()
                .any(|candidate| family.pattern.is_match(candidate)),
        });
        let family = matching.next();
        if let (Some(first), Some(second)) = (family, matching.next()) {
            return Err(FamilyOverlap {
                model: model.id.clone(),
                first: first.id.clone(),
                second: second.id.clone(),
            });
        }
        Ok(Query {
            family: family.map(|family| family.id.as_str()),
            model: &model.id,
            host: self.host(model, lookup),
        })
    }

    /// The host `model` names for `lookup` (see the module docs): a host
    /// that does not serve `lookup` is skipped as if it named nothing.
    fn host(&self, model: &Model, lookup: Lookup) -> Option<&str> {
        let serves = |host: &&String| match lookup {
            Lookup::Capabilities => true,
            Lookup::Wire => !self.capability_hosts.contains(host.as_str()),
        };
        let base_url = model.base_url.to_lowercase();
        self.by_api
            .get(&model.api)
            .filter(serves)
            .or_else(|| self.by_provider.get(&model.provider).filter(serves))
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
    pub fn of(model: &'a Model) -> Self {
        Self::for_lookup(model, Lookup::Wire)
    }

    /// The shipped rulebook's query for `model` and `lookup`. A model that
    /// two families match names no family: the overlap is logged as an
    /// error, once per model id.
    #[must_use]
    pub fn for_lookup(model: &'a Model, lookup: Lookup) -> Self {
        let book = Rulebook::shipped();
        let query = book.query(model, lookup).unwrap_or_else(|error| {
            let first_report = REPORTED_OVERLAPS
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .insert(model.id.clone());
            if first_report {
                tracing::error!(%error, "quirks: the model names no family");
            }
            Query {
                family: None,
                model: &model.id,
                host: book.host(model, lookup),
            }
        });
        Self { query }
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
            | Value::SessionAffinityFormat(_) => None,
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
}
