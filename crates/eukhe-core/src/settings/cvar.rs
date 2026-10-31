//! Settings as console variables (the model is
//! `bend/cvar.bend`, its laws are proven in `PROOF.bend`).
//!
//! Each setting (a cvar) is declared once in [`table`]: its id (the dotted
//! path of its key in `settings.json`), its type, its scope, whether an
//! agent may write it to its cfg (`persist`) and whether clients see it
//! (`replicate`), and its default. [`Registry::new`] rejects a second
//! declaration of an id and a default of the wrong type; [`registry`] is
//! the checked table, built at startup.
//!
//! Values come in layers; a higher layer wins:
//!
//! ```text
//! default < config (settings.json, config.cfg)
//!         < each agent of the family, root first:
//!           its profile (subagent.cfg, agents/<name>.cfg) < its own sets
//! ```
//!
//! In each layer the last valid set of a cvar wins. A set is valid when
//! the cvar is declared and the value has its type; in an agent layer the
//! cvar must also be Local: a Global cvar has one value for the whole
//! family. A subagent's family is its parent's family plus itself, so it
//! starts from its parent's values.
//!
//! Every one of these decisions runs as the compiled model (entry
//! `bend/ffi_cvar_layers.bend`, [`eukhe_bend::rules::cvar_layers`]): the
//! registry's refusal, each value and whether a layer sets it, the verdict
//! on a set and on a toggle, the sets an agent writes, the config sets of
//! a settings document. Rust keeps the layers, reads a value's syntax
//! ([`CvarType::admits`], [`CvarType::parse`]) and acts on the answers.

use std::collections::HashMap;
use std::fmt;
use std::sync::{LazyLock, OnceLock};

use eukhe_bend::rules::cvar::expand;
use eukhe_bend::rules::cvar_layers as cl;
use eukhe_types::cvar::{Aliases, Binds, Command, ExpandError, ParseError};
use serde::{Deserialize, Serialize};
use serde_json::Value;

pub mod table;

#[cfg(test)]
mod tests;

/// The words a [`CvarType::NatOrOff`] value turns its rule off with.
pub(crate) const OFF_WORDS: &[&str] = &["off", "none"];

/// The type of a cvar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CvarType {
    Bool,
    /// A whole number `>= 0`.
    Nat,
    /// A whole number `>= 0`, or `off` (also written `none`): a rule that
    /// may be turned off (`idleEvictionMinutes`, the session archive
    /// rules).
    NatOrOff,
    /// Any string (the empty string reads as unset where the setting is
    /// optional).
    Text,
    /// One of the listed strings.
    Choice(&'static [&'static str]),
    /// A list of strings.
    List,
    /// A list of strings, each one of the listed options.
    ChoiceList(&'static [&'static str]),
    /// Any JSON value (structured settings such as `mcpServers`).
    Json,
}

impl CvarType {
    /// `value` has this type.
    #[must_use]
    pub fn admits(self, value: &Value) -> bool {
        match self {
            CvarType::Bool => value.is_boolean(),
            CvarType::Nat => value.is_u64(),
            CvarType::NatOrOff => {
                value.is_u64() || value.as_str().is_some_and(|text| OFF_WORDS.contains(&text))
            }
            CvarType::Text => value.is_string(),
            CvarType::Choice(options) => value.as_str().is_some_and(|text| options.contains(&text)),
            CvarType::List => value
                .as_array()
                .is_some_and(|items| items.iter().all(Value::is_string)),
            CvarType::ChoiceList(options) => value.as_array().is_some_and(|items| {
                items
                    .iter()
                    .all(|item| item.as_str().is_some_and(|text| options.contains(&text)))
            }),
            CvarType::Json => true,
        }
    }

    /// The value a command writes as `text` (`set <id> <text>`).
    ///
    /// Bool: `true`/`on`/`yes`/`1` or `false`/`off`/`no`/`0`. A list (and a
    /// list of choices): a JSON array of strings or comma-separated items
    /// (each one of the options for a list of choices). Json: JSON.
    #[must_use]
    pub fn parse(self, text: &str) -> Option<Value> {
        match self {
            CvarType::Bool => match text {
                "true" | "on" | "yes" | "1" => Some(Value::Bool(true)),
                "false" | "off" | "no" | "0" => Some(Value::Bool(false)),
                _ => None,
            },
            CvarType::Nat => text.parse::<u64>().ok().map(Value::from),
            CvarType::NatOrOff => match text.parse::<u64>() {
                Ok(number) => Some(Value::from(number)),
                Err(_) => OFF_WORDS
                    .contains(&text)
                    .then(|| Value::String(text.to_string())),
            },
            CvarType::Text => Some(Value::String(text.to_string())),
            CvarType::Choice(options) => options
                .contains(&text)
                .then(|| Value::String(text.to_string())),
            CvarType::List | CvarType::ChoiceList(_) => {
                let value = if text.trim_start().starts_with('[') {
                    serde_json::from_str::<Value>(text).ok()?
                } else {
                    Value::Array(
                        text.split(',')
                            .map(str::trim)
                            .filter(|item| !item.is_empty())
                            .map(|item| Value::String(item.to_string()))
                            .collect(),
                    )
                };
                self.admits(&value).then_some(value)
            }
            CvarType::Json => serde_json::from_str(text).ok(),
        }
    }

    /// The name of the type in messages.
    #[must_use]
    pub fn name(self) -> String {
        match self {
            CvarType::Bool => "a bool".to_string(),
            CvarType::Nat => "a whole number".to_string(),
            CvarType::NatOrOff => "a whole number, off or none".to_string(),
            CvarType::Text => "a text".to_string(),
            CvarType::Choice(options) => format!("one of {}", options.join(", ")),
            CvarType::List => "a list".to_string(),
            CvarType::ChoiceList(options) => format!("a list of {}", options.join(", ")),
            CvarType::Json => "JSON".to_string(),
        }
    }
}

/// `value` as a command writes it: [`CvarType::parse`] reads it back.
#[must_use]
pub fn value_text(value: &Value) -> String {
    match value {
        Value::String(text) => text.clone(),
        Value::Bool(_) | Value::Number(_) | Value::Null | Value::Array(_) | Value::Object(_) => {
            value.to_string()
        }
    }
}

/// Whether a cvar has one value for the whole family.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CvarScope {
    /// One value for every agent: only the global config sets it (no
    /// project file, no profile, no agent set).
    Global,
    /// Each agent may have its own value.
    Local,
}

/// A declared default.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Init {
    Bool(bool),
    Nat(u64),
    Text(&'static str),
    /// The empty list.
    EmptyList,
    /// A list of strings.
    List(&'static [&'static str]),
    /// JSON `null` (a Json cvar that is unset).
    Null,
}

impl Init {
    #[must_use]
    pub fn value(self) -> Value {
        match self {
            Init::Bool(value) => Value::Bool(value),
            Init::Nat(value) => Value::from(value),
            Init::Text(value) => Value::String(value.to_string()),
            Init::EmptyList => Value::Array(Vec::new()),
            Init::List(items) => Value::Array(
                items
                    .iter()
                    .map(|item| Value::String((*item).to_string()))
                    .collect(),
            ),
            Init::Null => Value::Null,
        }
    }
}

/// The declaration of one cvar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Decl {
    /// The dotted path of the key in `settings.json` (`retry.enabled`).
    pub id: &'static str,
    pub ty: CvarType,
    pub scope: CvarScope,
    /// An agent may write its sets of this cvar to its cfg.
    pub persist: bool,
    /// Clients see the value of this cvar.
    pub replicate: bool,
    pub init: Init,
}

/// Which flag a [`Sets::written`] selects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Flag {
    Persist,
    Replicate,
}

impl Flag {
    fn model(self) -> cl::Flag {
        match self {
            Flag::Persist => cl::Flag::Persist,
            Flag::Replicate => cl::Flag::Replicate,
        }
    }
}

impl Decl {
    /// This declaration as the core sees it: cvar `number`, its default
    /// the reference `default`.
    fn model(&self, number: u64, default: u64) -> cl::Decl {
        cl::Decl {
            id: number,
            ty: match self.ty {
                CvarType::Bool => cl::Ty::Bool,
                CvarType::Nat
                | CvarType::NatOrOff
                | CvarType::Text
                | CvarType::Choice(_)
                | CvarType::List
                | CvarType::ChoiceList(_)
                | CvarType::Json => cl::Ty::Nat,
            },
            local: self.scope == CvarScope::Local,
            persist: self.persist,
            replicate: self.replicate,
            init: self.model_val(&self.init.value(), default),
        }
    }

    /// `value`, the reference `reference`, as the core sees it: of this
    /// cvar's type when it has it ([`CvarType::admits`]), of the other type
    /// when not. A Bool crosses as itself.
    fn model_val(&self, value: &Value, reference: u64) -> cl::Val {
        match (self.ty, value) {
            (CvarType::Bool, Value::Bool(b)) => cl::Val::Bool(*b),
            (CvarType::Bool, _) => cl::Val::Nat(reference),
            (ty, _) if ty.admits(value) => cl::Val::Nat(reference),
            _ => cl::Val::Bool(false),
        }
    }
}

/// The place `n` the core answered in a list of `len` items.
///
/// # Panics
///
/// When `n` is past the list: the core answered a number Rust never sent
/// (an inconsistent build).
fn place(n: u64, len: usize) -> usize {
    match usize::try_from(n) {
        Ok(at) if at < len => at,
        _ => panic!("the cvar core answered the number {n}, past the {len} it was sent"),
    }
}

/// Why a declaration table is not a registry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegistryError {
    /// A second declaration of `id`.
    Duplicate { id: &'static str },
    /// The default of `id` does not have its type.
    BadDefault { id: &'static str },
}

impl fmt::Display for RegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegistryError::Duplicate { id } => write!(f, "cvar `{id}` is declared twice"),
            RegistryError::BadDefault { id } => {
                write!(f, "the default of cvar `{id}` does not have its type")
            }
        }
    }
}

impl std::error::Error for RegistryError {}

/// The checked declarations: each id once, each default of its type.
#[derive(Debug, PartialEq)]
pub struct Registry {
    decls: &'static [Decl],
    index: HashMap<&'static str, usize>,
    /// The declarations as the core sees them: cvar `i` is `decls[i]`,
    /// its default the reference `i` ([`Refs`]).
    model: Vec<cl::Decl>,
}

impl Registry {
    /// The registry of `decls`: the compiled core decides which
    /// declaration it refuses first (`bend/cvar.bend` `refusal`).
    ///
    /// # Errors
    ///
    /// The first duplicate id or default of the wrong type.
    pub fn new(decls: &'static [Decl]) -> Result<Self, RegistryError> {
        let mut index: HashMap<&'static str, usize> = HashMap::with_capacity(decls.len());
        let mut names = Vec::with_capacity(decls.len());
        let mut model = Vec::with_capacity(decls.len());
        for (at, decl) in decls.iter().enumerate() {
            let next = index.len();
            let number = *index.entry(decl.id).or_insert(next);
            if number == next {
                names.push(decl.id);
            }
            model.push(decl.model(number as u64, at as u64));
        }
        match cl::refusal(&model) {
            None => Ok(Self {
                decls,
                index,
                model,
            }),
            Some(cl::Refusal::Twice(n)) => Err(RegistryError::Duplicate {
                id: names[place(n, names.len())],
            }),
            Some(cl::Refusal::BadInit(n)) => Err(RegistryError::BadDefault {
                id: names[place(n, names.len())],
            }),
        }
    }

    /// The declaration of `id`.
    #[must_use]
    pub fn find(&self, id: &str) -> Option<&'static Decl> {
        let decls: &'static [Decl] = self.decls;
        self.index.get(id).map(|at| &decls[*at])
    }

    /// The declarations, in table order.
    #[must_use]
    pub fn decls(&self) -> &'static [Decl] {
        self.decls
    }
}

static REGISTRY: LazyLock<Registry> = LazyLock::new(|| match Registry::new(table::DECLS) {
    Ok(registry) => registry,
    Err(error) => panic!("the cvar table is broken: {error}"),
});

/// The registry of [`table::DECLS`]. The composition root builds it at
/// startup, so a broken table stops eukhe before any session runs.
///
/// # Panics
///
/// When the table declares an id twice or has a default of the wrong type.
#[must_use]
pub fn registry() -> &'static Registry {
    &REGISTRY
}

/// One set: cvar `id` takes `value`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Set {
    pub id: String,
    pub value: Value,
}

/// A layer's sets, in order: the last valid set of a cvar wins.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Sets(pub Vec<Set>);

/// Which layer a set comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LayerKind {
    /// settings.json and config.cfg: Global and Local cvars.
    Config,
    /// A profile or an agent's own sets: Local cvars only.
    Agent,
}

impl LayerKind {
    fn model(self) -> cl::Layer {
        match self {
            LayerKind::Config => cl::Layer::Config,
            LayerKind::Agent => cl::Layer::Agent,
        }
    }
}

/// The values one request to the core refers to: reference `i` below the
/// registry's length is the default of cvar `i`, the ones after it the
/// values given, in order. An undeclared id crosses as the number past the
/// table.
struct Refs<'a> {
    registry: &'a Registry,
    values: Vec<&'a Value>,
}

impl<'a> Refs<'a> {
    fn new(registry: &'a Registry) -> Self {
        Self {
            registry,
            values: Vec::new(),
        }
    }

    /// `value`, a value of cvar number `at`.
    fn value_of(&mut self, at: usize, value: &'a Value) -> cl::Val {
        let reference = (self.registry.decls.len() + self.values.len()) as u64;
        self.values.push(value);
        self.registry.decls[at].model_val(value, reference)
    }

    fn bind(&mut self, set: &'a Set) -> cl::Bind {
        match self.registry.index.get(set.id.as_str()) {
            Some(&at) => cl::Bind {
                id: at as u64,
                val: self.value_of(at, &set.value),
            },
            None => cl::Bind {
                id: self.registry.decls.len() as u64,
                val: cl::Val::Nat(0),
            },
        }
    }

    fn binds(&mut self, sets: &'a Sets) -> Vec<cl::Bind> {
        sets.0.iter().map(|set| self.bind(set)).collect()
    }

    /// The value the core answered.
    fn value(&self, val: cl::Val) -> Value {
        match val {
            cl::Val::Bool(b) => Value::Bool(b),
            cl::Val::Nat(n) => {
                let decls = self.registry.decls;
                let at = place(n, decls.len() + self.values.len());
                match at.checked_sub(decls.len()) {
                    Some(given) => self.values[given].clone(),
                    None => decls[at].init.value(),
                }
            }
        }
    }

    /// The set the core answered.
    fn set(&self, bind: cl::Bind) -> Set {
        Set {
            id: self.registry.decls[place(bind.id, self.registry.decls.len())]
                .id
                .to_string(),
            value: self.value(bind.val),
        }
    }
}

impl Sets {
    /// The sets an agent writes to its cfg ([`Flag::Persist`]) or
    /// replicates ([`Flag::Replicate`]), in order, as the compiled core
    /// decides (`bend/cvar.bend` `written`).
    #[must_use]
    pub fn written(&self, registry: &Registry, flag: Flag) -> Sets {
        let mut refs = Refs::new(registry);
        let binds = refs.binds(self);
        Sets(
            cl::written(&registry.model, &binds, flag.model())
                .into_iter()
                .map(|bind| refs.set(bind))
                .collect(),
        )
    }

    /// The sets as cfg lines (`set <id> <value>`), one a line.
    #[must_use]
    pub fn render(&self) -> String {
        use std::fmt::Write as _;
        let mut out = String::new();
        for set in &self.0 {
            let command = Command::Set {
                id: set.id.clone(),
                value: value_text(&set.value),
            };
            // Writing to a String cannot fail.
            let _ = writeln!(out, "{command}");
        }
        out
    }
}

/// One agent of a family: its profile and its own sets.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct AgentLayer {
    pub profile: Sets,
    pub sets: Sets,
}

/// Where [`Cvars::execute`] writes its sets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Target {
    /// The config layer (loading config.cfg).
    Config,
    /// The last agent's profile (loading subagent.cfg, agents/<name>.cfg).
    Profile,
    /// The last agent's own sets (a session's `/set`).
    Sets,
}

/// Why a command did not apply.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CvarError {
    /// A line of a cfg that does not parse.
    Parse(ParseError),
    /// An alias that runs itself, or a run of an alias that does not exist.
    Expand(ExpandError),
    /// No cvar `id` is declared.
    Undeclared { id: String },
    /// `value` does not have the type of cvar `id`.
    BadValue {
        id: String,
        value: String,
        expected: String,
    },
    /// Cvar `id` is Global: an agent cannot set it; only the global config
    /// can (`/set --global`).
    Global { id: String },
    /// `toggle` of cvar `id`, which is not a Bool.
    NotBool { id: String },
    /// `action <id>` outside a key bind: only a client runs actions.
    Action { id: String },
}

impl fmt::Display for CvarError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CvarError::Parse(error) => write!(f, "{error}"),
            CvarError::Expand(error) => write!(f, "{error}"),
            CvarError::Undeclared { id } => write!(f, "no cvar `{id}`"),
            CvarError::BadValue {
                id,
                value,
                expected,
            } => write!(f, "`{value}` is not a value of `{id}` ({expected})"),
            CvarError::Global { id } => write!(
                f,
                "`{id}` is a Global cvar: a session cannot set it (use `/set --global`)"
            ),
            CvarError::NotBool { id } => write!(f, "`{id}` is not a bool: it cannot toggle"),
            CvarError::Action { id } => write!(f, "`action {id}` runs only from a key bind"),
        }
    }
}

impl std::error::Error for CvarError {}

/// Why a write of a cfg file did not happen.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CvarWriteError {
    /// The set is not valid (an undeclared cvar, a bad value, a Global
    /// cvar in an agent's cfg).
    Cvar(CvarError),
    /// The cfg file could not be read or written, or its name is not a
    /// plain file name.
    Io(String),
}

impl fmt::Display for CvarWriteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CvarWriteError::Cvar(error) => write!(f, "{error}"),
            CvarWriteError::Io(message) => write!(f, "{message}"),
        }
    }
}

impl std::error::Error for CvarWriteError {}

/// The values of one agent: the config layer and its family, root first
/// (the agent itself last).
#[derive(Debug, Clone)]
pub struct Cvars {
    registry: &'static Registry,
    config: Sets,
    family: Vec<AgentLayer>,
    /// The value of each declared cvar and whether a layer sets it, in
    /// table order, as the compiled core resolved them: one call after a
    /// change, on the first read.
    resolved: OnceLock<Vec<(Value, bool)>>,
}

impl PartialEq for Cvars {
    fn eq(&self, other: &Self) -> bool {
        self.registry == other.registry
            && self.config == other.config
            && self.family == other.family
    }
}

/// The layers of a [`Cvars`] as the core sees them.
struct Model<'a> {
    refs: Refs<'a>,
    config: Vec<cl::Bind>,
    family: Vec<(Vec<cl::Bind>, Vec<cl::Bind>)>,
}

impl<'a> Model<'a> {
    fn of(cvars: &'a Cvars) -> Self {
        let mut refs = Refs::new(cvars.registry);
        let config = refs.binds(&cvars.config);
        let family = cvars
            .family
            .iter()
            .map(|agent| (refs.binds(&agent.profile), refs.binds(&agent.sets)))
            .collect();
        Self {
            refs,
            config,
            family,
        }
    }

    fn chain(&self) -> Vec<cl::Agent<'_>> {
        self.family
            .iter()
            .map(|(profile, sets)| cl::Agent { profile, sets })
            .collect()
    }
}

impl Cvars {
    /// A root agent with no profile and no sets over `config`.
    #[must_use]
    pub fn new(registry: &'static Registry, config: Sets) -> Self {
        Self {
            registry,
            config,
            family: vec![AgentLayer::default()],
            resolved: OnceLock::new(),
        }
    }

    #[must_use]
    pub fn registry(&self) -> &'static Registry {
        self.registry
    }

    /// The config layer.
    #[must_use]
    pub fn config(&self) -> &Sets {
        &self.config
    }

    /// The family, root first.
    #[must_use]
    pub fn family(&self) -> &[AgentLayer] {
        &self.family
    }

    /// Replace the family (root first; an empty family is one root agent
    /// with no profile and no sets).
    pub fn set_family(&mut self, family: Vec<AgentLayer>) {
        self.family = family;
        if self.family.is_empty() {
            self.family.push(AgentLayer::default());
        }
        self.resolved.take();
    }

    /// The agent itself: the last of the family.
    #[must_use]
    pub fn agent(&self) -> &AgentLayer {
        self.family.last().unwrap_or(&EMPTY_AGENT)
    }

    /// The layer `target` names, to change.
    fn layer_mut(&mut self, target: Target) -> &mut Sets {
        self.resolved.take();
        if self.family.is_empty() {
            self.family.push(AgentLayer::default());
        }
        let last = self.family.len() - 1;
        match target {
            Target::Config => &mut self.config,
            Target::Profile => &mut self.family[last].profile,
            Target::Sets => &mut self.family[last].sets,
        }
    }

    /// A subagent of this agent: the same config, this family plus a new
    /// agent with no profile and no sets.
    #[must_use]
    pub fn child(&self) -> Self {
        let mut family = self.family.clone();
        family.push(AgentLayer::default());
        Self {
            registry: self.registry,
            config: self.config.clone(),
            family,
            resolved: OnceLock::new(),
        }
    }

    /// Every declared cvar's value and whether a layer sets it, in table
    /// order (`bend/cvar.bend` `value`, `layered`).
    fn resolved(&self) -> &[(Value, bool)] {
        self.resolved.get_or_init(|| {
            let model = Model::of(self);
            let values = cl::values(&self.registry.model, &model.config, &model.chain());
            assert_eq!(
                values.len(),
                self.registry.decls.len(),
                "the cvar core answered a value per cvar"
            );
            values
                .into_iter()
                .map(|resolved| (model.refs.value(resolved.value), resolved.layered))
                .collect()
        })
    }

    /// The resolved value of `decl`.
    ///
    /// # Panics
    ///
    /// When `decl` is not declared in this registry.
    fn resolved_of(&self, decl: &Decl) -> &(Value, bool) {
        match self.registry.index.get(decl.id) {
            Some(&at) => &self.resolved()[at],
            None => panic!("cvar `{}` is not in this registry", decl.id),
        }
    }

    /// The value of `decl` (`bend/cvar.bend` `value`).
    ///
    /// # Panics
    ///
    /// When `decl` is not declared in this registry.
    #[must_use]
    pub fn value(&self, decl: &Decl) -> Value {
        self.resolved_of(decl).0.clone()
    }

    /// The value a layer (config or an agent of the family) sets for
    /// `decl`; `None` when only the default applies (a reader whose unset
    /// means "the downstream default", such as the stream transport;
    /// `bend/cvar.bend` `layered`).
    ///
    /// # Panics
    ///
    /// When `decl` is not declared in this registry.
    #[must_use]
    pub fn layered(&self, decl: &Decl) -> Option<Value> {
        let (value, set) = self.resolved_of(decl);
        set.then(|| value.clone())
    }

    /// The value of cvar `id`; `None` when it is not declared.
    #[must_use]
    pub fn value_of(&self, id: &str) -> Option<Value> {
        let at = *self.registry.index.get(id)?;
        Some(self.resolved()[at].0.clone())
    }

    /// The value of a Bool cvar.
    ///
    /// # Panics
    ///
    /// When `decl` is not a Bool cvar (a getter reading the wrong type).
    #[must_use]
    pub fn bool(&self, decl: &Decl) -> bool {
        match self.value(decl) {
            Value::Bool(value) => value,
            other => panic!("cvar `{}` is not a bool: {other}", decl.id),
        }
    }

    /// The value of a Nat cvar.
    ///
    /// # Panics
    ///
    /// When `decl` is not a Nat cvar.
    #[must_use]
    pub fn nat(&self, decl: &Decl) -> u64 {
        match self.value(decl).as_u64() {
            Some(value) => value,
            None => panic!("cvar `{}` is not a whole number", decl.id),
        }
    }

    /// The value of a Text or Choice cvar.
    ///
    /// # Panics
    ///
    /// When `decl` is not a Text or Choice cvar.
    #[must_use]
    pub fn text(&self, decl: &Decl) -> String {
        match self.value(decl) {
            Value::String(value) => value,
            other => panic!("cvar `{}` is not a text: {other}", decl.id),
        }
    }

    /// The value of a Text cvar, `None` when empty (an optional setting
    /// that is unset) or only whitespace; trimmed.
    #[must_use]
    pub fn optional_text(&self, decl: &Decl) -> Option<String> {
        let text = self.text(decl);
        let trimmed = text.trim();
        (!trimmed.is_empty()).then(|| trimmed.to_string())
    }

    /// The value of a List cvar.
    ///
    /// # Panics
    ///
    /// When `decl` is not a List cvar.
    #[must_use]
    pub fn list(&self, decl: &Decl) -> Vec<String> {
        match self.value(decl) {
            Value::Array(items) => items
                .into_iter()
                .filter_map(|item| match item {
                    Value::String(text) => Some(text),
                    Value::Null
                    | Value::Bool(_)
                    | Value::Number(_)
                    | Value::Array(_)
                    | Value::Object(_) => None,
                })
                .collect(),
            other => panic!("cvar `{}` is not a list: {other}", decl.id),
        }
    }

    /// The values of the cvars clients see, in table order.
    #[must_use]
    pub fn replicated(&self) -> Vec<Set> {
        self.registry
            .decls()
            .iter()
            .filter(|decl| decl.replicate)
            .map(|decl| Set {
                id: decl.id.to_string(),
                value: self.value(decl),
            })
            .collect()
    }

    /// The set of `id` to `text` for a layer of `kind`: Rust reads `text`
    /// as a value of the cvar's type ([`CvarType::parse`]); the compiled
    /// core gives the verdict (`bend/cvar.bend` `check`).
    ///
    /// # Errors
    ///
    /// An undeclared cvar, a Global cvar in an agent layer, or a value of
    /// the wrong type.
    ///
    /// # Panics
    ///
    /// When the core calls a set valid or of the wrong type that it was
    /// sent as undeclared or unparsed (an inconsistent build).
    pub fn check(&self, kind: LayerKind, id: &str, text: &str) -> Result<Set, CvarError> {
        let found = self.registry.index.get(id).copied();
        let parsed = found.and_then(|at| self.registry.decls[at].ty.parse(text));
        let set = match (found, &parsed) {
            (Some(at), Some(value)) => cl::Bind {
                id: at as u64,
                val: self.registry.decls[at].model_val(value, 0),
            },
            (Some(at), None) => cl::Bind {
                id: at as u64,
                val: match self.registry.decls[at].ty {
                    CvarType::Bool => cl::Val::Nat(0),
                    _ => cl::Val::Bool(false),
                },
            },
            (None, _) => cl::Bind {
                id: self.registry.decls.len() as u64,
                val: cl::Val::Nat(0),
            },
        };
        let id = id.to_string();
        match (
            cl::check(&self.registry.model, kind.model(), set),
            found,
            parsed,
        ) {
            (cl::Check::Undeclared, _, _) => Err(CvarError::Undeclared { id }),
            (cl::Check::Global, _, _) => Err(CvarError::Global { id }),
            (cl::Check::BadType, Some(at), _) => Err(CvarError::BadValue {
                id,
                value: text.to_string(),
                expected: self.registry.decls[at].ty.name(),
            }),
            (cl::Check::Valid, Some(_), Some(value)) => Ok(Set { id, value }),
            (verdict, _, _) => {
                panic!("the cvar core answered {verdict:?} for `{id}` = `{text}`, which it was not sent")
            }
        }
    }

    /// Run `commands` into `target`: a `set` adds a set, a `toggle` adds
    /// the set that flips the cvar's current value, an `alias` defines an
    /// alias, a `bind` adds a bind, and a run of an alias runs its
    /// commands (expanded first, so a cycle or an unknown alias runs
    /// nothing of the list). A command that fails is reported and skipped;
    /// the others still apply.
    pub fn execute(
        &mut self,
        target: Target,
        commands: &[Command],
        aliases: &mut Aliases,
        binds: &mut Binds,
    ) -> Vec<CvarError> {
        let kind = match target {
            Target::Config => LayerKind::Config,
            Target::Profile | Target::Sets => LayerKind::Agent,
        };
        let mut errors = Vec::new();
        for command in commands {
            let outcome = match command {
                Command::Set { id, value } => self.check(kind, id, value).map(|set| vec![set]),
                Command::Toggle { id } => self.toggled(kind, id).map(|set| vec![set]),
                Command::Alias { name, body } => {
                    aliases.define(name.clone(), body.clone());
                    Ok(Vec::new())
                }
                Command::Bind { key, body } => {
                    binds.push(key.clone(), body.clone());
                    Ok(Vec::new())
                }
                Command::Action { id } => Err(CvarError::Action { id: id.clone() }),
                Command::Run { .. } => match expand(std::slice::from_ref(command), aliases) {
                    Ok(expanded) => {
                        errors.extend(self.execute(target, &expanded, aliases, binds));
                        Ok(Vec::new())
                    }
                    Err(error) => Err(CvarError::Expand(error)),
                },
            };
            match outcome {
                Ok(sets) => self.layer_mut(target).0.extend(sets),
                Err(error) => errors.push(error),
            }
        }
        errors
    }

    /// The set that flips Bool cvar `id`, as the compiled core decides
    /// (`bend/cvar.bend` `tog`): it flips the value the agent has, its
    /// inherited values included.
    fn toggled(&self, kind: LayerKind, id: &str) -> Result<Set, CvarError> {
        let number = self
            .registry
            .index
            .get(id)
            .map_or(self.registry.decls.len(), |at| *at);
        let model = Model::of(self);
        let id = id.to_string();
        match cl::toggle(
            &self.registry.model,
            &model.config,
            &model.chain(),
            kind.model(),
            number as u64,
        ) {
            cl::Toggle::Undeclared => Err(CvarError::Undeclared { id }),
            cl::Toggle::Global => Err(CvarError::Global { id }),
            cl::Toggle::NotBool => Err(CvarError::NotBool { id }),
            cl::Toggle::Flip(cl::Bind {
                val: cl::Val::Bool(value),
                ..
            }) => Ok(Set {
                id,
                value: Value::Bool(value),
            }),
            cl::Toggle::Flip(set) => {
                panic!("the cvar core flipped `{id}` to {set:?}, which is not a Bool")
            }
        }
    }
}

static EMPTY_AGENT: LazyLock<AgentLayer> = LazyLock::new(AgentLayer::default);

/// The config layer of a settings document (the merged `settings.json`):
/// Rust finds each declared cvar's key (a `null` is no value); the
/// compiled core keeps, in table order, the value of a Local cvar from
/// `merged` and of a Global cvar from `global_only` alone (never from a
/// project), when it has the cvar's type (`bend/cvar.bend` `document`).
#[must_use]
pub fn document_sets(registry: &Registry, merged: &Value, global_only: &Value) -> Sets {
    let mut refs = Refs::new(registry);
    let mut sets_of = |document| -> Vec<cl::Bind> {
        let mut binds = Vec::new();
        for (at, decl) in registry.decls.iter().enumerate() {
            let found = decl
                .id
                .split('.')
                .try_fold(document, |node: &Value, key| node.get(key));
            if let Some(value) = found.filter(|value| !value.is_null()) {
                binds.push(cl::Bind {
                    id: at as u64,
                    val: refs.value_of(at, value),
                });
            }
        }
        binds
    };
    let merged = sets_of(merged);
    let global = sets_of(global_only);
    Sets(
        cl::document(&registry.model, &merged, &global)
            .into_iter()
            .map(|bind| refs.set(bind))
            .collect(),
    )
}
