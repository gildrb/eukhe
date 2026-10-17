//! Settings as console variables (docs/control.md S4; the model is
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

use std::collections::HashMap;
use std::fmt;
use std::sync::LazyLock;

use eukhe_types::cvar::{expand, Aliases, Binds, Command, ExpandError, ParseError};
use serde::{Deserialize, Serialize};
use serde_json::Value;

pub mod table;

#[cfg(test)]
mod bridge;
#[cfg(test)]
mod tests;

/// The type of a cvar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CvarType {
    Bool,
    /// A whole number `>= 0`.
    Nat,
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

impl Decl {
    fn flag(&self, flag: Flag) -> bool {
        match flag {
            Flag::Persist => self.persist,
            Flag::Replicate => self.replicate,
        }
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
}

impl Registry {
    /// The registry of `decls`.
    ///
    /// # Errors
    ///
    /// The first duplicate id or default of the wrong type.
    pub fn new(decls: &'static [Decl]) -> Result<Self, RegistryError> {
        let mut index = HashMap::with_capacity(decls.len());
        for (at, decl) in decls.iter().enumerate() {
            if index.insert(decl.id, at).is_some() {
                return Err(RegistryError::Duplicate { id: decl.id });
            }
            if !decl.ty.admits(&decl.init.value()) {
                return Err(RegistryError::BadDefault { id: decl.id });
            }
        }
        Ok(Self { decls, index })
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

/// `value` is a valid set of `decl` in a layer of `kind`.
fn valid(decl: &Decl, kind: LayerKind, value: &Value) -> bool {
    let scoped = match kind {
        LayerKind::Config => true,
        LayerKind::Agent => decl.scope == CvarScope::Local,
    };
    scoped && decl.ty.admits(value)
}

impl Sets {
    /// The last valid set of `decl` in this layer.
    #[must_use]
    pub fn last(&self, decl: &Decl, kind: LayerKind) -> Option<&Value> {
        self.0
            .iter()
            .rev()
            .find(|set| set.id == decl.id && valid(decl, kind, &set.value))
            .map(|set| &set.value)
    }

    /// The sets an agent writes to its cfg ([`Flag::Persist`]) or
    /// replicates ([`Flag::Replicate`]): its valid sets of cvars with the
    /// flag, in order (`bend/cvar.bend` `written`).
    #[must_use]
    pub fn written(&self, registry: &Registry, flag: Flag) -> Sets {
        Sets(
            self.0
                .iter()
                .filter(|set| {
                    registry.find(&set.id).is_some_and(|decl| {
                        decl.flag(flag) && valid(decl, LayerKind::Agent, &set.value)
                    })
                })
                .cloned()
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
#[derive(Debug, Clone, PartialEq)]
pub struct Cvars {
    registry: &'static Registry,
    config: Sets,
    family: Vec<AgentLayer>,
}

impl Cvars {
    /// A root agent with no profile and no sets over `config`.
    #[must_use]
    pub fn new(registry: &'static Registry, config: Sets) -> Self {
        Self {
            registry,
            config,
            family: vec![AgentLayer::default()],
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
    }

    /// The agent itself: the last of the family.
    #[must_use]
    pub fn agent(&self) -> &AgentLayer {
        self.family.last().unwrap_or(&EMPTY_AGENT)
    }

    fn agent_mut(&mut self) -> &mut AgentLayer {
        if self.family.is_empty() {
            self.family.push(AgentLayer::default());
        }
        let last = self.family.len() - 1;
        &mut self.family[last]
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
        }
    }

    /// The value of `decl` (`bend/cvar.bend` `value`).
    #[must_use]
    pub fn value(&self, decl: &Decl) -> Value {
        self.layered(decl).unwrap_or_else(|| decl.init.value())
    }

    /// The value a layer (config or an agent of the family) sets for
    /// `decl`; `None` when only the default applies (a reader whose unset
    /// means "the downstream default", such as the stream transport).
    #[must_use]
    pub fn layered(&self, decl: &Decl) -> Option<Value> {
        let mut value = self.config.last(decl, LayerKind::Config).cloned();
        for agent in &self.family {
            if let Some(set) = agent
                .sets
                .last(decl, LayerKind::Agent)
                .or_else(|| agent.profile.last(decl, LayerKind::Agent))
            {
                value = Some(set.clone());
            }
        }
        value
    }

    /// The value of cvar `id`; `None` when it is not declared.
    #[must_use]
    pub fn value_of(&self, id: &str) -> Option<Value> {
        self.registry.find(id).map(|decl| self.value(decl))
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

    /// The set of `id` to `text`, checked against its declaration for a
    /// layer of `kind`.
    ///
    /// # Errors
    ///
    /// An undeclared cvar, a value of the wrong type, or a Global cvar in an
    /// agent layer.
    pub fn check(&self, kind: LayerKind, id: &str, text: &str) -> Result<Set, CvarError> {
        let decl = self
            .registry
            .find(id)
            .ok_or_else(|| CvarError::Undeclared { id: id.to_string() })?;
        if kind == LayerKind::Agent && decl.scope == CvarScope::Global {
            return Err(CvarError::Global { id: id.to_string() });
        }
        let value = decl.ty.parse(text).ok_or_else(|| CvarError::BadValue {
            id: id.to_string(),
            value: text.to_string(),
            expected: decl.ty.name(),
        })?;
        Ok(Set {
            id: id.to_string(),
            value,
        })
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
                Ok(sets) => {
                    let layer = match target {
                        Target::Config => &mut self.config,
                        Target::Profile => &mut self.agent_mut().profile,
                        Target::Sets => &mut self.agent_mut().sets,
                    };
                    layer.0.extend(sets);
                }
                Err(error) => errors.push(error),
            }
        }
        errors
    }

    /// The set that flips Bool cvar `id` (`bend/cvar.bend` `flip`).
    fn toggled(&self, kind: LayerKind, id: &str) -> Result<Set, CvarError> {
        let decl = self
            .registry
            .find(id)
            .ok_or_else(|| CvarError::Undeclared { id: id.to_string() })?;
        if kind == LayerKind::Agent && decl.scope == CvarScope::Global {
            return Err(CvarError::Global { id: id.to_string() });
        }
        match self.value(decl) {
            Value::Bool(value) => Ok(Set {
                id: id.to_string(),
                value: Value::Bool(!value),
            }),
            Value::Null
            | Value::Number(_)
            | Value::String(_)
            | Value::Array(_)
            | Value::Object(_) => Err(CvarError::NotBool { id: id.to_string() }),
        }
    }
}

static EMPTY_AGENT: LazyLock<AgentLayer> = LazyLock::new(AgentLayer::default);

/// The config layer of a settings document (the merged `settings.json`):
/// a set for each declared cvar the document holds with a value of its
/// type, in table order. `global_only` is the global document: Global
/// cvars come from it alone, never from a project.
#[must_use]
pub fn document_sets(registry: &Registry, merged: &Value, global_only: &Value) -> Sets {
    let mut sets = Vec::new();
    for decl in registry.decls() {
        let source = match decl.scope {
            CvarScope::Global => global_only,
            CvarScope::Local => merged,
        };
        let found = decl
            .id
            .split('.')
            .try_fold(source, |node, key| node.get(key));
        if let Some(value) = found.filter(|value| !value.is_null() && decl.ty.admits(value)) {
            sets.push(Set {
                id: decl.id.to_string(),
                value: value.clone(),
            });
        }
    }
    Sets(sets)
}
