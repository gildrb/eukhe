//! Global key binds with TS DEFAULT_* defaults.
//!
//! Port of `packages/tui/src/keybindings.ts` + `coding-agent/src/core/keybindings.ts`,
//! on the console-variable command language (`eukhe_types::cvar`). The
//! defaults below are the TS product's DEFAULT_* tables verbatim; each
//! default key runs `action <id>`. The user's `bind` and `alias` lines live
//! in `<agentDir>/binds.cfg` and come before the defaults: the first bind
//! of a key wins, and an empty bind (`bind ctrl+o ""`) runs nothing. A
//! legacy `keybindings.json` (TS parse semantics: legacy names migrate,
//! malformed values drop, an empty array disables a binding) is imported
//! once into a new `binds.cfg`.

use eukhe_bend::rules::cvar::Presses;
use eukhe_types::cvar::{parse_script, Aliases, Binds, Command, ExpandError};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeybindingDefinition {
    pub default_keys: &'static [&'static str],
    pub default_key_scope: Option<&'static str>,
}

macro_rules! def {
    ($keys:expr) => {
        KeybindingDefinition {
            default_keys: $keys,
            default_key_scope: None,
        }
    };
    ($keys:expr, scope $scope:expr) => {
        KeybindingDefinition {
            default_keys: $keys,
            default_key_scope: Some($scope),
        }
    };
}

mod definitions;

pub use definitions::{APP_KEYBINDINGS, TUI_KEYBINDINGS};

/// A legacy `keybindings.json`: the keys per action id (an empty list
/// disables the action).
pub type KeybindingsConfig = BTreeMap<String, Vec<String>>;

/// A parsed key id (TS `parseKeyId`): the modifier set plus the base key,
/// lowercase, so matching is case- and order-insensitive exactly like
/// `matchesKey` (a config value `Ctrl+O` matches the `ctrl+o` a key event
/// decodes to; `ctrl+shift+down` matches the event id `shift+ctrl+down`).
#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedKeyId {
    key: String,
    ctrl: bool,
    shift: bool,
    alt: bool,
    super_key: bool,
}

/// TS `parseKeyId`: split on `+`, the last part is the key, the rest are
/// modifiers; `esc` and `escape` name the same key. An empty key id or
/// trailing `+` parses to `None` (never matches).
fn parse_key_id(id: &str) -> Option<ParsedKeyId> {
    let parts: Vec<&str> = id.split('+').collect();
    let raw_key = parts.last()?.trim().to_lowercase();
    if raw_key.is_empty() {
        return None;
    }
    let key = match raw_key.as_str() {
        "esc" => "escape".to_string(),
        other => other.to_string(),
    };
    let mut parsed = ParsedKeyId {
        key,
        ctrl: false,
        shift: false,
        alt: false,
        super_key: false,
    };
    for part in &parts {
        match part.trim().to_lowercase().as_str() {
            "ctrl" => parsed.ctrl = true,
            "shift" => parsed.shift = true,
            "alt" => parsed.alt = true,
            "super" => parsed.super_key = true,
            _ => {}
        }
    }
    Some(parsed)
}

/// The legacy pre-namespaced keybinding ids and their current names (TS
/// `KEYBINDING_NAME_MIGRATIONS` in `coding-agent/src/core/keybindings.ts`).
pub const KEYBINDING_NAME_MIGRATIONS: &[(&str, &str)] = &[
    ("app.message.dequeue", "app.message.navigateOlder"),
    ("cursorUp", "tui.editor.cursorUp"),
    ("cursorDown", "tui.editor.cursorDown"),
    ("cursorLeft", "tui.editor.cursorLeft"),
    ("cursorRight", "tui.editor.cursorRight"),
    ("cursorWordLeft", "tui.editor.cursorWordLeft"),
    ("cursorWordRight", "tui.editor.cursorWordRight"),
    ("cursorLineStart", "tui.editor.cursorLineStart"),
    ("cursorLineEnd", "tui.editor.cursorLineEnd"),
    ("jumpForward", "tui.editor.jumpForward"),
    ("jumpBackward", "tui.editor.jumpBackward"),
    ("pageUp", "tui.editor.pageUp"),
    ("pageDown", "tui.editor.pageDown"),
    ("deleteCharBackward", "tui.editor.deleteCharBackward"),
    ("deleteCharForward", "tui.editor.deleteCharForward"),
    ("deleteWordBackward", "tui.editor.deleteWordBackward"),
    ("deleteWordForward", "tui.editor.deleteWordForward"),
    ("deleteToLineStart", "tui.editor.deleteToLineStart"),
    ("deleteToLineEnd", "tui.editor.deleteToLineEnd"),
    ("yank", "tui.editor.yank"),
    ("yankPop", "tui.editor.yankPop"),
    ("undo", "tui.editor.undo"),
    ("newLine", "tui.input.newLine"),
    ("submit", "tui.input.submit"),
    ("tab", "tui.input.tab"),
    ("copy", "tui.input.copy"),
    ("selectUp", "tui.select.up"),
    ("selectDown", "tui.select.down"),
    ("selectPageUp", "tui.select.pageUp"),
    ("selectPageDown", "tui.select.pageDown"),
    ("selectConfirm", "tui.select.confirm"),
    ("selectCancel", "tui.select.cancel"),
    ("interrupt", "app.interrupt"),
    ("clear", "app.clear"),
    ("clearInput", "app.input.clear"),
    ("exit", "app.exit"),
    ("suspend", "app.suspend"),
    ("selectModel", "app.model.select"),
    ("expandTools", "app.tools.expand"),
    ("focusSubagents", "app.subagents.focus"),
    ("externalEditor", "app.editor.external"),
    ("followUp", "app.message.followUp"),
    ("dequeue", "app.message.navigateOlder"),
    ("pasteImage", "app.clipboard.pasteImage"),
    ("newSession", "app.session.new"),
    ("tree", "app.session.tree"),
    ("fork", "app.session.fork"),
    ("resume", "app.session.resume"),
    ("agentsBack", "app.agents.back"),
    ("agentsReply", "app.agents.reply"),
    ("agentsNew", "app.agents.new"),
    ("agentsDelete", "app.agents.delete"),
    ("agentsProgram", "app.agents.program"),
    ("agentsRename", "app.agents.rename"),
    ("treeFoldOrUp", "app.tree.foldOrUp"),
    ("treeUnfoldOrDown", "app.tree.unfoldOrDown"),
    ("treeEditLabel", "app.tree.editLabel"),
    ("treeToggleLabelTimestamp", "app.tree.toggleLabelTimestamp"),
];

fn legacy_migration(id: &str) -> Option<&'static str> {
    KEYBINDING_NAME_MIGRATIONS
        .iter()
        .find(|(legacy, _)| *legacy == id)
        .map(|(_, current)| *current)
}

/// The config object as an ordered entry list (`serde_json` maps sort keys,
/// so the TS object order -- definition ids first, extras sorted after -- is
/// carried by this vector).
pub type OrderedConfig = Vec<(String, serde_json::Value)>;

/// TS `migrateKeybindingsConfig`: rename legacy ids (a legacy entry is
/// dropped when its current name also exists) and order the object with
/// known ids first in definition order, extras sorted after. Values are
/// carried over unchanged (filtering happens in [`to_keybindings_config`]).
fn migrate_keybindings_config(raw: &serde_json::Map<String, serde_json::Value>) -> OrderedConfig {
    let mut config: OrderedConfig = Vec::new();
    for (key, value) in raw {
        let Some(next_key) = legacy_migration(key) else {
            config.push((key.clone(), value.clone()));
            continue;
        };
        if raw.contains_key(next_key) {
            // The current name is authoritative; the legacy entry drops.
            continue;
        }
        config.push((next_key.to_string(), value.clone()));
    }
    order_keybindings_config(config)
}

/// TS `orderKeybindingsConfig`: known ids first in definition order, the
/// rest sorted.
fn order_keybindings_config(mut config: OrderedConfig) -> OrderedConfig {
    let mut ordered: OrderedConfig = Vec::new();
    for (id, _) in definitions() {
        if let Some(position) = config.iter().position(|(key, _)| key == id) {
            let (_, value) = config.remove(position);
            ordered.push((id.to_string(), value));
        }
    }
    config.sort_by(|a, b| a.0.cmp(&b.0));
    ordered.extend(config);
    ordered
}

/// TS `toKeybindingsConfig`: a value is a key list only when it is a string
/// or an array whose every entry is a string (an empty array disables the
/// binding); anything else drops.
fn to_keybindings_config(value: &serde_json::Value) -> Option<Vec<String>> {
    match value {
        serde_json::Value::String(key) => Some(vec![key.clone()]),
        serde_json::Value::Array(entries) => {
            let keys: Option<Vec<String>> = entries
                .iter()
                .map(|entry| entry.as_str().map(str::to_string))
                .collect();
            keys
        }
        _ => None,
    }
}

/// The legacy `keybindings.json` at `path` (TS `loadFromFile`): legacy
/// names migrated, then filtered to the well-formed key lists. A missing
/// file, malformed JSON, or a non-object document read as empty.
fn load_legacy_config(path: &Path) -> KeybindingsConfig {
    let Some(raw) = std::fs::read(path)
        .ok()
        .and_then(|bytes| serde_json::from_slice::<serde_json::Value>(&bytes).ok())
        .and_then(|parsed| parsed.as_object().cloned())
    else {
        return KeybindingsConfig::new();
    };
    let mut bindings = KeybindingsConfig::new();
    for (id, value) in &migrate_keybindings_config(&raw) {
        if let Some(keys) = to_keybindings_config(value) {
            bindings.insert(id.clone(), keys);
        }
    }
    bindings
}

/// The definitions in table order (TUI first, then app).
fn definitions() -> impl Iterator<Item = &'static (&'static str, KeybindingDefinition)> {
    TUI_KEYBINDINGS.iter().chain(APP_KEYBINDINGS.iter())
}

/// The keys of each definition (in table order) that a legacy
/// `keybindings.json` gave it (TS `KeybindingsManager.rebuild()`): a user
/// entry replaces the definition's keys outright; within one default
/// scope, a key a user entry adds (outside its own defaults) is freed
/// from the other defaults of that scope. Unknown ids claim nothing.
fn legacy_resolution(user_bindings: &KeybindingsConfig) -> Vec<(&'static str, Vec<&str>)> {
    // The scopes of the user entries that add each key.
    let mut added_claims: BTreeMap<&str, Vec<&'static str>> = BTreeMap::new();
    for (id, keys) in user_bindings {
        let Some((_, definition)) = definitions().find(|(known, _)| known == id) else {
            continue;
        };
        let Some(scope) = definition.default_key_scope else {
            continue;
        };
        for key in keys {
            if !definition.default_keys.contains(&key.as_str()) {
                added_claims.entry(key).or_default().push(scope);
            }
        }
    }
    definitions()
        .map(|(id, definition)| {
            let keys = match user_bindings.get(*id) {
                Some(user_keys) => user_keys.iter().map(String::as_str).collect(),
                None => definition
                    .default_keys
                    .iter()
                    .copied()
                    .filter(|key| {
                        definition.default_key_scope.is_none_or(|scope| {
                            !added_claims
                                .get(key)
                                .is_some_and(|scopes| scopes.contains(&scope))
                        })
                    })
                    .collect(),
            };
            (*id, keys)
        })
        .collect()
}

/// The `bind` commands that reproduce a legacy `keybindings.json` over the
/// default binds: one for every key whose actions differ from its default
/// actions, of exactly the actions the legacy file gave it (`""` when
/// none) -- a rebound action's new key, the default key it left (or that
/// a `[]` entry emptied), the same-scope default an added key freed. The
/// file's keys come first, in its order, then the default keys. A key the
/// file left alone gets no bind, so a key several actions share by
/// default (Enter, the arrows, Ctrl+O) keeps every action the file did
/// not take off it.
#[must_use]
pub fn legacy_binds(user_bindings: &KeybindingsConfig) -> Vec<Command> {
    // Per definition: its id, its legacy keys, its default keys (normal
    // forms).
    let table: Vec<(&str, BTreeSet<String>, BTreeSet<String>)> = legacy_resolution(user_bindings)
        .into_iter()
        .zip(definitions())
        .map(|((id, legacy), (_, definition))| {
            (
                id,
                legacy.into_iter().filter_map(canonical_key).collect(),
                definition
                    .default_keys
                    .iter()
                    .copied()
                    .filter_map(canonical_key)
                    .collect(),
            )
        })
        .collect();
    let candidates =
        user_bindings.values().flatten().map(String::as_str).chain(
            definitions().flat_map(|(_, definition)| definition.default_keys.iter().copied()),
        );
    let mut seen = BTreeSet::new();
    let mut binds = Vec::new();
    for written in candidates {
        let Some(key) = canonical_key(written) else {
            continue;
        };
        if !seen.insert(key.clone()) {
            continue;
        }
        let legacy: Vec<&str> = table
            .iter()
            .filter(|(_, legacy, _)| legacy.contains(&key))
            .map(|(id, _, _)| *id)
            .collect();
        let default: Vec<&str> = table
            .iter()
            .filter(|(_, _, default)| default.contains(&key))
            .map(|(id, _, _)| *id)
            .collect();
        if legacy != default {
            binds.push(Command::Bind {
                key: written.to_string(),
                body: legacy
                    .into_iter()
                    .map(|id| Command::Action { id: id.to_string() })
                    .collect(),
            });
        }
    }
    binds
}

/// The user binds file in the agent dir.
const BINDS_FILE: &str = "binds.cfg";

/// The legacy keybindings file `binds.cfg` replaces.
const LEGACY_FILE: &str = "keybindings.json";

/// The text of `<agentDir>/binds.cfg`, and what went wrong reading it.
/// When it does not exist and a legacy `keybindings.json` does, the legacy
/// bindings are imported once: their [`legacy_binds`] are written as a new
/// `binds.cfg` (never over a file that appeared meanwhile) and
/// `keybindings.json` stays in place. Once `binds.cfg` exists it is the
/// only source. A `binds.cfg` that exists but cannot be read binds nothing
/// (a warning says so); a failed import write still binds the imported
/// text for this run (a warning says so, and the next start imports
/// again).
fn read_binds_file(agent_dir: &Path) -> (String, Option<String>) {
    let path = agent_dir.join(BINDS_FILE);
    match std::fs::read_to_string(&path) {
        Ok(text) => return (text, None),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => {
            return (
                String::new(),
                Some(format!(
                    "{} could not be read ({error}): no user key bind applies",
                    path.display()
                )),
            )
        }
    }
    let legacy = agent_dir.join(LEGACY_FILE);
    if !legacy.exists() {
        return (String::new(), None);
    }
    let mut text = format!("# Key binds, imported from {LEGACY_FILE}.\n");
    for bind in legacy_binds(&load_legacy_config(&legacy)) {
        text.push_str(&bind.to_string());
        text.push('\n');
    }
    let written = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .and_then(|mut file| std::io::Write::write_all(&mut file, text.as_bytes()));
    let warning = written.err().map(|error| {
        format!(
            "the {LEGACY_FILE} binds could not be written to {} ({error}): they apply to this run only",
            path.display()
        )
    });
    (text, warning)
}

/// A key id in its normal form (the [`parse_key_id`] semantics): the
/// modifiers in a fixed order, then the key, lowercase; two ids that
/// match each other have the same normal form. `None` for an id that
/// never matches.
fn canonical_key(id: &str) -> Option<String> {
    let parsed = parse_key_id(id)?;
    let mut key = String::new();
    for (held, name) in [
        (parsed.ctrl, "ctrl+"),
        (parsed.shift, "shift+"),
        (parsed.alt, "alt+"),
        (parsed.super_key, "super+"),
    ] {
        if held {
            key.push_str(name);
        }
    }
    key.push_str(&parsed.key);
    Some(key)
}

/// The key binds: the user binds (`<agentDir>/binds.cfg`, in order), then
/// the default binds (each definition's default keys run `action <id>`;
/// the definitions sharing a default key share its bind, and the context
/// a key is pressed in picks among them). The first bind of a key wins,
/// so a user bind of a key shadows its default actions, and an empty
/// bind leaves the key running nothing. Keys are bound and looked up in
/// their [`canonical_key`] form. The aliases of `binds.cfg` expand a
/// press.
#[derive(Debug, Clone)]
pub struct KeybindingsManager {
    binds: Binds,
    /// How many of `binds` are the user's (they come first).
    user_binds: usize,
    /// The presses of `binds` with the `binds.cfg` aliases, as the
    /// compiled core runs them (`bend/cvar.bend` `press`).
    presses: Presses,
    /// The key as its first user bind spells it (hint labels; a default
    /// key is labeled as its definition spells it).
    labels: BTreeMap<String, String>,
    /// The actions a press of each bound key runs (none when its
    /// expansion fails).
    actions: BTreeMap<String, Vec<String>>,
    /// The agent dir whose `binds.cfg` [`reload`](Self::reload) re-reads.
    agent_dir: Option<PathBuf>,
    /// What went wrong reading `binds.cfg` ([`Self::warnings`]).
    warnings: Vec<String>,
}

impl KeybindingsManager {
    /// The default binds only.
    #[must_use]
    pub fn new() -> Self {
        Self::with_binds(&[], None)
    }

    /// The default binds under the binds a legacy `keybindings.json` with
    /// `user_bindings` imports to ([`legacy_binds`]).
    #[must_use]
    pub fn with_user_bindings(user_bindings: &KeybindingsConfig) -> Self {
        Self::with_binds(&legacy_binds(user_bindings), None)
    }

    /// The binds of `<agentDir>/binds.cfg` (imported once from a legacy
    /// `keybindings.json`), remembered for [`reload`](Self::reload). A
    /// problem reading or importing the file is in
    /// [`warnings`](Self::warnings). Each line that does not parse is in
    /// the warnings too. A `bind` whose key does not parse is in the
    /// warnings. An `action` of a bind or alias body that is not a known
    /// action is in the warnings. A `set`, `toggle`, `action` or alias
    /// run at the top level of the file is in the warnings as ignored.
    #[must_use]
    pub fn create(agent_dir: &Path) -> Self {
        let (text, read_warning) = read_binds_file(agent_dir);
        let mut script = Vec::new();
        let mut warnings = Vec::new();
        for (at, line) in text.lines().enumerate() {
            let number = at + 1;
            let (commands, errors) = parse_script(line);
            for mut error in errors {
                error.line = number;
                warnings.push(format!("{BINDS_FILE} {error}: the line is ignored"));
            }
            for command in commands {
                let body = match &command {
                    Command::Bind { key, body } => {
                        if canonical_key(key).is_none() {
                            warnings.push(format!(
                                "{BINDS_FILE} line {number}: key `{key}` does not parse: the bind is ignored"
                            ));
                        }
                        Some(body)
                    }
                    Command::Alias { body, .. } => Some(body),
                    Command::Set { .. }
                    | Command::Toggle { .. }
                    | Command::Action { .. }
                    | Command::Run { .. } => {
                        warnings.push(format!(
                            "{BINDS_FILE} line {number}: `{command}` is ignored (only `bind` and `alias` apply)"
                        ));
                        None
                    }
                };
                let mut pending: Vec<&Command> = body.into_iter().flatten().collect();
                while let Some(inner) = pending.pop() {
                    match inner {
                        Command::Action { id } => {
                            if !definitions().any(|(known, _)| *known == id.as_str()) {
                                warnings.push(format!(
                                    "{BINDS_FILE} line {number}: action `{id}` is unknown"
                                ));
                            }
                        }
                        Command::Bind { body, .. } | Command::Alias { body, .. } => {
                            pending.extend(body);
                        }
                        Command::Set { .. } | Command::Toggle { .. } | Command::Run { .. } => {}
                    }
                }
                script.push(command);
            }
        }
        let mut manager = Self::with_binds(&script, Some(agent_dir.to_path_buf()));
        manager.warnings.extend(read_warning);
        manager.warnings.extend(warnings);
        manager
    }

    /// Re-read `binds.cfg` (a no-op for a manager without an agent dir).
    pub fn reload(&mut self) {
        if let Some(agent_dir) = self.agent_dir.take() {
            *self = Self::create(&agent_dir);
        }
    }

    /// What went wrong reading `binds.cfg` at the last
    /// [`create`](Self::create) or [`reload`](Self::reload), for the user.
    #[must_use]
    pub fn warnings(&self) -> &[String] {
        &self.warnings
    }

    /// The `bind` and `alias` commands of `script` over the default binds
    /// (a `binds.cfg` line of any other command binds nothing).
    fn with_binds(script: &[Command], agent_dir: Option<PathBuf>) -> Self {
        let mut binds = Binds::default();
        let mut aliases = Aliases::default();
        let mut labels = BTreeMap::new();
        let mut user_binds = 0;
        for command in script {
            match command {
                Command::Bind { key, body } => {
                    if let Some(canonical) = canonical_key(key) {
                        labels
                            .entry(canonical.clone())
                            .or_insert_with(|| key.clone());
                        binds.push(canonical, body.clone());
                        user_binds += 1;
                    }
                }
                Command::Alias { name, body } => aliases.define(name.clone(), body.clone()),
                Command::Set { .. }
                | Command::Toggle { .. }
                | Command::Action { .. }
                | Command::Run { .. } => {}
            }
        }
        let mut defaults: Vec<(String, Vec<Command>)> = Vec::new();
        for (id, definition) in definitions() {
            for written in definition.default_keys {
                let Some(key) = canonical_key(written) else {
                    continue;
                };
                let action = Command::Action { id: id.to_string() };
                match defaults.iter_mut().find(|(known, _)| *known == key) {
                    Some((_, body)) => body.push(action),
                    None => defaults.push((key, vec![action])),
                }
            }
        }
        for (key, body) in defaults {
            binds.push(key, body);
        }
        let presses = Presses::new(&binds, &aliases);
        let mut actions: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (key, _) in binds.iter() {
            if actions.contains_key(key) {
                continue;
            }
            let ids = presses
                .press(key)
                .map(|commands| {
                    commands
                        .into_iter()
                        .filter_map(|command| match command {
                            Command::Action { id } => Some(id),
                            Command::Set { .. }
                            | Command::Toggle { .. }
                            | Command::Alias { .. }
                            | Command::Bind { .. }
                            | Command::Run { .. } => None,
                        })
                        .collect()
                })
                .unwrap_or_default();
            actions.insert(key.to_string(), ids);
        }
        Self {
            binds,
            user_binds,
            presses,
            labels,
            actions,
            agent_dir,
            warnings: Vec::new(),
        }
    }

    /// The commands a press of `data` runs (`eukhe_bend::rules::cvar`,
    /// `bend/cvar.bend` `press`): its winning bind expanded with the
    /// `binds.cfg` aliases; none for an unbound or malformed key.
    ///
    /// # Errors
    ///
    /// The bind runs an alias that cycles or does not exist.
    pub fn press(&self, data: &str) -> Result<Vec<Command>, ExpandError> {
        match canonical_key(data) {
            Some(key) => self.presses.press(&key),
            None => Ok(Vec::new()),
        }
    }

    /// TS `matches` (via `matchesKey`): a press of `data` runs the action
    /// `keybinding`; matching is case- and modifier-order-insensitive.
    #[must_use]
    pub fn matches(&self, data: &str, keybinding: &str) -> bool {
        canonical_key(data)
            .and_then(|key| self.actions.get(&key))
            .is_some_and(|actions| actions.iter().any(|id| id == keybinding))
    }

    /// The keys whose press runs the action `keybinding`: the definition's
    /// default keys in its order (as it spells them), then the user binds'
    /// keys in bind order (as the user spells them).
    #[must_use]
    pub fn get_keys(&self, keybinding: &str) -> Vec<String> {
        let default_keys = definitions()
            .find(|(id, _)| *id == keybinding)
            .map_or(&[][..], |(_, definition)| definition.default_keys);
        let user_keys = self
            .binds
            .iter()
            .take(self.user_binds)
            .filter_map(|(key, _)| Some((key.to_string(), self.labels.get(key)?.clone())));
        let default_keys = default_keys
            .iter()
            .filter_map(|written| Some((canonical_key(written)?, (*written).to_string())));
        let mut seen = BTreeSet::new();
        default_keys
            .chain(user_keys)
            .filter(|(key, _)| {
                self.actions
                    .get(key)
                    .is_some_and(|actions| actions.iter().any(|id| id == keybinding))
            })
            .filter(|(key, _)| seen.insert(key.clone()))
            .map(|(_, label)| label)
            .collect()
    }

    /// Whether `data` is the macOS option-composed form of one of the id's
    /// bound keys (TS `matches(keyData, id, { optionComposed: true })`:
    /// Option+S types U+00DF (sharp s) on layouts without option-as-meta, and the
    /// composed character must toggle like Alt+S; only an alt-only
    /// binding composes).
    #[must_use]
    pub fn matches_option_composed(&self, data: &str, keybinding: &str) -> bool {
        self.get_keys(keybinding).iter().any(|key| {
            let composed = parse_key_id(key).and_then(|parsed| {
                (parsed.alt
                    && !parsed.ctrl
                    && !parsed.shift
                    && !parsed.super_key
                    && parsed.key == "s")
                    .then_some("\u{df}")
            });
            composed.is_some_and(|composed| composed == data)
        })
    }

    #[must_use]
    pub fn first_key(&self, keybinding: &str) -> Option<String> {
        self.get_keys(keybinding).into_iter().next()
    }

    /// TS `keyText(keybinding)`: every key of the binding formatted and
    /// joined with "/" ("Esc/Ctrl+C"); an unbound id renders empty.
    #[must_use]
    pub fn key_text(&self, keybinding: &str) -> String {
        format_key_text(&self.get_keys(keybinding).join("/"))
    }

    /// TS `getEffectiveConfig` / `getResolvedBindings`: the effective key
    /// list per definition id.
    #[must_use]
    pub fn get_effective_config(&self) -> BTreeMap<String, Vec<String>> {
        definitions()
            .map(|(id, _)| (id.to_string(), self.get_keys(id)))
            .collect()
    }
}

impl Default for KeybindingsManager {
    fn default() -> Self {
        Self::new()
    }
}

/// The platform flavor used to label modifier keys in hints (TS
/// `formatKeyPart`'s `platform` parameter, `process.platform` at the call
/// sites): macOS terminals send the literal Control key, so `alt` is
/// labeled `Option` and control is never relabeled as Cmd.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LabelPlatform {
    /// `process.platform === "darwin"`: `alt` renders as `Option`.
    Macos,
    /// Every other platform: `alt` renders as `Alt`.
    Other,
}

impl LabelPlatform {
    /// The platform the binary is running on.
    fn host() -> Self {
        if std::env::consts::OS == "macos" {
            Self::Macos
        } else {
            Self::Other
        }
    }

    fn is_macos(self) -> bool {
        matches!(self, Self::Macos)
    }
}

/// Format a key id for display in hints ("ctrl+o" -> "Ctrl+O", arrows to
/// glyphs; `alt` renders as `Option` on macOS, `Alt` elsewhere).
#[must_use]
pub fn format_key_text(key: &str) -> String {
    format_key_text_on(key, LabelPlatform::host())
}

/// The platform-explicit form of [`format_key_text`] (TS `formatKeyText(key,
/// platform)`), so the label choice is testable on every host.
fn format_key_text_on(key: &str, platform: LabelPlatform) -> String {
    key.split('/')
        .map(|binding| {
            binding
                .split('+')
                .map(|part| match part {
                    "escape" => "Esc".to_string(),
                    "up" => crate::glyphs::KEY_UP.to_string(),
                    "down" => crate::glyphs::KEY_DOWN.to_string(),
                    "left" => crate::glyphs::KEY_LEFT.to_string(),
                    "right" => crate::glyphs::KEY_RIGHT.to_string(),
                    "pageUp" => "PageUp".to_string(),
                    "pageDown" => "PageDown".to_string(),
                    // macOS labels the modifier after the keyboard row
                    // (Option), like TS formatKeyPart's darwin branch.
                    "alt" if platform.is_macos() => "Option".to_string(),
                    // The macOS Cmd key -- a prompt-editor-keybinds label
                    // addition (TS never renders a super binding).
                    "super" if platform.is_macos() => "Cmd".to_string(),
                    other => {
                        let mut c = other.chars();
                        match c.next() {
                            Some(first) => first.to_uppercase().collect::<String>() + c.as_str(),
                            None => String::new(),
                        }
                    }
                })
                .collect::<Vec<_>>()
                .join("+")
        })
        .collect::<Vec<_>>()
        .join("/")
}

#[cfg(test)]
mod tests;
