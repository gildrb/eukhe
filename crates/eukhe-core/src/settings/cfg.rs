//! The cfg files of the settings (docs/control.md S4): command scripts in
//! the cvar language (`eukhe_types::cvar`) beside `settings.json`.
//!
//! - `config.cfg` (global `<agentDir>/config.cfg`, then the project's
//!   `<cwd>/.eukhe/config.cfg`): the config layer over `settings.json`.
//!   The project file follows the project's trust like its
//!   `settings.json` (an untrusted project's withheld keys do not apply)
//!   and never sets a Global cvar.
//! - `subagent.cfg`, `agents/<agent>.cfg`: profiles
//!   ([`SettingsManager::read_profile`](super::SettingsManager::read_profile)).

use std::fmt::Write as _;

use eukhe_types::cvar::{parse_script, render_list, Aliases, Binds, Command};
use serde_json::Value;

use super::cvar::{
    document_sets, registry, value_text, CvarError, CvarScope, Cvars, Decl, Set, Sets, Target,
};
use super::load::load_document;
use super::manager::SettingsError;
use super::storage::{SettingsScope, SettingsStorage};
use super::trust::{effective_project, TrustLevel};
use super::types::Settings;

#[cfg(test)]
mod tests;

/// The config layer's cfg file.
pub(super) const CONFIG_CFG: &str = "config.cfg";

/// The settings document of a scope, as diagnostics name it.
pub(super) const SETTINGS_JSON: &str = "settings.json";

/// Where the sets of a config layer come from: `[0, document)` from the
/// `settings.json` documents, `[document, global_cfg)` from the global
/// `config.cfg`, the rest from the project `config.cfg`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ConfigBounds {
    pub(super) document: usize,
    pub(super) global_cfg: usize,
}

/// The config layer of one load: the cvars over `settings.json` and the
/// config cfg files, their aliases, and what did not apply.
pub(super) struct ConfigLayer {
    pub(super) cvars: Cvars,
    pub(super) aliases: Aliases,
    pub(super) errors: Vec<SettingsError>,
    /// Keys of the project `config.cfg` the project's trust withheld.
    pub(super) withheld: Vec<String>,
    /// Where the sets of `cvars.config()` come from.
    pub(super) bounds: ConfigBounds,
}

/// A failed command of cfg file `name` as a settings error.
pub(super) fn cfg_error(scope: SettingsScope, name: &str, error: &CvarError) -> SettingsError {
    SettingsError {
        scope,
        message: format!("{name}: {error}"),
    }
}

/// Run the cfg script `text` into `cvars` at `target`; the failures, as
/// settings errors of cfg file `name`.
pub(super) fn run_script(
    cvars: &mut Cvars,
    target: Target,
    text: &str,
    aliases: &mut Aliases,
    scope: SettingsScope,
    name: &str,
) -> Vec<SettingsError> {
    let (commands, parse_errors) = parse_script(text);
    // A `bind` in a settings cfg is not a key bind of any client (binds.cfg
    // holds those): it is dropped.
    let mut binds = Binds::default();
    let failures = cvars.execute(target, &commands, aliases, &mut binds);
    parse_errors
        .into_iter()
        .map(CvarError::Parse)
        .chain(failures)
        .map(|error| cfg_error(scope, name, &error))
        .collect()
}

/// The list value of cvar `decl` in the global layer alone: the global
/// `settings.json`, then the global `config.cfg` (the `trustedProjects`
/// reader: trust must be known before the project layers). The cfg's
/// errors are recorded by [`config_layer`].
pub(super) fn global_list(
    storage: &dyn SettingsStorage,
    global: &Settings,
    decl: &Decl,
) -> Result<Vec<String>, SettingsError> {
    let registry = registry();
    let global_value = serde_json::to_value(global).unwrap_or(Value::Null);
    let mut cvars = Cvars::new(
        registry,
        document_sets(registry, &global_value, &global_value),
    );
    let text = storage
        .read_cfg(SettingsScope::Global, CONFIG_CFG)
        .map_err(|error| SettingsError {
            scope: SettingsScope::Global,
            message: format!("{CONFIG_CFG}: {error:#}"),
        })?;
    if let Some(text) = text {
        // Recorded by `config_layer`, which runs the same file.
        let _recorded_by_config_layer = run_script(
            &mut cvars,
            Target::Config,
            &text,
            &mut Aliases::default(),
            SettingsScope::Global,
            CONFIG_CFG,
        );
    }
    Ok(cvars.list(decl))
}

/// The config layer: `settings.json` (`merged` for Local cvars, `global`
/// for Global ones), then the global `config.cfg`, then the sets of the
/// project `config.cfg` that are Local and that the project's trust lets
/// apply (each checked as if the project's `settings.json` held it). The
/// project file's aliases apply only to a trusted project.
pub(super) fn config_layer(
    storage: &dyn SettingsStorage,
    global: &Settings,
    merged: &Settings,
    trust: TrustLevel,
) -> ConfigLayer {
    let registry = registry();
    let merged_value = serde_json::to_value(merged).unwrap_or(Value::Null);
    let global_value = serde_json::to_value(global).unwrap_or(Value::Null);
    let mut cvars = Cvars::new(
        registry,
        document_sets(registry, &merged_value, &global_value),
    );
    let document = cvars.config().0.len();
    let mut aliases = Aliases::default();
    let mut errors = Vec::new();
    let mut withheld = Vec::new();
    // A cfg file that exists but cannot be read is a load error; its
    // writers refuse it too (`SettingsStorage::with_cfg_lock`).
    let read = |scope: SettingsScope, errors: &mut Vec<SettingsError>| {
        storage.read_cfg(scope, CONFIG_CFG).unwrap_or_else(|error| {
            errors.push(SettingsError {
                scope,
                message: format!("{CONFIG_CFG}: {error:#}"),
            });
            None
        })
    };
    if let Some(text) = read(SettingsScope::Global, &mut errors) {
        errors.extend(run_script(
            &mut cvars,
            Target::Config,
            &text,
            &mut aliases,
            SettingsScope::Global,
            CONFIG_CFG,
        ));
    }
    let bounds = ConfigBounds {
        document,
        global_cfg: cvars.config().0.len(),
    };
    if let Some(text) = read(SettingsScope::Project, &mut errors) {
        let mut scratch = cvars.clone();
        let mut project_aliases = aliases.clone();
        errors.extend(run_script(
            &mut scratch,
            Target::Config,
            &text,
            &mut project_aliases,
            SettingsScope::Project,
            CONFIG_CFG,
        ));
        let mut config = cvars.config().clone();
        for set in &scratch.config().0[config.0.len()..] {
            match project_set(set, trust) {
                ProjectSet::Applies => config.0.push(set.clone()),
                ProjectSet::Global => errors.push(SettingsError {
                    scope: SettingsScope::Project,
                    message: format!(
                        "{CONFIG_CFG}: `{}` is a Global cvar: only the global {CONFIG_CFG} sets it",
                        set.id
                    ),
                }),
                ProjectSet::Withheld(key) => {
                    if !withheld.contains(&key) {
                        withheld.push(key);
                    }
                }
                ProjectSet::Unfit => errors.push(SettingsError {
                    scope: SettingsScope::Project,
                    message: format!(
                        "{CONFIG_CFG}: `{} {}` is not a value settings.json holds",
                        set.id,
                        value_text(&set.value)
                    ),
                }),
            }
        }
        cvars = Cvars::new(registry, config);
        match trust {
            TrustLevel::Trusted => aliases = project_aliases,
            TrustLevel::Untrusted => {
                if project_aliases != aliases {
                    withheld.push(format!("{CONFIG_CFG} aliases"));
                }
            }
        }
    }
    ConfigLayer {
        cvars,
        aliases,
        errors,
        withheld,
        bounds,
    }
}

/// What becomes of one set of the project `config.cfg`.
enum ProjectSet {
    Applies,
    /// A Global cvar: only the global config sets it.
    Global,
    /// The project's trust withholds this top-level key.
    Withheld(String),
    /// The value has the cvar's type but `settings.json` cannot hold it.
    Unfit,
}

/// The set as the project's `settings.json` would hold it: the document
/// `{a: {b: value}}` of set `a.b`, through the lenient load and the
/// project's trust, must give back the same set.
fn project_set(set: &Set, trust: TrustLevel) -> ProjectSet {
    let registry = registry();
    let Some(decl) = registry.find(&set.id) else {
        return ProjectSet::Unfit;
    };
    match decl.scope {
        CvarScope::Global => return ProjectSet::Global,
        CvarScope::Local => {}
    }
    let document = set.id.rsplit('.').fold(set.value.clone(), |value, key| {
        let mut object = serde_json::Map::new();
        object.insert(key.to_string(), value);
        Value::Object(object)
    });
    let loaded = match &document {
        Value::Object(object) => load_document(object).settings,
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) | Value::Array(_) => {
            return ProjectSet::Unfit
        }
    };
    let (kept, ignored) = effective_project(&loaded, trust);
    if let Some(key) = ignored.into_iter().next() {
        return ProjectSet::Withheld(key);
    }
    let kept = serde_json::to_value(kept).unwrap_or(Value::Null);
    if document_sets(registry, &kept, &Value::Null).0.contains(set) {
        ProjectSet::Applies
    } else {
        ProjectSet::Unfit
    }
}

/// `command` sets or toggles cvar `id`.
fn writes(command: &Command, id: &str) -> bool {
    match command {
        Command::Set { id: target, .. } | Command::Toggle { id: target } => target == id,
        Command::Alias { .. }
        | Command::Bind { .. }
        | Command::Action { .. }
        | Command::Run { .. } => false,
    }
}

/// `content` (a cfg script) with `sets` written in: the last set of each
/// id replaces, in place, the first line that sets or toggles it; every
/// other set or toggle of the id goes (a line of several commands keeps
/// the others); a set of an id no line holds is appended. Lines that do
/// not parse, comments, and every other command stay as they are.
pub(super) fn replace_sets(content: &str, sets: &Sets) -> String {
    let mut latest: Vec<&Set> = Vec::new();
    for set in &sets.0 {
        match latest.iter_mut().find(|known| known.id == set.id) {
            Some(slot) => *slot = set,
            None => latest.push(set),
        }
    }
    let mut written = vec![false; latest.len()];
    let mut out = String::new();
    let emit = |out: &mut String, set: &Set| {
        let command = Command::Set {
            id: set.id.clone(),
            value: value_text(&set.value),
        };
        // Writing to a String cannot fail.
        let _ = writeln!(out, "{command}");
    };
    for line in content.lines() {
        let (commands, parse_errors) = parse_script(line);
        let hits: Vec<usize> = (0..latest.len())
            .filter(|at| {
                commands
                    .iter()
                    .any(|command| writes(command, &latest[*at].id))
            })
            .collect();
        if !parse_errors.is_empty() || hits.is_empty() {
            out.push_str(line);
            out.push('\n');
            continue;
        }
        let kept: Vec<Command> = commands
            .into_iter()
            .filter(|command| !latest.iter().any(|set| writes(command, &set.id)))
            .collect();
        if !kept.is_empty() {
            let _ = writeln!(out, "{}", render_list(&kept));
        }
        for at in hits {
            if !written[at] {
                written[at] = true;
                emit(&mut out, latest[at]);
            }
        }
    }
    for (at, set) in latest.iter().enumerate() {
        if !written[at] {
            emit(&mut out, set);
        }
    }
    out
}
