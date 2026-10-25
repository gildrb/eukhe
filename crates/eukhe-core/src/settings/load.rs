//! The load of one settings document: each leaf applies or is named by a
//! diagnostic, as the compiled core decides (`laws/config.bend`
//! `leaf_applied_or_reported`, `leaf_not_both`).
//!
//! A leaf is a value that is not an object, or the whole value of a cvar.
//! The load keeps a leaf when the typed `Settings` holds it and its cvar
//! (if it has one) admits it. It drops and names:
//!
//! - a top-level key that `Settings` does not declare ([`CvarError::Undeclared`];
//!   the key stays in `extra`, so a write never removes it);
//! - a nested key that the typed setting does not hold (`Undeclared`);
//! - a value that the typed setting or its cvar does not admit
//!   ([`CvarError::BadValue`]).
//!
//! The known top-level keys come from the `Settings` type itself (the keys
//! of its serialized default), not from a hand list.

use eukhe_bend::rules::config::{leaves, Outcome};
use serde_json::{Map, Value};

use super::cvar::{registry, value_text, CvarError, CvarType, Registry};
use super::types::Settings;

/// One loaded settings document: what applies and what was dropped.
#[derive(Debug, Clone)]
pub(crate) struct Loaded {
    pub(crate) settings: Settings,
    pub(crate) rejected: Vec<CvarError>,
}

/// The text a diagnostic shows for a value the typed setting cannot hold
/// when no cvar names the type.
const SETTINGS_TYPE: &str = "the type of this setting";

/// Load `document` (a migrated settings object) leaf by leaf.
pub(crate) fn load_document(document: &Map<String, Value>) -> Loaded {
    let registry = registry();
    let known = known_fields();
    let mut rejected = Vec::new();
    let mut kept = Map::new();
    for (key, value) in document {
        if value.is_null() {
            continue;
        }
        if !known.contains(key) {
            rejected.push(CvarError::Undeclared { id: key.clone() });
            kept.insert(key.clone(), value.clone());
            continue;
        }
        if let Some(value) = typed_part(registry, key, value, &mut rejected) {
            kept.insert(key.clone(), value);
        }
    }
    let mut settings = parse(&kept);
    let mut round = serde_json::to_value(&settings).unwrap_or(Value::Null);
    let mut refused = Vec::new();
    for decl in registry.decls() {
        let path: Vec<&str> = decl.id.split('.').collect();
        if let Some(value) = lookup(&round, &path).filter(|value| !value.is_null()) {
            if !decl.ty.admits(value) {
                rejected.push(CvarError::BadValue {
                    id: decl.id.to_string(),
                    value: value_text(value),
                    expected: decl.ty.name(),
                });
                refused.push(path);
            }
        }
    }
    if !refused.is_empty() {
        for path in &refused {
            remove(&mut round, path);
        }
        settings = parse(round.as_object().unwrap_or(&Map::new()));
        round = serde_json::to_value(&settings).unwrap_or(Value::Null);
    }
    for (key, value) in &kept {
        if known.contains(key) {
            undeclared_leaves(registry, key, value, &round, &refused, &mut rejected);
        }
    }
    // The leaves: each dropped value with its diagnostic, then each
    // declared top-level key the load kept. The core says which apply
    // and which are named; a kept key it does not apply leaves.
    let good: Vec<&String> = kept
        .keys()
        .filter(|key| {
            known.contains(*key)
                && round
                    .get(key.as_str())
                    .is_some_and(|value| !value.is_null())
        })
        .collect();
    let outcomes: Vec<(u64, Outcome)> = rejected
        .iter()
        .map(|error| match error {
            CvarError::Undeclared { .. } => Outcome::Undeclared,
            CvarError::BadValue { .. }
            | CvarError::Parse(_)
            | CvarError::Expand(_)
            | CvarError::Global { .. }
            | CvarError::NotBool { .. }
            | CvarError::Action { .. } => Outcome::BadType,
        })
        .chain(good.iter().map(|_| Outcome::Good))
        .zip(0u64..)
        .map(|(outcome, place)| (place, outcome))
        .collect();
    let (applied, reported) = leaves(&outcomes);
    let dropped: Vec<&str> = good
        .iter()
        .zip(rejected.len() as u64..)
        .filter(|(_, place)| !applied.contains(place))
        .map(|(key, _)| key.as_str())
        .collect();
    if !dropped.is_empty() {
        for key in dropped {
            remove(&mut round, &[key]);
        }
        settings = parse(round.as_object().unwrap_or(&Map::new()));
    }
    let rejected = reported
        .into_iter()
        .filter_map(|place| {
            usize::try_from(place)
                .ok()
                .and_then(|place| rejected.get(place))
        })
        .cloned()
        .collect();
    Loaded { settings, rejected }
}

/// The top-level keys `Settings` declares: its default serializes every
/// field (`None` as `null`) except the flattened `extra`.
fn known_fields() -> Vec<String> {
    match serde_json::to_value(Settings::default()) {
        Ok(Value::Object(fields)) => fields.into_iter().map(|(key, _)| key).collect(),
        Ok(
            Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) | Value::Array(_),
        )
        | Err(_) => Vec::new(),
    }
}

/// `Settings` from an object whose every field parses on its own.
fn parse(object: &Map<String, Value>) -> Settings {
    match serde_json::from_value::<Settings>(Value::Object(object.clone())) {
        Ok(settings) => settings,
        // Each field parsed alone (`typed_part`), so the whole parses; a
        // failure here is a serde invariant break, not user input.
        Err(error) => panic!("settings fields that parse alone do not parse together: {error}"),
    }
}

/// The document `{path: value}`.
fn nested(path: &[&str], value: Value) -> Value {
    path.iter().rev().fold(value, |value, key| {
        let mut object = Map::new();
        object.insert((*key).to_string(), value);
        Value::Object(object)
    })
}

/// `Settings` holds `value` at `path` on its own: the document
/// `{path: value}` parses and serializes back with a value at `path`.
fn holds(path: &[&str], value: &Value) -> bool {
    serde_json::from_value::<Settings>(nested(path, value.clone()))
        .ok()
        .and_then(|settings| serde_json::to_value(settings).ok())
        .is_some_and(|round| lookup(&round, path).is_some_and(|found| !found.is_null()))
}

/// The part of top-level `value` at `key` that the typed setting holds:
/// the whole value when it parses, else (for an object that is not a
/// cvar's value) each child that parses alone, else nothing. Each dropped
/// value is named.
fn typed_part(
    registry: &Registry,
    key: &str,
    value: &Value,
    rejected: &mut Vec<CvarError>,
) -> Option<Value> {
    let mut path = vec![key];
    keep_typed(registry, &mut path, value, rejected)
}

fn keep_typed<'a>(
    registry: &Registry,
    path: &mut Vec<&'a str>,
    value: &'a Value,
    rejected: &mut Vec<CvarError>,
) -> Option<Value> {
    if holds(path, value) {
        return Some(value.clone());
    }
    // The whole value of a cvar is one leaf: a map setting (such as
    // `providerMaxInFlight`) with one bad entry is dropped whole, never
    // kept without that entry.
    let leaf = registry.find(&path.join(".")).is_some();
    match value {
        Value::Object(children) if !children.is_empty() && !leaf => {
            let mut kept = Map::new();
            for (child, child_value) in children {
                if child_value.is_null() {
                    continue;
                }
                path.push(child);
                if let Some(part) = keep_typed(registry, path, child_value, rejected) {
                    kept.insert(child.clone(), part);
                }
                path.pop();
            }
            (!kept.is_empty() && holds(path, &Value::Object(kept.clone())))
                .then_some(Value::Object(kept))
        }
        Value::Object(_)
        | Value::Null
        | Value::Bool(_)
        | Value::Number(_)
        | Value::String(_)
        | Value::Array(_) => {
            let id = path.join(".");
            // A Json cvar admits any value; the typed setting names the
            // type then.
            let expected = registry
                .find(&id)
                .filter(|decl| !matches!(decl.ty, CvarType::Json))
                .map_or_else(|| SETTINGS_TYPE.to_string(), |decl| decl.ty.name());
            rejected.push(CvarError::BadValue {
                id,
                value: value_text(value),
                expected,
            });
            None
        }
    }
}

/// Name every leaf of `value` (at top-level `key`) that the typed round
/// trip `round` does not hold: a nested key the setting does not declare.
/// A cvar's whole value is one leaf; a path the cvar check refused is
/// named already.
fn undeclared_leaves(
    registry: &Registry,
    key: &str,
    value: &Value,
    round: &Value,
    refused: &[Vec<&str>],
    rejected: &mut Vec<CvarError>,
) {
    let mut stack: Vec<(Vec<String>, &Value)> = vec![(vec![key.to_string()], value)];
    while let Some((path, value)) = stack.pop() {
        let id = path.join(".");
        let steps: Vec<&str> = path.iter().map(String::as_str).collect();
        if refused.contains(&steps) {
            continue;
        }
        if lookup(round, &steps).is_none_or(Value::is_null) {
            if !rejected.iter().any(|error| names(error, &id)) {
                rejected.push(CvarError::Undeclared { id });
            }
            continue;
        }
        if registry.find(&id).is_some() {
            continue;
        }
        if let Value::Object(children) = value {
            for (child, child_value) in children {
                if !child_value.is_null() {
                    let mut next = path.clone();
                    next.push(child.clone());
                    stack.push((next, child_value));
                }
            }
        }
    }
}

/// `error` names `id` or a key above it.
fn names(error: &CvarError, id: &str) -> bool {
    match error {
        CvarError::Undeclared { id: named } | CvarError::BadValue { id: named, .. } => {
            id == named || id.starts_with(&format!("{named}."))
        }
        CvarError::Parse(_)
        | CvarError::Expand(_)
        | CvarError::Global { .. }
        | CvarError::NotBool { .. }
        | CvarError::Action { .. } => false,
    }
}

/// The value at `path` in `value`.
fn lookup<'a>(value: &'a Value, path: &[&str]) -> Option<&'a Value> {
    path.iter().try_fold(value, |node, key| node.get(key))
}

/// Remove the value at `path` from `value`.
fn remove(value: &mut Value, path: &[&str]) {
    let Some((last, parents)) = path.split_last() else {
        return;
    };
    let parent = parents
        .iter()
        .try_fold(value, |node, key| node.get_mut(*key));
    if let Some(Value::Object(object)) = parent {
        object.remove(*last);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::settings::types::{CompactionSettings, QueueModeSetting, ShellSettings};
    use serde_json::json;

    fn load(value: &Value) -> Loaded {
        load_document(value.as_object().expect("an object"))
    }

    #[test]
    fn wrong_typed_fields_are_dropped_and_named() {
        let loaded = load(&json!({
            "defaultProvider": 42,
            "steeringMode": "all",
            "recentModels": "not-an-array",
            "unknownKey": { "kept": true }
        }));
        assert_eq!(loaded.settings.default_provider, None);
        assert_eq!(loaded.settings.steering_mode, Some(QueueModeSetting::All));
        assert_eq!(loaded.settings.recent_models, None);
        assert_eq!(
            loaded.settings.extra.get("unknownKey"),
            Some(&json!({ "kept": true }))
        );
        assert_eq!(
            loaded.rejected,
            vec![
                CvarError::BadValue {
                    id: "defaultProvider".into(),
                    value: "42".into(),
                    expected: "a text".into()
                },
                CvarError::BadValue {
                    id: "recentModels".into(),
                    value: "not-an-array".into(),
                    expected: "a list".into()
                },
                CvarError::Undeclared {
                    id: "unknownKey".into()
                },
            ]
        );
    }

    #[test]
    fn clean_document_loads_with_no_diagnostic() {
        let loaded = load(&json!({ "theme": "eukhe", "rlmMaxDepth": 4 }));
        assert_eq!(loaded.settings.theme.as_deref(), Some("eukhe"));
        assert_eq!(loaded.settings.rlm_max_depth, Some(4));
        assert_eq!(loaded.rejected, Vec::new());
    }

    /// Regression (audit H3): one bad leaf dropped its whole object
    /// (`compaction`) in silence. Now only the leaf goes, and it is named.
    #[test]
    fn a_bad_leaf_drops_only_itself_and_is_named() {
        let loaded = load(&json!({
            "compaction": { "enabled": false, "reserveTokens": "16k" }
        }));
        let compaction = serde_json::to_value(loaded.settings.compaction).unwrap();
        let expected = serde_json::to_value(Some(CompactionSettings {
            enabled: Some(false),
            ..CompactionSettings::default()
        }))
        .unwrap();
        assert_eq!(compaction, expected);
        assert_eq!(
            loaded.rejected,
            vec![CvarError::BadValue {
                id: "compaction.reserveTokens".into(),
                value: "16k".into(),
                expected: "a whole number".into()
            }]
        );
    }

    /// Regression (audit H3): a value the typed setting holds but its cvar
    /// does not admit was skipped in silence.
    #[test]
    fn a_value_its_cvar_refuses_is_named() {
        let loaded = load(&json!({ "shell": { "autoEffects": ["read", "wirte"] } }));
        assert_eq!(
            serde_json::to_value(loaded.settings.shell).unwrap(),
            serde_json::to_value(Some(ShellSettings::default())).unwrap()
        );
        assert_eq!(
            loaded.rejected,
            vec![CvarError::BadValue {
                id: "shell.autoEffects".into(),
                value: "[\"read\",\"wirte\"]".into(),
                expected: "a list of read, write, exec, net, outside, protected".into()
            }]
        );
    }

    /// A nested key no setting declares is named; the rest applies.
    #[test]
    fn an_undeclared_nested_key_is_named() {
        let loaded = load(&json!({ "compaction": { "enabled": true, "bogus": 1 } }));
        assert_eq!(
            loaded.rejected,
            vec![CvarError::Undeclared {
                id: "compaction.bogus".into()
            }]
        );
        assert_eq!(
            loaded.settings.compaction.and_then(|c| c.enabled),
            Some(true)
        );
    }

    /// Regression (audit H3): a map setting with one bad entry was kept
    /// without it, so the provider of that entry had no limit. A cvar's
    /// value is one leaf: the map is dropped whole and named, and the
    /// admission limits read it as written (failing closed).
    #[test]
    fn a_map_setting_with_a_bad_entry_is_one_bad_leaf() {
        let loaded = load(&json!({ "providerMaxInFlight": { "a": 1, "b": "4" } }));
        assert_eq!(loaded.settings.provider_max_in_flight, None);
        assert_eq!(
            loaded.rejected,
            vec![CvarError::BadValue {
                id: "providerMaxInFlight".into(),
                value: "{\"a\":1,\"b\":\"4\"}".into(),
                expected: SETTINGS_TYPE.into()
            }]
        );
    }

    /// The keys that the hand list missed (`toolBlockingBudgetMs` and the
    /// others) are known: a wrong-typed value is dropped, not kept in
    /// `extra`.
    #[test]
    fn known_fields_come_from_the_settings_type() {
        let loaded = load(&json!({ "toolBlockingBudgetMs": "soon", "mcpCatalogSources": 3 }));
        assert_eq!(loaded.settings.extra, Map::new());
        assert_eq!(
            loaded.rejected,
            vec![
                CvarError::BadValue {
                    id: "toolBlockingBudgetMs".into(),
                    value: "soon".into(),
                    expected: "a whole number".into()
                },
                CvarError::BadValue {
                    id: "mcpCatalogSources".into(),
                    value: "3".into(),
                    expected: "a list".into()
                },
            ]
        );
    }
}
