//! Migration of the values earlier releases wrote: each legacy shape maps
//! to the value of the current schema with the same behaviour, on every
//! read. The load after it never reports a value an earlier release
//! wrote.
//!
//! The settings release fixtures (`tests/settings_releases.rs`) hold every
//! value each release accepted; a schema change without its migration here
//! fails them.

use serde_json::{Map, Value};

use super::cvar::registry;

/// `document` in the current schema.
pub(crate) fn migrate(document: &Map<String, Value>) -> Map<String, Value> {
    let mut document = document.clone();
    legacy_shapes(&mut document);
    flag_sections(&mut document);
    document
}

/// The shapes of the first releases (queueMode, websockets, skills
/// object, retry.maxDelayMs, onboardingCompleted). A `markdown` that is
/// not an object stays: the load names it.
fn legacy_shapes(document: &mut Map<String, Value>) {
    // queueMode -> steeringMode
    if let Some(queue_mode) = document.remove("queueMode") {
        document.entry("steeringMode").or_insert(queue_mode);
    }
    // onboardingCompleted (the legacy first-run flag) -> onboardingShown,
    // which the first-run check reads alone.
    if let Some(completed) = document.get("onboardingCompleted").cloned() {
        document.entry("onboardingShown").or_insert(completed);
    }
    // websockets bool -> transport
    if !document.contains_key("transport") {
        if let Some(websockets) = document.remove("websockets") {
            if websockets.is_boolean() {
                let transport = if websockets == Value::Bool(true) {
                    "web-socket"
                } else {
                    "sse"
                };
                document.insert("transport".into(), Value::String(transport.into()));
            }
        }
    }
    // skills object -> enableSkillCommands + customDirectories
    if let Some(skills) = document.remove("skills") {
        if let Value::Object(mut skills_obj) = skills {
            if let Some(flag) = skills_obj.remove("enableSkillCommands") {
                if document.get("enableSkillCommands").is_none() {
                    document.insert("enableSkillCommands".into(), flag);
                }
            }
            match skills_obj.remove("customDirectories") {
                Some(Value::Array(dirs)) if !dirs.is_empty() => {
                    document.insert("skills".into(), Value::Array(dirs));
                }
                _ => {}
            }
        } else {
            // Already a directory list: put it back untouched.
            document.insert("skills".into(), skills);
        }
    }
    // retry.maxDelayMs -> retry.provider.maxRetryDelayMs
    if let Some(Value::Object(retry)) = document.get_mut("retry") {
        let max_delay = retry.remove("maxDelayMs");
        if let Some(Value::Number(delay)) = max_delay {
            let provider = retry
                .entry("provider")
                .or_insert_with(|| Value::Object(Map::new()));
            if let Some(provider_obj) = provider.as_object_mut() {
                provider_obj
                    .entry("maxRetryDelayMs")
                    .or_insert(Value::Number(delay));
            }
        }
    }
}

/// A section with an `enabled` setting written as the flag alone
/// (`"autoRefine": true`) is that flag: `{"enabled": true}`, in place.
fn flag_sections(document: &mut Map<String, Value>) {
    for section in registry()
        .decls()
        .iter()
        .filter_map(|decl| decl.id.strip_suffix(".enabled"))
    {
        let path: Vec<&str> = section.split('.').collect();
        if let Some(slot) = lookup_mut(document, &path).filter(|slot| slot.is_boolean()) {
            let enabled = Value::Bool(slot.as_bool() == Some(true));
            *slot = Value::Object([("enabled".to_string(), enabled)].into_iter().collect());
        }
    }
}

/// The value at `path` of `document`.
fn lookup_mut<'a>(document: &'a mut Map<String, Value>, path: &[&str]) -> Option<&'a mut Value> {
    let (last, parents) = path.split_last()?;
    let mut at = document;
    for key in parents {
        at = at.get_mut(*key)?.as_object_mut()?;
    }
    at.get_mut(*last)
}

/// The text to save for the settings file `text` holds: its migration,
/// when the file is eukhe's own (`text` is exactly the text eukhe writes
/// for its document) and the migration changes it. `None` for a file a
/// person edited (any other text: the migration applies on each read),
/// and for a file with nothing to migrate.
pub(crate) fn rewrite(text: &str) -> Option<String> {
    let document = match serde_json::from_str::<Value>(text).ok()? {
        Value::Object(document) => document,
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) | Value::Array(_) => {
            return None
        }
    };
    let own = serde_json::to_string_pretty(&document).ok()? == text;
    let migrated = migrate(&document);
    (own && migrated != document)
        .then(|| serde_json::to_string_pretty(&migrated).ok())
        .flatten()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::settings::cvar::table;
    use crate::settings::{
        InMemorySettingsStorage, SettingsManager, SettingsScope, SettingsStorage,
    };
    use serde_json::json;

    fn object(value: Value) -> Map<String, Value> {
        match value {
            Value::Object(object) => object,
            Value::Null
            | Value::Bool(_)
            | Value::Number(_)
            | Value::String(_)
            | Value::Array(_) => {
                panic!("not an object")
            }
        }
    }

    #[test]
    fn migration_rewrites_legacy_shapes() {
        let migrated = migrate(&object(json!({
            "queueMode": "all",
            "websockets": true,
            "skills": { "enableSkillCommands": false, "customDirectories": ["/x"] },
            "retry": { "maxDelayMs": 5 }
        })));
        assert_eq!(
            migrated,
            object(json!({
                "steeringMode": "all",
                "transport": "web-socket",
                "enableSkillCommands": false,
                "skills": ["/x"],
                "retry": { "provider": { "maxRetryDelayMs": 5 } }
            }))
        );
    }

    /// Regression: `"autoRefine": true` (a hand-written or older file)
    /// was a settings error on every session; it is the `enabled` flag.
    #[test]
    fn a_section_written_as_its_flag_is_its_enabled_setting() {
        let migrated = migrate(&object(json!({
            "theme": "dark",
            "autoRefine": true,
            "compaction": false,
            "retry": { "enabled": true }
        })));
        assert_eq!(
            migrated,
            object(json!({
                "theme": "dark",
                "autoRefine": { "enabled": true },
                "compaction": { "enabled": false },
                "retry": { "enabled": true }
            }))
        );
    }

    /// Regression: the reported settings error, end to end through the
    /// load: a flag section applies its flag and names nothing.
    #[test]
    fn a_flag_section_loads_without_a_settings_error() {
        let storage = Arc::new(InMemorySettingsStorage::default());
        storage
            .with_lock(SettingsScope::Global, &mut |_| {
                Some(r#"{ "autoRefine": false }"#.to_string())
            })
            .expect("the in-memory storage never fails");
        let manager = SettingsManager::from_storage(storage);
        assert_eq!(
            (
                manager.errors().to_vec(),
                manager.cvars().bool(&table::AUTO_REFINE_ENABLED)
            ),
            (Vec::new(), false)
        );
    }

    fn pretty(value: &Value) -> String {
        serde_json::to_string_pretty(value).expect("JSON serializes")
    }

    #[test]
    fn only_eukhes_own_text_is_rewritten() {
        let own = pretty(&json!({ "theme": "dark", "autoRefine": true }));
        let edited = "{\n  \"theme\": \"dark\",\n\n  \"autoRefine\": true\n}\n";
        let current = pretty(&json!({ "theme": "dark", "autoRefine": { "enabled": true } }));
        assert_eq!(
            (rewrite(&own), rewrite(edited), rewrite(&current)),
            (Some(current.clone()), None, None)
        );
    }

    /// A load saves the migration of eukhe's own file, and never writes a
    /// file that is a link (a Home Manager or Nix store file): it applies
    /// the migration in memory, with no settings error.
    #[cfg(unix)]
    #[test]
    fn a_load_saves_the_migration_of_its_own_file_and_never_writes_a_link() {
        let dir = tempfile::tempdir().expect("tempdir");
        let own_dir = dir.path().join("own");
        let linked_dir = dir.path().join("linked");
        let store = dir.path().join("store.json");
        let legacy = pretty(&json!({ "autoRefine": false }));
        for created in [&own_dir, &linked_dir] {
            std::fs::create_dir_all(created).expect("agent dir");
        }
        std::fs::write(own_dir.join("settings.json"), &legacy).expect("own settings");
        std::fs::write(&store, &legacy).expect("linked settings");
        std::os::unix::fs::symlink(&store, linked_dir.join("settings.json")).expect("link");
        let own = SettingsManager::create(dir.path(), &own_dir);
        let linked = SettingsManager::create(dir.path(), &linked_dir);
        let read = |path: &std::path::Path| std::fs::read_to_string(path).expect("settings text");
        assert_eq!(
            (
                own.errors().to_vec(),
                linked.errors().to_vec(),
                linked.cvars().bool(&table::AUTO_REFINE_ENABLED),
                read(&own_dir.join("settings.json")),
                read(&store),
            ),
            (
                Vec::new(),
                Vec::new(),
                false,
                pretty(&json!({ "autoRefine": { "enabled": false } })),
                legacy,
            )
        );
    }
}
