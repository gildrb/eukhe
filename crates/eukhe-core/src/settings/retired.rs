//! The retired settings a settings file holds (`migrate::RETIRED`) are
//! named to the user once per file: the record
//! `<agent dir>/retired-settings.json` keeps each one named, or pending
//! when the migration saved its file without it before any session named
//! it.

use serde::{Deserialize, Serialize};

use super::storage::{SettingsScope, SettingsStorage, CONFIG_DIR_NAME};

/// The record, in the global scope's directory.
const RECORD: &str = "retired-settings.json";

/// A retired setting a settings file held.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RetiredSetting {
    pub scope: SettingsScope,
    /// Its dotted id.
    pub id: &'static str,
}

/// Where a retired setting stands with the user.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum Naming {
    /// Its file was saved without it; no session named it yet.
    Pending,
    /// A session named it.
    Named,
}

/// One entry of the record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct Entry {
    /// The settings file (its path; the scope's name for a storage with
    /// no files).
    file: String,
    id: String,
    naming: Naming,
}

/// The settings file of `scope` as the record names it.
fn file(storage: &dyn SettingsStorage, scope: SettingsScope) -> String {
    let path = match scope {
        SettingsScope::Global => storage.global_location().map(std::path::Path::to_path_buf),
        SettingsScope::Project => storage
            .project_dir()
            .map(|dir| dir.join(CONFIG_DIR_NAME).join("settings.json")),
    };
    match (path, scope) {
        (Some(path), _) => path.to_string_lossy().into_owned(),
        (None, SettingsScope::Global) => "global".to_string(),
        (None, SettingsScope::Project) => "project".to_string(),
    }
}

/// The entries of the record `text`; a missing or broken record is empty
/// (each retired setting is named again, once).
fn entries(text: Option<&str>) -> Vec<Entry> {
    text.and_then(|text| serde_json::from_str(text).ok())
        .unwrap_or_default()
}

/// The entry of `setting`, if the record has one.
fn entry_of<'a>(
    entries: &'a [Entry],
    storage: &dyn SettingsStorage,
    setting: RetiredSetting,
) -> Option<&'a Entry> {
    let file = file(storage, setting.scope);
    entries
        .iter()
        .find(|entry| entry.file == file && entry.id == setting.id)
}

/// The retired settings to name: those `found` in the files that no
/// session named, and those pending in the record for a file of
/// `storage`.
pub(crate) fn unnamed(
    storage: &dyn SettingsStorage,
    found: &[RetiredSetting],
) -> Vec<RetiredSetting> {
    let text = storage
        .read_cfg(SettingsScope::Global, RECORD)
        .ok()
        .flatten();
    let entries = entries(text.as_deref());
    let pending = [SettingsScope::Global, SettingsScope::Project]
        .into_iter()
        .flat_map(|scope| {
            super::migrate::retired_ids()
                .iter()
                .map(move |id| RetiredSetting { scope, id })
        })
        .filter(|setting| {
            entry_of(&entries, storage, *setting)
                .is_some_and(|entry| entry.naming == Naming::Pending)
        });
    let unnamed_found = found.iter().copied().filter(|setting| {
        entry_of(&entries, storage, *setting).is_none_or(|entry| entry.naming == Naming::Pending)
    });
    let mut settings: Vec<RetiredSetting> = Vec::new();
    for setting in unnamed_found.chain(pending) {
        if !settings.contains(&setting) {
            settings.push(setting);
        }
    }
    settings
}

/// `entries` with each of `settings` at `naming`: a named entry stays
/// named.
fn noted(
    mut entries: Vec<Entry>,
    files: &[(RetiredSetting, String)],
    naming: Naming,
) -> Vec<Entry> {
    for (setting, file) in files {
        match entries
            .iter_mut()
            .find(|entry| entry.file == *file && entry.id == setting.id)
        {
            Some(entry) => {
                entry.naming = match (entry.naming, naming) {
                    (Naming::Named, Naming::Pending | Naming::Named)
                    | (Naming::Pending, Naming::Named) => Naming::Named,
                    (Naming::Pending, Naming::Pending) => Naming::Pending,
                };
            }
            None => entries.push(Entry {
                file: file.clone(),
                id: setting.id.to_string(),
                naming,
            }),
        }
    }
    entries
}

/// Record `settings` at `naming`.
fn note(storage: &dyn SettingsStorage, settings: &[RetiredSetting], naming: Naming) {
    if settings.is_empty() {
        return;
    }
    let files: Vec<(RetiredSetting, String)> = settings
        .iter()
        .map(|setting| (*setting, file(storage, setting.scope)))
        .collect();
    let written = storage.with_cfg_lock(SettingsScope::Global, RECORD, &mut |current| {
        serde_json::to_string_pretty(&noted(entries(current.as_deref()), &files, naming)).ok()
    });
    if let Err(error) = written {
        tracing::debug!(%error, "the retired settings record not saved");
    }
}

/// Record `settings` as saved out of their files before a session named
/// them.
pub(crate) fn note_pending(storage: &dyn SettingsStorage, settings: &[RetiredSetting]) {
    note(storage, settings, Naming::Pending);
}

/// Record `settings` as named.
pub(crate) fn note_named(storage: &dyn SettingsStorage, settings: &[RetiredSetting]) {
    note(storage, settings, Naming::Named);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::settings::InMemorySettingsStorage;

    const TELEMETRY: RetiredSetting = RetiredSetting {
        scope: SettingsScope::Global,
        id: "telemetry",
    };
    const CHANNEL: RetiredSetting = RetiredSetting {
        scope: SettingsScope::Project,
        id: "updateChannel",
    };

    /// A retired setting is named until a session names it; one saved out
    /// of its file stays to name until then.
    #[test]
    fn each_retired_setting_is_named_once() {
        let storage = InMemorySettingsStorage::default();
        let first = unnamed(&storage, &[TELEMETRY]);
        note_pending(&storage, &[CHANNEL]);
        let with_pending = unnamed(&storage, &[TELEMETRY]);
        note_named(&storage, &[TELEMETRY, CHANNEL]);
        note_pending(&storage, &[TELEMETRY]);
        let after = unnamed(&storage, &[TELEMETRY]);
        assert_eq!(
            (first, with_pending, after),
            (vec![TELEMETRY], vec![TELEMETRY, CHANNEL], Vec::new())
        );
    }
}
