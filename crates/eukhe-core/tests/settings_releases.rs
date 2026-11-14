//! Every settings value an earlier release accepted loads with no
//! settings error and the effect it had in that release.
//!
//! `fixtures/settings_releases/` holds one file per settings schema that
//! main has had since 0.10.50: the releases that shipped it (when known)
//! and its documents (`settings_releases/generate.rs`: every setting with
//! each value of its type the schema accepted, and the value each setting
//! took). A change of the settings schema fails
//! [`the_current_schema_is_stored`] until its documents are stored, and
//! fails [`every_value_an_earlier_schema_accepted_loads_with_its_effect`]
//! until `settings/migrate.rs` maps each value earlier schemas accepted.
//! Store the current schema with
//! `EUKHE_BLESS_SETTINGS=1 cargo test -p eukhe-core --test settings_releases`.

#[path = "settings_releases/generate.rs"]
mod generate;

use std::path::{Path, PathBuf};

use eukhe_core::settings::cvar::registry;
use serde_json::{json, Value};

/// The stored schemas.
fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/settings_releases")
}

/// Each stored schema: its file name and content.
fn stored() -> Vec<(String, Value)> {
    let mut files: Vec<(String, Value)> = std::fs::read_dir(fixtures_dir())
        .expect("the settings release fixtures")
        .map(|entry| entry.expect("a fixture entry").path())
        .map(|path| {
            let text = std::fs::read_to_string(&path).expect("a readable fixture");
            let name = path
                .file_name()
                .expect("a fixture name")
                .to_string_lossy()
                .into_owned();
            (
                name,
                serde_json::from_str(&text).expect("a fixture is JSON"),
            )
        })
        .collect();
    files.sort_by(|left, right| left.0.cmp(&right.0));
    files
}

/// What differs when the current build loads one stored document: its
/// settings errors, and each setting whose value is not the one the
/// schema's release gave it.
fn differences(name: &str, index: usize, case: &Value) -> Vec<String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let document = case["settings"].as_object().expect("a settings document");
    let (errors, manager) = generate::load(dir.path(), document);
    let errors = errors
        .into_iter()
        .map(|error| format!("{name} document {index}: settings error: {error}"));
    let effects = case["effective"]
        .as_object()
        .expect("the effective values")
        .iter()
        .filter_map(|(id, then)| {
            let now = registry().find(id).map(|decl| manager.cvars().value(decl));
            (now.as_ref() != Some(then))
                .then(|| format!("{name} document {index}: `{id}` was {then}, now {now:?}"))
        });
    errors.chain(effects).collect()
}

#[test]
fn every_value_an_earlier_schema_accepted_loads_with_its_effect() {
    let failures: Vec<String> = stored()
        .iter()
        .flat_map(|(name, schema)| {
            schema["documents"]
                .as_array()
                .expect("the documents of a schema")
                .iter()
                .enumerate()
                .flat_map(|(index, case)| differences(name, index, case))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(failures, Vec::<String>::new());
}

#[test]
fn the_current_schema_is_stored() {
    let documents = Value::Array(generate::documents());
    let known = stored()
        .iter()
        .any(|(_, schema)| schema["documents"] == documents);
    if known {
        return;
    }
    if std::env::var_os("EUKHE_BLESS_SETTINGS").is_some() {
        let text = serde_json::to_string_pretty(&json!({ "releases": [], "documents": documents }))
            .expect("serialize");
        let name = format!(
            "{}-{:016x}.json",
            env!("CARGO_PKG_VERSION"),
            fnv1a(text.as_bytes())
        );
        std::fs::write(fixtures_dir().join(name), text + "\n").expect("store the schema");
        return;
    }
    panic!(
        "the settings schema changed: map every value an earlier schema accepted in \
         crates/eukhe-core/src/settings/migrate.rs, then store this schema with \
         `EUKHE_BLESS_SETTINGS=1 cargo test -p eukhe-core --test settings_releases`"
    );
}

/// A stable name for a stored schema.
fn fnv1a(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x0100_0000_01b3)
    })
}
