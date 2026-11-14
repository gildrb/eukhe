//! The settings documents of one release: every setting the release
//! declares, with each value of its type that the release loads with no
//! settings error, and the value each setting takes once loaded.
//!
//! The candidates per type are fixed here; a candidate enters a document
//! only when the release itself loads it cleanly, so a document never
//! holds a value its release rejected.

use std::path::Path;

use eukhe_core::settings::cvar::{registry, CvarType, Decl};
use eukhe_core::settings::SettingsManager;
use serde_json::{json, Map, Value};

/// The candidate values of a setting of type `ty` (`id` picks the
/// structured samples of the JSON settings).
fn candidates(id: &str, ty: CvarType) -> Vec<Value> {
    match ty {
        CvarType::Bool => vec![json!(true), json!(false)],
        CvarType::Nat => vec![json!(0), json!(7)],
        CvarType::NatOrOff => vec![json!(7), json!(0), json!("off"), json!("none")],
        CvarType::Text => vec![json!("fixture"), json!("")],
        CvarType::Choice(options) => options.iter().map(|option| json!(option)).collect(),
        CvarType::List => vec![json!([]), json!(["fixture-a", "fixture-b"])],
        CvarType::ChoiceList(options) => vec![json!([]), json!(options)],
        CvarType::Json => json_candidates(id),
    }
}

/// Structured samples first, then the scalar shapes a JSON setting may
/// take (a number, a fraction, an off word, a flag, a text, a map).
fn json_candidates(id: &str) -> Vec<Value> {
    let structured = match id {
        "mcpServers" => vec![
            json!({}),
            json!({ "fixture-stdio": { "type": "stdio", "command": "fixture-mcp", "args": ["--x"] } }),
            json!({ "fixture-http": { "type": "http", "url": "https://example.invalid/mcp", "headers": { "X-Fixture": "1" } } }),
            json!({ "fixture-sse": { "type": "sse", "url": "https://example.invalid/sse" } }),
            json!({ "fixture-plain": { "command": "fixture-mcp" } }),
        ],
        "packages" => vec![
            json!([]),
            json!(["npm:fixture-package"]),
            json!([{ "source": "npm:fixture-package" }]),
        ],
        "kernelTransport" => vec![
            json!({ "type": "local" }),
            json!({ "type": "ssh", "host": "fixture-host" }),
            json!({ "type": "ssh", "host": "fixture-host", "identity": "~/.ssh/fixture", "user": "fixture", "port": 22 }),
        ],
        "providerMaxInFlight" => vec![json!({}), json!({ "fixture": 4 })],
        _ => Vec::new(),
    };
    structured
        .into_iter()
        .chain([
            json!(0),
            json!(7),
            json!(2.5),
            json!(-1),
            json!("off"),
            json!("none"),
            json!("unlimited"),
            json!(true),
            json!(false),
            json!("fixture"),
            json!({}),
            json!([]),
        ])
        .collect()
}

/// `document` with `value` at the dotted `id`.
fn set(document: &mut Map<String, Value>, id: &str, value: Value) {
    let mut path: Vec<&str> = id.split('.').collect();
    let Some(last) = path.pop() else { return };
    let mut at = document;
    for key in path {
        let slot = at
            .entry(key.to_string())
            .or_insert_with(|| Value::Object(Map::new()));
        if !slot.is_object() {
            *slot = Value::Object(Map::new());
        }
        let Value::Object(next) = slot else { return };
        at = next;
    }
    at.insert(last.to_string(), value);
}

/// The settings errors of `document` loaded as the global settings, and
/// the loaded manager.
pub fn load(dir: &Path, document: &Map<String, Value>) -> (Vec<String>, SettingsManager) {
    let agent = dir.join("agent");
    let cwd = dir.join("project");
    std::fs::create_dir_all(&agent).expect("agent dir");
    std::fs::create_dir_all(&cwd).expect("project dir");
    std::fs::write(
        agent.join("settings.json"),
        serde_json::to_string_pretty(&Value::Object(document.clone())).expect("serialize"),
    )
    .expect("write settings");
    let manager = SettingsManager::create(&cwd, &agent);
    let errors = manager
        .errors()
        .iter()
        .map(|error| error.message.clone())
        .collect();
    (errors, manager)
}

/// The values a release loads cleanly for `decl`, each alone.
fn accepted(dir: &Path, decl: &Decl) -> Vec<Value> {
    candidates(decl.id, decl.ty)
        .into_iter()
        .filter(|value| {
            let mut document = Map::new();
            set(&mut document, decl.id, value.clone());
            load(dir, &document).0.is_empty()
        })
        .collect()
}

/// One generated document and the value each setting it sets takes.
fn case(dir: &Path, document: Map<String, Value>, ids: &[&str]) -> Value {
    let (errors, manager) = load(dir, &document);
    assert!(
        errors.is_empty(),
        "a generated document has errors: {errors:?}"
    );
    let effective: Map<String, Value> = ids
        .iter()
        .filter_map(|id| registry().find(id))
        .map(|decl| (decl.id.to_string(), manager.cvars().value(decl)))
        .collect();
    json!({ "settings": Value::Object(document), "effective": Value::Object(effective) })
}

/// The documents of the running build's settings schema: document `k`
/// sets each setting to its `k`-th accepted value (cycling), and a value
/// that loads cleanly alone but not beside the others gets a document of
/// its own.
#[must_use]
pub fn documents() -> Vec<Value> {
    let dir = tempfile::tempdir().expect("tempdir");
    let values: Vec<(&Decl, Vec<Value>)> = registry()
        .decls()
        .iter()
        .map(|decl| (decl, accepted(dir.path(), decl)))
        .filter(|(_, values)| !values.is_empty())
        .collect();
    let rounds = values
        .iter()
        .map(|(_, values)| values.len())
        .max()
        .unwrap_or(0);
    let mut cases = Vec::new();
    let mut alone: Vec<(&str, Value)> = Vec::new();
    for round in 0..rounds {
        let mut document = Map::new();
        let mut ids = Vec::new();
        for (decl, accepted) in &values {
            let value = accepted[round % accepted.len()].clone();
            let mut next = document.clone();
            set(&mut next, decl.id, value.clone());
            if load(dir.path(), &next).0.is_empty() {
                document = next;
                ids.push(decl.id);
            } else if !alone
                .iter()
                .any(|(id, seen)| *id == decl.id && *seen == value)
            {
                alone.push((decl.id, value));
            }
        }
        cases.push(case(dir.path(), document, &ids));
    }
    for (id, value) in alone {
        let mut document = Map::new();
        set(&mut document, id, value);
        cases.push(case(dir.path(), document, &[id]));
    }
    cases
}
