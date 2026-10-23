//! The bridge between the config code and its Bend model
//! (`bend/config.bend`, whose laws `laws/config.bend` states and
//! `PROOF.bend` proves): the Rust test builds each scenario's documents in
//! a temp dir, runs the real code over them, and prints what it did; the
//! model prints the same from the scenario. `bridge/bridge_config.bend`
//! documents the scenario format. Six kinds of scenario:
//!
//! - rmw: a read/modify/write of each writer (`eukhe mcp add`/`remove`
//!   through [`SettingsManager::set_global_mcp_server`] and
//!   [`SettingsManager::remove_global_mcp_server`],
//!   `McpConnectionStore::upsert`/`remove`, [`AuthStorage::set`] and
//!   [`AuthStorage::remove`]) over a missing, valid, invalid, unreadable or
//!   other-version file;
//! - save: a settings setter after another writer changed the file;
//! - leaf: the load of a settings document with good, wrong-typed and
//!   undeclared leaves;
//! - limit: the admission limits of a `providerMaxInFlight` value;
//! - trust: a project's preferences, limits, prompt files and MCP
//!   servers under each trust;
//! - merge: the global and project `mcpServers` entries.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;
use std::os::unix::fs::PermissionsExt as _;
use std::path::Path;
use std::sync::Arc;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use serde_json::{json, Map, Value};

use super::cvar::{registry, table, Decl};
use super::merge::deep_merge;
use super::storage::{InMemorySettingsStorage, SettingsScope, SettingsStorage};
use super::types::Settings;
use super::SettingsManager;
use crate::auth::{AuthCredential, AuthStorage};
use crate::mcp::connection_store::{new_pending_record, McpConnectionStore};
use crate::resources::{load_system_prompts, SystemPromptRequest};

/// The value of an entry as the model prints it: `<key> <value>` or
/// `<key> -`.
fn value_line(out: &mut String, key: u64, value: Option<u64>) {
    match value {
        Some(value) => {
            let _ = writeln!(out, "{key} {value}");
        }
        None => {
            let _ = writeln!(out, "{key} -");
        }
    }
}

/// The number after `prefix` in `text`.
fn number(text: &str, prefix: &str) -> Option<u64> {
    text.strip_prefix(prefix)?.parse().ok()
}

/// Whether the current user can read a file with mode 000 (root can):
/// then an unreadable file cannot be made, and the scenario uses an
/// invalid one.
fn can_read_000(dir: &Path) -> bool {
    let probe = dir.join("probe");
    std::fs::write(&probe, "x").unwrap();
    std::fs::set_permissions(&probe, std::fs::Permissions::from_mode(0o000)).unwrap();
    let readable = std::fs::read(&probe).is_ok();
    std::fs::set_permissions(&probe, std::fs::Permissions::from_mode(0o600)).unwrap();
    readable
}

// rmw
// ---

/// The writers of the rmw scenarios.
#[derive(Debug, Clone, Copy)]
enum Writer {
    /// `mcpServers.s<k>` of the global settings.json.
    Settings,
    /// Record `c<k>` of mcp-connections.json.
    Connections,
    /// The credential of provider `p<k>` in auth.json.
    Auth,
}

/// How the file the writer reads is broken.
#[derive(Debug, Clone, Copy)]
enum Broken {
    Invalid,
    Unreadable,
    OtherVersion,
}

/// The document of `entries` as `writer` stores it.
fn document(writer: Writer, entries: &[(u64, u64)]) -> String {
    match writer {
        Writer::Settings => {
            let servers: Map<String, Value> = entries
                .iter()
                .map(|(k, v)| {
                    (
                        format!("s{k}"),
                        json!({ "type": "stdio", "command": format!("c{v}") }),
                    )
                })
                .collect();
            json!({ "theme": "kept", "mcpServers": servers }).to_string()
        }
        Writer::Connections => {
            let records: Map<String, Value> = entries
                .iter()
                .map(|(k, v)| {
                    let mut record = new_pending_record(
                        &format!("c{k}"),
                        "svc",
                        &format!("l{v}"),
                        "https://e/mcp",
                    );
                    record.created_at = 1;
                    record.updated_at = 1;
                    (format!("c{k}"), serde_json::to_value(record).unwrap())
                })
                .collect();
            json!({ "version": 1, "connections": records }).to_string()
        }
        Writer::Auth => {
            let credentials: Map<String, Value> = entries
                .iter()
                .map(|(k, v)| {
                    (
                        format!("p{k}"),
                        json!({ "type": "api_key", "key": format!("k{v}") }),
                    )
                })
                .collect();
            Value::Object(credentials).to_string()
        }
    }
}

/// The value of key `key` in the document `text` that `writer` stored.
fn stored(writer: Writer, text: &str, key: u64) -> Option<u64> {
    let document: Value = serde_json::from_str(text).ok()?;
    match writer {
        Writer::Settings => number(
            document["mcpServers"][format!("s{key}")]["command"].as_str()?,
            "c",
        ),
        Writer::Connections => number(
            document["connections"][format!("c{key}")]["label"].as_str()?,
            "l",
        ),
        Writer::Auth => number(document[format!("p{key}")]["key"].as_str()?, "k"),
    }
}

/// Run one edit (`set`: `Some(v)`) of key `key` by `writer` over the
/// agent dir; `Err` when it refused.
fn write(writer: Writer, agent_dir: &Path, key: u64, set: Option<u64>) -> Result<(), String> {
    match writer {
        Writer::Settings => {
            let mut manager = SettingsManager::create(agent_dir.join("cwd"), agent_dir);
            let name = format!("s{key}");
            match set {
                Some(v) => manager
                    .set_global_mcp_server(
                        &name,
                        &json!({ "type": "stdio", "command": format!("c{v}") }),
                    )
                    .map_err(|error| error.to_string()),
                None => manager
                    .remove_global_mcp_server(&name)
                    .map(drop)
                    .map_err(|error| error.to_string()),
            }
        }
        Writer::Connections => {
            let mut store = McpConnectionStore::open(agent_dir.join("mcp-connections.json"));
            let id = format!("c{key}");
            match set {
                Some(v) => {
                    let mut record =
                        new_pending_record(&id, "svc", &format!("l{v}"), "https://e/mcp");
                    record.created_at = 1;
                    record.updated_at = 1;
                    store.upsert(&record).map_err(|error| error.to_string())
                }
                None => store.remove(&id).map_err(|error| error.to_string()),
            }
        }
        Writer::Auth => {
            let mut auth = AuthStorage::create(agent_dir);
            let provider = format!("p{key}");
            match set {
                Some(v) => auth
                    .set(
                        &provider,
                        AuthCredential::ApiKey {
                            key: format!("k{v}"),
                            prime_team: None,
                        },
                    )
                    .map_err(|error| error.to_string()),
                None => auth.remove(&provider).map_err(|error| error.to_string()),
            }
        }
    }
}

fn rmw_scenario(rng: &mut Rng, unreadable_ok: bool) -> (String, String) {
    let writer = rng
        .pick(&[Writer::Settings, Writer::Connections, Writer::Auth])
        .unwrap();
    let read = rng.below(3);
    let edit = rng.below(2);
    let entries: Vec<(u64, u64)> = (0..rng.range(0, 4)).map(|k| (k, rng.range(1, 9))).collect();
    let key = rng.below(6);
    let value = rng.range(1, 9);
    let temp = tempfile::tempdir().unwrap();
    let agent_dir = temp.path();
    let file = agent_dir.join(match writer {
        Writer::Settings => "settings.json",
        Writer::Connections => "mcp-connections.json",
        Writer::Auth => "auth.json",
    });
    let broken = match writer {
        Writer::Connections => {
            rng.pick(&[Broken::Invalid, Broken::Unreadable, Broken::OtherVersion])
        }
        Writer::Settings | Writer::Auth => rng.pick(&[Broken::Invalid, Broken::Unreadable]),
    }
    .unwrap();
    let broken = match broken {
        Broken::Unreadable if !unreadable_ok => Broken::Invalid,
        Broken::Invalid | Broken::Unreadable | Broken::OtherVersion => broken,
    };
    let before = match read {
        0 => None,
        1 => Some(document(writer, &entries)),
        _ => Some(match broken {
            Broken::Invalid => "{ \"oops\": ".to_string(),
            Broken::Unreadable => document(writer, &entries),
            Broken::OtherVersion => {
                document(writer, &entries).replace("\"version\":1", "\"version\":2")
            }
        }),
    };
    if let Some(text) = &before {
        std::fs::write(&file, text).unwrap();
    }
    if let (2, Broken::Unreadable) = (read, broken) {
        std::fs::set_permissions(&file, std::fs::Permissions::from_mode(0o000)).unwrap();
    }
    let set = (edit == 0).then_some(value);
    let outcome = write(writer, agent_dir, key, set);
    let mut queries: Vec<u64> = entries.iter().map(|(k, _)| *k).collect();
    if !queries.contains(&key) {
        queries.push(key);
    }
    let mut events = format!("rmw {read} {edit} {key} {value}\n");
    for (k, v) in &entries {
        let _ = writeln!(events, "e {k} {v}");
    }
    for q in &queries {
        let _ = writeln!(events, "q {q}");
    }
    let mut transcript = String::new();
    if file.exists() {
        std::fs::set_permissions(&file, std::fs::Permissions::from_mode(0o600)).unwrap();
    }
    let after = std::fs::read_to_string(&file).ok();
    match outcome {
        // Refused: the model prints no value; the file must be as it was.
        Err(_) => {
            assert_eq!(
                before, after,
                "a refused write changed the file ({writer:?})"
            );
            for q in &queries {
                value_line(&mut transcript, *q, None);
            }
        }
        Ok(()) => {
            for q in &queries {
                value_line(
                    &mut transcript,
                    *q,
                    after.as_deref().and_then(|text| stored(writer, text, *q)),
                );
            }
        }
    }
    (events, transcript)
}

// save
// ----

/// The Text cvars the save scenarios write (key k is `TEXT_KEYS[k]`).
const TEXT_KEYS: [&Decl; 5] = [
    &table::THEME,
    &table::DEFAULT_MODEL,
    &table::DEFAULT_PROVIDER,
    &table::AUXILIARY_MODEL,
    &table::IMAGE_MODEL,
];

/// Value v as written: an even one is the text `v<v>`, an odd one a number
/// (a value the Text cvar does not admit, which the load drops).
fn text_value(v: u64) -> Value {
    if v.is_multiple_of(2) {
        json!(format!("v{v}"))
    } else {
        json!(v)
    }
}

fn text_document(entries: &[(u64, u64)]) -> String {
    let document: Map<String, Value> = entries
        .iter()
        .map(|(k, v)| (TEXT_KEYS[*k as usize].id.to_string(), text_value(*v)))
        .collect();
    Value::Object(document).to_string()
}

fn save_scenario(rng: &mut Rng) -> (String, String) {
    let mut documents = [Vec::new(), Vec::new()];
    for document in &mut documents {
        for k in 0..5u64 {
            if rng.chance(60) {
                document.push((k, rng.range(1, 9)));
            }
        }
    }
    let [loaded, disk] = documents;
    let key = rng.below(5);
    let value = rng.range(1, 4) * 2;
    let temp = tempfile::tempdir().unwrap();
    let agent_dir = temp.path();
    let file = agent_dir.join("settings.json");
    std::fs::write(&file, text_document(&loaded)).unwrap();
    let mut manager = SettingsManager::create(agent_dir.join("cwd"), agent_dir);
    std::fs::write(&file, text_document(&disk)).unwrap();
    manager
        .set_global_cvar(TEXT_KEYS[key as usize], &text_value(value))
        .unwrap()
        .applied()
        .unwrap();
    let written: Value = serde_json::from_str(&std::fs::read_to_string(&file).unwrap()).unwrap();
    let mut events = format!("save {key} {value}\n");
    for (k, v) in &loaded {
        let _ = writeln!(events, "l {k} {v}");
    }
    for (k, v) in &disk {
        let _ = writeln!(events, "e {k} {v}");
    }
    let mut transcript = String::new();
    for q in 0..5u64 {
        let _ = writeln!(events, "q {q}");
        let at = &written[TEXT_KEYS[q as usize].id];
        let value = at
            .as_str()
            .and_then(|text| number(text, "v"))
            .or_else(|| at.as_u64());
        value_line(&mut transcript, q, value);
    }
    (events, transcript)
}

// leaf
// ----

/// One leaf kind of the leaf scenarios: its key path, a value it admits,
/// and a value of the wrong type.
struct LeafKind {
    path: &'static str,
    good: fn() -> Value,
    bad: fn() -> Value,
}

const LEAVES: [LeafKind; 12] = [
    LeafKind {
        path: "theme",
        good: || json!("dark"),
        bad: || json!(5),
    },
    LeafKind {
        path: "quietStartup",
        good: || json!(true),
        bad: || json!("yes"),
    },
    LeafKind {
        path: "maxToolRounds",
        good: || json!(40),
        bad: || json!("500"),
    },
    LeafKind {
        path: "compaction.reserveTokens",
        good: || json!(2048),
        bad: || json!("16k"),
    },
    LeafKind {
        path: "compaction.enabled",
        good: || json!(false),
        bad: || json!(1),
    },
    LeafKind {
        path: "transport",
        good: || json!("sse"),
        bad: || json!("pigeon"),
    },
    LeafKind {
        path: "steeringMode",
        good: || json!("all"),
        bad: || json!("some"),
    },
    LeafKind {
        path: "shell.autoEffects",
        good: || json!(["read", "write"]),
        bad: || json!(["read", "wirte"]),
    },
    LeafKind {
        path: "terminal.fullscreen",
        good: || json!(true),
        bad: || json!("on"),
    },
    LeafKind {
        path: "editorPaddingX",
        good: || json!(2),
        bad: || json!(-1),
    },
    LeafKind {
        path: "idleEvictionMinutes",
        good: || json!("off"),
        bad: || json!("soon"),
    },
    LeafKind {
        path: "defaultModel",
        good: || json!("m"),
        bad: || json!(["m"]),
    },
];

/// Put `value` at the dotted `path` of `document`.
fn put(document: &mut Map<String, Value>, path: &str, value: Value) {
    let steps: Vec<&str> = path.split('.').collect();
    super::persist::edit_path(document, &steps, super::persist::KeyEdit::Set(value)).unwrap();
}

fn leaf_scenario(rng: &mut Rng) -> (String, String) {
    let mut document = Map::new();
    let mut events = "leaf\n".to_string();
    // (model path, key path, outcome)
    let mut leaves: Vec<(usize, String, u64)> = Vec::new();
    for (at, kind) in LEAVES.iter().enumerate() {
        if !rng.chance(60) {
            continue;
        }
        let outcome = rng.below(3);
        let path = match outcome {
            0 => {
                put(&mut document, kind.path, (kind.good)());
                kind.path.to_string()
            }
            1 => {
                put(&mut document, kind.path, (kind.bad)());
                kind.path.to_string()
            }
            // An undeclared key: top-level, or beside the leaf's parent.
            _ => {
                let path = match kind.path.rsplit_once('.') {
                    Some((parent, _)) => format!("{parent}.bogus{at}"),
                    None => format!("bogus{at}"),
                };
                put(&mut document, &path, json!(at));
                path
            }
        };
        leaves.push((at, path, outcome));
    }
    let storage: Arc<dyn SettingsStorage> = Arc::new(InMemorySettingsStorage::default());
    let text = Value::Object(document.clone()).to_string();
    storage
        .with_lock(SettingsScope::Global, &mut |_| Some(text.clone()))
        .unwrap();
    let manager = SettingsManager::from_storage(storage);
    let mut transcript = String::new();
    for (at, path, outcome) in &leaves {
        let _ = writeln!(events, "f {at} {outcome}");
        let steps: Vec<&str> = path.split('.').collect();
        let written = steps
            .iter()
            .try_fold(Value::Object(document.clone()), |node, key| {
                node.get(*key).cloned()
            });
        let applied = registry().find(path).is_some()
            && manager
                .cvars()
                .config()
                .0
                .iter()
                .any(|set| set.id == *path && Some(&set.value) == written.as_ref());
        let needle = format!("`{path}`");
        let reported = manager
            .errors()
            .iter()
            .any(|error| error.message.contains(&needle));
        transcript.push_str(match (applied, reported) {
            (true, false) => "L\n",
            (true, true) => "LD\n",
            (false, false) => "S\n",
            (false, true) => "R\n",
        });
    }
    (events, transcript)
}

// limit
// -----

fn limit_scenario(rng: &mut Rng) -> (String, String) {
    let shape = rng.below(3);
    let mut events = format!("limit {shape}\n");
    let mut document = Map::new();
    match shape {
        0 => {}
        1 => {
            let mut entries = Map::new();
            for p in 0..4u64 {
                if !rng.chance(60) {
                    continue;
                }
                if rng.chance(30) {
                    entries.insert(format!("p{p}"), json!("4"));
                    let _ = writeln!(events, "s {p} x");
                } else {
                    let n = rng.below(4);
                    entries.insert(format!("p{p}"), json!(n));
                    let _ = writeln!(events, "s {p} {n}");
                }
            }
            document.insert("providerMaxInFlight".to_string(), Value::Object(entries));
        }
        _ => {
            document.insert("providerMaxInFlight".to_string(), json!("lots"));
        }
    }
    let storage: Arc<dyn SettingsStorage> = Arc::new(InMemorySettingsStorage::default());
    let text = Value::Object(document).to_string();
    storage
        .with_lock(SettingsScope::Global, &mut |_| Some(text.clone()))
        .unwrap();
    let limits = SettingsManager::from_storage(storage).get_admission_limits();
    let mut transcript = String::new();
    for p in 0..5u64 {
        let _ = writeln!(events, "q {p}");
        match limits.max_in_flight(&format!("p{p}")) {
            None => {
                let _ = writeln!(transcript, "{p} U");
            }
            Some(n) => {
                let _ = writeln!(transcript, "{p} C {n}");
            }
        }
    }
    (events, transcript)
}

// trust
// -----

/// A key of the trust scenarios and what it is in the model.
#[derive(Clone, Copy)]
enum TrustKey {
    /// A Text preference (the value `v<n>`).
    Pref(&'static Decl),
    /// A Nat limit.
    Limit(&'static Decl),
    /// `SYSTEM.md` (0) or `APPEND_SYSTEM.md` (1), with the text `p<n>`.
    Prompt(u64),
    /// `mcpServers.c<i>` (the command `c<n>`).
    Credential(u64),
}

impl TrustKey {
    fn class(self) -> u64 {
        match self {
            TrustKey::Pref(_) => 0,
            TrustKey::Limit(_) => 1,
            TrustKey::Prompt(_) => 2,
            TrustKey::Credential(_) => 3,
        }
    }
}

const TRUST_KEYS: [TrustKey; 14] = [
    TrustKey::Pref(&table::THEME),
    TrustKey::Pref(&table::DEFAULT_MODEL),
    TrustKey::Pref(&table::AUXILIARY_MODEL),
    TrustKey::Limit(&table::MAX_TOOL_ROUNDS),
    TrustKey::Limit(&table::SUBAGENT_MAX_CONCURRENCY),
    TrustKey::Limit(&table::SUBAGENT_STALL_MS),
    TrustKey::Limit(&table::TOOL_BLOCKING_BUDGET_MS),
    TrustKey::Limit(&table::DIRECTORS_MAX_STEPS),
    TrustKey::Limit(&table::RETRY_MAX_RETRIES),
    TrustKey::Limit(&table::RETRY_FAILOVER_MAX_RETRIES),
    TrustKey::Prompt(0),
    TrustKey::Prompt(1),
    TrustKey::Credential(0),
    TrustKey::Credential(1),
];

const PROMPT_FILES: [&str; 2] = ["SYSTEM.md", "APPEND_SYSTEM.md"];

/// Write key `key` with value `n` into a settings `document` and a
/// prompt-file `dir`.
fn put_trust(document: &mut Map<String, Value>, dir: &Path, key: TrustKey, n: u64) {
    match key {
        TrustKey::Pref(decl) => put(document, decl.id, json!(format!("v{n}"))),
        TrustKey::Limit(decl) => put(document, decl.id, json!(n)),
        TrustKey::Prompt(slot) => {
            std::fs::write(dir.join(PROMPT_FILES[slot as usize]), format!("p{n}")).unwrap();
        }
        TrustKey::Credential(i) => put(
            document,
            &format!("mcpServers.c{i}"),
            json!({ "type": "stdio", "command": format!("c{n}") }),
        ),
    }
}

fn trust_scenario(rng: &mut Rng) -> (String, String) {
    let trusted = rng.chance(30);
    let temp = tempfile::tempdir().unwrap();
    let cwd = temp.path().join("work");
    let project_dir = cwd.join(".eukhe");
    let agent_dir = temp.path().join("agent");
    std::fs::create_dir_all(&project_dir).unwrap();
    std::fs::create_dir_all(&agent_dir).unwrap();
    let mut events = format!("trust {}\n", u64::from(!trusted));
    let mut global = Map::new();
    let mut project = Map::new();
    for (k, key) in TRUST_KEYS.iter().enumerate() {
        if rng.chance(50) {
            let n = rng.range(1, 9);
            put_trust(&mut global, &agent_dir, *key, n);
            let _ = writeln!(events, "g {k} {n}");
        }
        if rng.chance(50) {
            let n = rng.range(1, 9);
            put_trust(&mut project, &project_dir, *key, n);
            let _ = writeln!(events, "i {k} {} {n}", key.class());
        }
    }
    if trusted {
        global.insert(
            "trustedProjects".to_string(),
            json!([temp.path().display().to_string()]),
        );
    }
    std::fs::write(
        agent_dir.join("settings.json"),
        Value::Object(global).to_string(),
    )
    .unwrap();
    std::fs::write(
        project_dir.join("settings.json"),
        Value::Object(project).to_string(),
    )
    .unwrap();
    let manager = SettingsManager::create(&cwd, &agent_dir);
    let prompts = load_system_prompts(&SystemPromptRequest {
        cwd: &cwd,
        agent_dir: &agent_dir,
        trust: manager.project_trust().level,
        system: None,
        append: &[],
    })
    .unwrap();
    let mut transcript = String::new();
    for (k, key) in TRUST_KEYS.iter().enumerate() {
        let _ = writeln!(events, "q {k}");
        let value = match key {
            TrustKey::Pref(decl) => manager
                .cvars()
                .layered(decl)
                .and_then(|value| value.as_str().and_then(|text| number(text, "v"))),
            TrustKey::Limit(decl) => manager
                .cvars()
                .layered(decl)
                .and_then(|value| value.as_u64()),
            TrustKey::Prompt(0) => prompts
                .system
                .as_ref()
                .and_then(|prompt| number(&prompt.text, "p")),
            TrustKey::Prompt(_) => prompts
                .append
                .first()
                .and_then(|prompt| number(&prompt.text, "p")),
            TrustKey::Credential(i) => manager
                .settings()
                .mcp_servers
                .as_ref()
                .and_then(|servers| servers.get(&format!("c{i}")))
                .and_then(|entry| entry["command"].as_str())
                .and_then(|text| number(text, "c")),
        };
        value_line(&mut transcript, k as u64, value);
    }
    (events, transcript)
}

// merge
// -----

/// Random named entries for the merge scenarios, each a `<tag>` line of
/// `events`.
fn named_entries(tag: &str, events: &mut String, rng: &mut Rng) -> Map<String, Value> {
    let mut servers = Map::new();
    for n in 0..4u64 {
        if !rng.chance(50) {
            continue;
        }
        let mut fields = Map::new();
        let mut line = format!("{tag} {n}");
        for k in 0..4u64 {
            if rng.chance(50) {
                let v = rng.range(1, 9);
                fields.insert(format!("f{k}"), json!(v));
                let _ = write!(line, " {k} {v}");
            }
        }
        let _ = writeln!(events, "{line}");
        servers.insert(format!("n{n}"), Value::Object(fields));
    }
    servers
}

fn merge_scenario(rng: &mut Rng) -> (String, String) {
    let mut events = "merge\n".to_string();
    let global = named_entries("G", &mut events, rng);
    let project = named_entries("P", &mut events, rng);
    let settings = |servers: Map<String, Value>| Settings {
        mcp_servers: Some(servers),
        ..Settings::default()
    };
    let merged = deep_merge(&settings(global), &settings(project));
    let mut transcript = String::new();
    for n in 0..5u64 {
        let _ = writeln!(events, "q {n}");
        let entry = merged
            .mcp_servers
            .as_ref()
            .and_then(|servers| servers.get(&format!("n{n}")));
        let _ = write!(transcript, "{n}");
        match entry.and_then(Value::as_object) {
            None => transcript.push_str(" -"),
            Some(fields) => {
                for (k, v) in fields {
                    let _ = write!(transcript, " {}={v}", k.trim_start_matches('f'));
                }
            }
        }
        transcript.push('\n');
    }
    (events, transcript)
}

#[test]
fn the_rust_config_code_equals_the_bend_model() {
    let unreadable_ok = !can_read_000(tempfile::tempdir().unwrap().path());
    let scenarios = (1..=360u64).map(|seed| {
        let mut rng = Rng(seed);
        let (events, transcript) = match seed % 6 {
            0 => rmw_scenario(&mut rng, unreadable_ok),
            1 => save_scenario(&mut rng),
            2 => leaf_scenario(&mut rng),
            3 => limit_scenario(&mut rng),
            4 => trust_scenario(&mut rng),
            _ => merge_scenario(&mut rng),
        };
        Scenario {
            name: seed.to_string(),
            events,
            transcript,
        }
    });
    compare("bridge/bridge_config.bend", scenarios);
}
