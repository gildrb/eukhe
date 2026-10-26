use std::sync::Arc;

use eukhe_types::cvar::parse_list;
use serde_json::{json, Value};

use crate::settings::cvar::{CvarError, CvarWriteError, Set, Sets};
use crate::settings::storage::{
    FileSettingsStorage, InMemorySettingsStorage, SettingsScope, SettingsStorage,
};
use crate::settings::{SettingsManager, TransportSetting};

fn set(id: &str, value: Value) -> Set {
    Set {
        id: id.to_string(),
        value,
    }
}

/// An in-memory store with a global `settings.json` and cfg files.
fn storage(settings: &str, cfgs: &[(SettingsScope, &str, &str)]) -> Arc<dyn SettingsStorage> {
    let storage: Arc<dyn SettingsStorage> = Arc::new(InMemorySettingsStorage::default());
    let settings = settings.to_string();
    storage
        .with_lock(SettingsScope::Global, &mut |_| Some(settings.clone()))
        .expect("settings.json");
    for (scope, name, content) in cfgs {
        storage
            .with_cfg_lock(*scope, name, &mut |_| Some((*content).to_string()))
            .expect("cfg");
    }
    storage
}

fn errors(manager: &SettingsManager) -> Vec<(SettingsScope, String)> {
    manager
        .errors()
        .iter()
        .map(|error| (error.scope, error.message.clone()))
        .collect()
}

/// The global config.cfg is the config layer over settings.json: its sets
/// come after the document's, so they win.
#[test]
fn config_cfg_sets_over_settings_json() {
    let manager = SettingsManager::from_storage(storage(
        r#"{ "transport": "sse", "retry": { "enabled": true } }"#,
        &[(
            SettingsScope::Global,
            "config.cfg",
            "# local overrides\nset transport web-socket\nset retry.enabled off\n",
        )],
    ));
    assert_eq!(
        manager.cvars().config(),
        &Sets(vec![
            set("transport", json!("sse")),
            set("retry.enabled", json!(true)),
            set("transport", json!("web-socket")),
            set("retry.enabled", json!(false)),
        ])
    );
    assert_eq!(
        (manager.get_transport(), manager.get_retry_enabled()),
        (TransportSetting::WebSocket, false)
    );
}

/// A project config.cfg cannot set a Global cvar, nor a key an untrusted
/// project's trust withholds; its other sets apply.
#[test]
fn project_config_cfg_cannot_set_global_or_withheld_cvars() {
    let manager = SettingsManager::from_storage(storage(
        "{}",
        &[(
            SettingsScope::Project,
            "config.cfg",
            "set rlmMaxDepth 3\nset shellPath /bin/zsh\nset theme dark\n",
        )],
    ));
    assert_eq!(
        manager.cvars().config(),
        &Sets(vec![set("theme", json!("dark"))])
    );
    assert_eq!(
        (
            manager.project_trust().ignored_keys.clone(),
            errors(&manager)
        ),
        (
            vec!["shellPath".to_string()],
            vec![
                (
                    SettingsScope::Project,
                    "config.cfg: `rlmMaxDepth` is a Global cvar: only the global config.cfg sets it"
                        .to_string()
                ),
                (
                    SettingsScope::Project,
                    "Project is not trusted: ignored project settings shellPath. To allow them, add the project directory to trustedProjects in the global settings."
                        .to_string()
                ),
            ]
        )
    );
    assert_eq!(
        (manager.get_rlm_max_depth(), manager.get_shell_path()),
        (None, None)
    );
}

/// The global command replaces the line that set the cvar, in place, keeps
/// every other command and comment, and the value applies at once; a bad
/// value writes nothing.
#[test]
fn run_global_replaces_the_line() {
    let store = storage(
        "{}",
        &[(
            SettingsScope::Global,
            "config.cfg",
            "# mine\nset transport sse; set theme dark\nset retry.enabled off\n",
        )],
    );
    let mut manager = SettingsManager::from_storage(Arc::clone(&store));
    manager
        .run_global(&parse_list("set transport web-socket").expect("parse"))
        .expect("set");
    let written = "# mine\nset theme dark\nset transport web-socket\nset retry.enabled off\n";
    assert_eq!(
        store
            .read_cfg(SettingsScope::Global, "config.cfg")
            .expect("read"),
        Some(written.to_string())
    );
    assert_eq!(manager.get_transport(), TransportSetting::WebSocket);
    assert_eq!(
        manager.run_global(&parse_list("set transport pigeon").expect("parse")),
        Err(CvarWriteError::Cvar(CvarError::BadValue {
            id: "transport".to_string(),
            value: "pigeon".to_string(),
            expected: "one of auto, sse, web-socket, websocket-cached".to_string(),
        }))
    );
    assert_eq!(
        store
            .read_cfg(SettingsScope::Global, "config.cfg")
            .expect("read"),
        Some(written.to_string())
    );
}

/// Regression: a global toggle flipped the value with the project's sets
/// applied, and wrote that to the global config.cfg. It flips the global
/// layer's value alone.
#[test]
fn a_global_toggle_flips_the_global_value_not_the_projects() {
    let store = storage(
        "{}",
        &[(
            SettingsScope::Project,
            "config.cfg",
            "set retry.enabled off\n",
        )],
    );
    let mut manager = SettingsManager::from_storage(Arc::clone(&store));
    assert!(!manager.get_retry_enabled());
    manager
        .run_global(&parse_list("toggle retry.enabled").expect("parse"))
        .expect("toggle");
    assert_eq!(
        store
            .read_cfg(SettingsScope::Global, "config.cfg")
            .expect("read"),
        Some("set retry.enabled false\n".to_string())
    );
}

/// Regression: a `config.cfg` or `agents/<name>.cfg` that exists but
/// cannot be read (here: not UTF-8) read as absent, so the load said
/// nothing and a write replaced the user's file with one line. The load
/// reports it, every writer refuses, and the bytes stay.
#[test]
fn an_unreadable_cfg_file_is_reported_and_never_overwritten() {
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(agent_dir.join("agents")).expect("agent dir");
    let bytes = b"set theme dark\n\xff\xfe\n";
    let config = agent_dir.join("config.cfg");
    let profile = agent_dir.join("agents/main.cfg");
    std::fs::write(&config, bytes).expect("write");
    std::fs::write(&profile, bytes).expect("write");
    let mut manager = SettingsManager::create(dir.path().join("cwd"), &agent_dir);
    let unreadable = |path: &std::path::Path| {
        format!(
            "cannot read {}: stream did not contain valid UTF-8",
            path.display()
        )
    };
    let (_, _, failures) = manager.read_profile(&["agents/main.cfg".to_string()]);
    assert_eq!(
        (
            errors(&manager),
            failures
                .iter()
                .map(|error| (error.scope, error.message.clone()))
                .collect::<Vec<_>>()
        ),
        (
            vec![(
                SettingsScope::Global,
                format!("config.cfg: {}", unreadable(&config))
            )],
            vec![(
                SettingsScope::Global,
                format!("agents/main.cfg: {}", unreadable(&profile))
            )]
        )
    );
    assert_eq!(
        (
            manager.run_global(&parse_list("set transport sse").expect("parse")),
            manager.write_agent_cfg("main", &Sets(vec![set("steeringMode", json!("all"))]))
        ),
        (
            Err(CvarWriteError::Io(unreadable(&config))),
            Err(CvarWriteError::Io(unreadable(&profile)))
        )
    );
    assert_eq!(
        (
            std::fs::read(&config).expect("read"),
            std::fs::read(&profile).expect("read")
        ),
        (bytes.to_vec(), bytes.to_vec())
    );
}

/// Regression: the global write read the file, then wrote it under a
/// separate lock, so two sessions setting two cvars at once could lose
/// one. The read-modify-write holds one lock: both sets land.
#[test]
fn concurrent_global_sets_both_land() {
    for _ in 0..20 {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");
        std::fs::write(agent_dir.join("config.cfg"), "# mine\n").expect("write");
        let cwd = dir.path().join("cwd");
        let barrier = std::sync::Barrier::new(2);
        std::thread::scope(|scope| {
            for line in ["set transport sse", "set theme dark"] {
                let (barrier, cwd, agent_dir) = (&barrier, &cwd, &agent_dir);
                scope.spawn(move || {
                    let mut manager = SettingsManager::create(cwd, agent_dir);
                    barrier.wait();
                    manager
                        .run_global(&parse_list(line).expect("parse"))
                        .expect("set");
                });
            }
        });
        let mut lines: Vec<String> = std::fs::read_to_string(agent_dir.join("config.cfg"))
            .expect("read")
            .lines()
            .map(str::to_string)
            .collect();
        lines.sort();
        assert_eq!(
            lines,
            vec![
                "# mine".to_string(),
                "set theme dark".to_string(),
                "set transport sse".to_string(),
            ]
        );
    }
}

/// What `write_agent_cfg` writes, `read_profile` reads back as the same
/// profile; the file's other lines stay, and a Global cvar is refused.
#[test]
fn write_agent_cfg_round_trips_through_read_profile() {
    let store = storage(
        "{}",
        &[(
            SettingsScope::Global,
            "agents/main.cfg",
            "alias quiet \"set quietStartup on\"\nset steeringMode all\n",
        )],
    );
    let mut manager = SettingsManager::from_storage(Arc::clone(&store));
    let sets = Sets(vec![
        set("steeringMode", json!("one-at-a-time")),
        set("compaction.enabled", json!(false)),
    ]);
    manager.write_agent_cfg("main", &sets).expect("write");
    let (profile, aliases, failures) = manager.read_profile(&["agents/main.cfg".to_string()]);
    assert_eq!(
        (
            profile,
            aliases.iter().map(|(name, _)| name).collect::<Vec<_>>(),
            failures.len()
        ),
        (sets, vec!["quiet"], 0)
    );
    assert_eq!(
        manager.write_agent_cfg("main", &Sets(vec![set("rlmMaxDepth", json!(3))])),
        Err(CvarWriteError::Cvar(CvarError::Global {
            id: "rlmMaxDepth".to_string(),
        }))
    );
}

/// Regression: a setter used to write the whole global document even when
/// `settings.json` had failed to parse, replacing the user's file with the
/// defaults plus one field. The broken file now stays byte-identical and
/// the setter fails.
#[test]
fn a_setter_never_clobbers_a_global_settings_file_that_failed_to_parse() {
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let path = agent_dir.join("settings.json");
    let broken = "{ \"theme\": \"dark\", oops }\n";
    std::fs::write(&path, broken).expect("write");
    let mut manager = SettingsManager::create(dir.path().join("cwd"), &agent_dir);
    assert!(manager.set_theme("light".to_string()).is_err());
    assert_eq!(std::fs::read_to_string(&path).expect("read"), broken);
}

/// The scope that sets a cvar: the global config.cfg over the global
/// settings.json, the project settings.json for a Local key it holds,
/// nothing for an unset key.
#[test]
fn config_scope_names_the_file_that_sets_the_cvar() {
    use crate::settings::cvar::table;
    let store = storage(
        r#"{ "memory": { "model": "a/b" }, "auxiliaryModel": "g/h" }"#,
        &[(
            SettingsScope::Global,
            "config.cfg",
            "set memory.model c/d\n",
        )],
    );
    store
        .with_lock(SettingsScope::Project, &mut |_| {
            Some(r#"{ "modelRoles": { "tiny": "local/lfm2.5-230m" } }"#.to_string())
        })
        .expect("project settings.json");
    let manager = SettingsManager::from_storage(store);
    assert_eq!(
        [
            &table::MEMORY_MODEL,
            &table::AUXILIARY_MODEL,
            &table::MODEL_ROLE_TINY,
            &table::IMAGE_MODEL,
        ]
        .map(|decl| manager.config_scope(decl)),
        [
            Some(SettingsScope::Global),
            Some(SettingsScope::Global),
            Some(SettingsScope::Project),
            None,
        ]
    );
}

/// Clearing a global cvar takes its key out of the global settings.json
/// and its sets out of the global config.cfg (a line's other commands
/// stay); the default applies at once.
#[test]
fn clear_global_unsets_the_cvar_in_both_global_files() {
    use crate::settings::cvar::table;
    let store = storage(
        r#"{ "memory": { "model": "a/b", "thinking": "high" } }"#,
        &[(
            SettingsScope::Global,
            "config.cfg",
            "# mine\nset memory.model c/d; set theme dark\n",
        )],
    );
    let mut manager = SettingsManager::from_storage(Arc::clone(&store));
    assert_eq!(manager.get_memory_model().as_deref(), Some("c/d"));
    manager
        .clear_global(&[&table::MEMORY_MODEL])
        .expect("clear");
    assert_eq!(
        (
            manager.get_memory_model(),
            manager.config_scope(&table::MEMORY_MODEL),
            store
                .read_cfg(SettingsScope::Global, "config.cfg")
                .expect("read"),
        ),
        (None, None, Some("# mine\nset theme dark\n".to_string()))
    );
    assert_eq!(
        manager.get_memory_thinking(),
        crate::settings::ThinkingLevelSetting::High
    );
}

/// A session run from the agent dir's parent (`eukhe` launched in the
/// home directory) resolves the project `config.cfg` to the global one:
/// the global sets apply once, and the global file's own Global cvars
/// raise no project error.
#[test]
fn a_session_in_the_agent_dirs_parent_reads_its_config_once() {
    let dir = tempfile::tempdir().expect("tempdir");
    let home = dir.path().join("home");
    std::fs::create_dir_all(home.join(".eukhe")).expect("agent dir");
    let storage: Arc<dyn SettingsStorage> =
        Arc::new(FileSettingsStorage::new(&home, home.join(".eukhe")));
    storage
        .with_lock(SettingsScope::Global, &mut |_| Some("{}".to_string()))
        .expect("settings.json");
    storage
        .with_cfg_lock(SettingsScope::Global, "config.cfg", &mut |_| {
            Some("set memory.model zai/glm-5.3-flash\nset memory.thinking low\n".to_string())
        })
        .expect("cfg");
    let manager = SettingsManager::from_storage(Arc::clone(&storage));
    assert!(
        errors(&manager).is_empty(),
        "the global config.cfg must not error as the project one: {:?}",
        errors(&manager)
    );
    assert_eq!(
        (
            manager.get_memory_model().as_deref(),
            manager.get_memory_thinking()
        ),
        (
            Some("zai/glm-5.3-flash"),
            crate::settings::ThinkingLevelSetting::Low
        )
    );
}
