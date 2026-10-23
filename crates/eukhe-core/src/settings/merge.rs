//! Deep-merge and migration (settings-manager.ts).

use serde_json::Value;

use super::types::Settings;

/// Settings that map names to entries: an entry is one unit, so an
/// override entry replaces the base entry of its name whole and never
/// takes keys (a URL, a credential) from it (`laws/config.bend`
/// `project_entry_never_merges`).
const ENTRY_MAPS: &[&str] = &["mcpServers"];

/// Settings that are one unit (where the kernel runs and how it reaches
/// it): an override replaces the base value whole.
const UNITS: &[&str] = &["kernelTransport"];

/// Deep merge: overrides win; nested objects merge recursively; arrays and
/// scalars replace (`deepMergeSettings`); the entries of [`ENTRY_MAPS`]
/// and the values of [`UNITS`] replace whole.
pub fn deep_merge(base: &Settings, overrides: &Settings) -> Settings {
    let mut base_value = serde_json::to_value(base).unwrap_or_default();
    let overrides_value = serde_json::to_value(overrides).unwrap_or_default();
    if let (Value::Object(base_obj), Value::Object(overrides_obj)) =
        (&mut base_value, &overrides_value)
    {
        for (key, value) in overrides_obj {
            if value.is_null() {
                continue;
            }
            let entries = ENTRY_MAPS.contains(&key.as_str());
            match (base_obj.get_mut(key), value) {
                (Some(Value::Object(base_entries)), Value::Object(entries_value)) if entries => {
                    for (name, entry) in entries_value {
                        if !entry.is_null() {
                            base_entries.insert(name.clone(), entry.clone());
                        }
                    }
                }
                (Some(existing), _) if !UNITS.contains(&key.as_str()) && !entries => {
                    merge_values(existing, value);
                }
                (Some(_) | None, _) => {
                    base_obj.insert(key.clone(), value.clone());
                }
            }
        }
    }
    serde_json::from_value(base_value).unwrap_or_default()
}

fn merge_values(base: &mut Value, overrides: &Value) {
    match (base, overrides) {
        (Value::Object(base_obj), Value::Object(overrides_obj)) => {
            for (key, value) in overrides_obj {
                // `null` means the key is unset (TS documents omit undefined
                // keys); it must never override a real value.
                if value.is_null() {
                    continue;
                }
                match base_obj.get_mut(key) {
                    Some(existing) if existing.is_object() && value.is_object() => {
                        merge_values(existing, value);
                    }
                    _ => {
                        base_obj.insert(key.clone(), value.clone());
                    }
                }
            }
        }
        (base_slot, value) => {
            if !value.is_null() {
                *base_slot = value.clone();
            }
        }
    }
}

/// Migrate legacy settings shapes (queueMode, websockets, skills object,
/// retry.maxDelayMs, onboardingCompleted) - port of `migrateSettings`. A
/// `markdown` that is not an object stays: the load names it.
pub fn migrate(document: &mut serde_json::Map<String, Value>) {
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
                .or_insert_with(|| Value::Object(serde_json::Map::new()));
            if let Some(provider_obj) = provider.as_object_mut() {
                provider_obj
                    .entry("maxRetryDelayMs")
                    .or_insert(Value::Number(delay));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn merge_prefers_overrides_and_merges_nested() {
        let base: Settings = serde_json::from_value(json!({
            "theme": "eukhe", "compaction": { "enabled": true, "reserveTokens": 1024 }
        }))
        .unwrap();
        let overrides: Settings = serde_json::from_value(json!({
            "compaction": { "reserveTokens": 2048 }
        }))
        .unwrap();
        let merged = deep_merge(&base, &overrides);
        assert_eq!(merged.theme.as_deref(), Some("eukhe"));
        assert_eq!(merged.compaction.as_ref().unwrap().enabled, Some(true));
        assert_eq!(
            merged.compaction.as_ref().unwrap().reserve_tokens,
            Some(2048)
        );
    }

    /// Regression (audit M7): a project `mcpServers.github` with its own
    /// URL merged into the global entry and kept its token header. A
    /// project entry now replaces the global entry of its name whole;
    /// other global entries stay.
    #[test]
    fn a_project_mcp_entry_never_takes_global_credentials() {
        let global: Settings = serde_json::from_value(json!({
            "mcpServers": {
                "github": {
                    "type": "http",
                    "url": "https://api.github.com/mcp",
                    "headers": { "Authorization": "Bearer secret" },
                    "bearerTokenEnvVar": "GITHUB_TOKEN"
                },
                "notes": { "type": "stdio", "command": "notes-mcp" }
            },
            "kernelTransport": { "type": "ssh", "host": "box", "identity": "~/.ssh/id" }
        }))
        .unwrap();
        let project: Settings = serde_json::from_value(json!({
            "mcpServers": { "github": { "type": "http", "url": "https://other/mcp" } },
            "kernelTransport": { "type": "local" }
        }))
        .unwrap();
        let merged = serde_json::to_value(deep_merge(&global, &project)).unwrap();
        assert_eq!(
            (&merged["mcpServers"], &merged["kernelTransport"]),
            (
                &json!({
                    "github": { "type": "http", "url": "https://other/mcp" },
                    "notes": { "type": "stdio", "command": "notes-mcp" }
                }),
                &json!({ "type": "local" })
            )
        );
    }

    #[test]
    fn migration_rewrites_legacy_shapes() {
        let mut doc = json!({
            "queueMode": "all",
            "websockets": true,
            "skills": { "enableSkillCommands": false, "customDirectories": ["/x"] },
            "retry": { "maxDelayMs": 5 }
        });
        let mut map = doc.as_object_mut().unwrap().clone();
        migrate(&mut map);
        assert_eq!(map.get("steeringMode"), Some(&json!("all")));
        assert_eq!(map.get("transport"), Some(&json!("web-socket")));
        assert_eq!(map.get("skills"), Some(&json!(["/x"])));
        assert_eq!(
            map.get("retry"),
            Some(&json!({ "provider": { "maxRetryDelayMs": 5 } }))
        );
    }
}
