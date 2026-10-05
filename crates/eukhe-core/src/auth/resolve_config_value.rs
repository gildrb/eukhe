//! Resolve config values: `!command` (successful results are cached),
//! env var, or literal.
//! Port of resolve-config-value.ts.

use std::collections::HashMap;
use std::sync::Mutex;

use anyhow::Result;

static COMMAND_RESULT_CACHE: Mutex<Option<HashMap<String, String>>> = Mutex::new(None);

/// Resolve a config value: `!command` executes and caches successful
/// results; otherwise the environment wins over the literal string
/// (set-but-empty means missing).
pub fn resolve_config_value(config: &str) -> Option<String> {
    if let Some(command) = config.strip_prefix('!') {
        return execute_command(config, command);
    }
    resolve_env_or_literal(config)
}

/// Never-cached variant used when a command key was marked stale.
pub fn resolve_config_value_uncached(config: &str) -> Option<String> {
    if let Some(command) = config.strip_prefix('!') {
        return run_command(command).ok().flatten();
    }
    resolve_env_or_literal(config)
}

/// Unset env var falls back to the literal string; set-but-empty is a missing
/// credential (never the variable name).
fn resolve_env_or_literal(config: &str) -> Option<String> {
    match std::env::var(config) {
        Ok(value) if !value.is_empty() => Some(value),
        Ok(_) => None,
        Err(_) => Some(config.to_string()),
    }
}

fn execute_command(cache_key: &str, command: &str) -> Option<String> {
    let mut cache = COMMAND_RESULT_CACHE.lock().unwrap();
    let cache = cache.get_or_insert_with(HashMap::new);
    if let Some(cached) = cache.get(cache_key) {
        return Some(cached.clone());
    }
    let value = run_command(command).ok().flatten();
    // A command that produced no value is not a resolution: a locked
    // keychain, a missing network, or a rotated secret must be retried on
    // the next lookup instead of pinning the failure for the lifetime of
    // the process (TS #2497).
    if let Some(value) = &value {
        cache.insert(cache_key.to_string(), value.clone());
    }
    value
}

fn run_command(command: &str) -> Result<Option<String>> {
    // Hidden spawn: stdin closed, stdout captured, stderr suppressed.
    let output = hidden_spawn(command)?;
    if !output.status.success() {
        return Ok(None);
    }
    let value = String::from_utf8_lossy(&output.stdout).trim().to_string();
    Ok((!value.is_empty()).then_some(value))
}

/// Hidden command execution for `!command` config values (TS
/// `resolve-config-value`: the default shell).
fn hidden_spawn(command: &str) -> std::io::Result<std::process::Output> {
    use std::process::{Command, Stdio};
    Command::new("bash")
        .arg("-c")
        .arg(command)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .output()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn env_or_literal_semantics() {
        // Literal when the variable is unset.
        let key = "EUKHE_TEST_DEFINITELY_UNSET_VAR";
        assert_eq!(resolve_env_or_literal(key), Some(key.to_string()));
    }

    #[test]
    fn command_resolution_and_cache() {
        let value = resolve_config_value("!echo resolved-value");
        assert_eq!(value.as_deref(), Some("resolved-value"));
        // A successful command runs once per process (the cache holds it).
        assert_eq!(
            resolve_config_value("!echo resolved-value").as_deref(),
            Some("resolved-value")
        );

        // A failing command resolves to None and is retried on every
        // lookup (TS #2497: a locked keychain or a transient failure must
        // not disable the credential for the process lifetime). The
        // counter proves each lookup re-ran the command.
        let counter = std::env::temp_dir().join(format!("pa-resolve-retry-{}", std::process::id()));
        let _ = std::fs::remove_file(&counter);
        let command = format!("echo x >> {} ; exit 1", counter.display());
        for _ in 0..3 {
            assert_eq!(resolve_config_value(&format!("!{command}")), None);
        }
        let runs = std::fs::read_to_string(&counter).map_or(0, |text| text.lines().count());
        let _ = std::fs::remove_file(&counter);
        assert_eq!(runs, 3, "failed commands are re-run on each lookup");
    }
}
