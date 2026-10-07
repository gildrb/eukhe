//! Provider environment lookup.
//!
//! The TS module also reads `/proc/self/environ` when running as a Bun
//! compiled binary whose `process.env` is empty (oven-sh/bun#27802). That
//! branch only applies under Bun; a Rust process always sees its real
//! environment, so the lookup is scoped overrides, then the process env.

use eukhe_types::pi_ai::ProviderEnv;

/// Resolve a provider env value from scoped overrides, then the process
/// environment. Empty values count as unset (TS `||`).
#[must_use]
pub fn get_provider_env_value(name: &str, env: Option<&ProviderEnv>) -> Option<String> {
    if let Some(value) = env
        .and_then(|env| env.get(name))
        .filter(|value| !value.is_empty())
    {
        return Some(value.clone());
    }
    std::env::var_os(name)
        .map(|value| value.to_string_lossy().into_owned())
        .filter(|value| !value.is_empty())
}
