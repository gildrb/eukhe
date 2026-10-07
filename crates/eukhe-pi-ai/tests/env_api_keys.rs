//! Port of `test/env-api-keys.test.ts`.
//!
//! The cases mutate the process environment: [`EnvGuard`] serializes them
//! within this binary and restores the variables afterwards (TS `afterEach`).

use std::sync::{Mutex, MutexGuard, PoisonError};

use eukhe_pi_ai::env_api_keys::{find_env_keys, get_env_api_key};

static ENV_LOCK: Mutex<()> = Mutex::new(());

const TOUCHED: [&str; 7] = [
    "COPILOT_GITHUB_TOKEN",
    "GH_TOKEN",
    "GITHUB_TOKEN",
    "ZAI_CODING_CN_API_KEY",
    "ANTHROPIC_AUTH_TOKEN",
    "ANTHROPIC_OAUTH_TOKEN",
    "ANTHROPIC_API_KEY",
];

/// Holds the env lock and restores the original values on drop.
struct EnvGuard {
    original: Vec<(&'static str, Option<String>)>,
    _lock: MutexGuard<'static, ()>,
}

impl EnvGuard {
    fn new() -> Self {
        let lock = ENV_LOCK.lock().unwrap_or_else(PoisonError::into_inner);
        Self {
            original: TOUCHED
                .iter()
                .map(|name| (*name, std::env::var(name).ok()))
                .collect(),
            _lock: lock,
        }
    }
}

impl Drop for EnvGuard {
    fn drop(&mut self) {
        for (name, value) in &self.original {
            match value {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
    }
}

#[test]
fn does_not_treat_generic_github_tokens_as_github_copilot_credentials() {
    let _env = EnvGuard::new();
    std::env::remove_var("COPILOT_GITHUB_TOKEN");
    std::env::set_var("GH_TOKEN", "gh-token");
    std::env::set_var("GITHUB_TOKEN", "github-token");

    assert_eq!(find_env_keys("github-copilot", None), None);
    assert_eq!(get_env_api_key("github-copilot", None), None);
}

#[test]
fn resolves_github_copilot_credentials_from_copilot_github_token() {
    let _env = EnvGuard::new();
    std::env::set_var("COPILOT_GITHUB_TOKEN", "copilot-token");
    std::env::set_var("GH_TOKEN", "gh-token");
    std::env::set_var("GITHUB_TOKEN", "github-token");

    assert_eq!(
        find_env_keys("github-copilot", None),
        Some(vec!["COPILOT_GITHUB_TOKEN".to_owned()])
    );
    assert_eq!(
        get_env_api_key("github-copilot", None).as_deref(),
        Some("copilot-token")
    );
}

#[test]
fn resolves_zai_china_coding_plan_credentials_from_zai_coding_cn_api_key() {
    let _env = EnvGuard::new();
    std::env::set_var("ZAI_CODING_CN_API_KEY", "zai-coding-cn-token");

    assert_eq!(
        find_env_keys("zai-coding-cn", None),
        Some(vec!["ZAI_CODING_CN_API_KEY".to_owned()])
    );
    assert_eq!(
        get_env_api_key("zai-coding-cn", None).as_deref(),
        Some("zai-coding-cn-token")
    );
}

#[test]
fn reports_anthropic_auth_token_but_preserves_oauth_token_api_key_lookup() {
    let _env = EnvGuard::new();
    std::env::set_var("ANTHROPIC_AUTH_TOKEN", "auth-token");
    std::env::set_var("ANTHROPIC_OAUTH_TOKEN", "oauth-token");
    std::env::set_var("ANTHROPIC_API_KEY", "api-key");

    assert_eq!(
        find_env_keys("anthropic", None),
        Some(vec![
            "ANTHROPIC_AUTH_TOKEN".to_owned(),
            "ANTHROPIC_OAUTH_TOKEN".to_owned(),
            "ANTHROPIC_API_KEY".to_owned(),
        ])
    );
    assert_eq!(
        get_env_api_key("anthropic", None).as_deref(),
        Some("oauth-token")
    );
}

#[test]
fn does_not_return_anthropic_auth_token_as_an_api_key() {
    let _env = EnvGuard::new();
    std::env::set_var("ANTHROPIC_AUTH_TOKEN", "auth-token");
    std::env::remove_var("ANTHROPIC_OAUTH_TOKEN");
    std::env::remove_var("ANTHROPIC_API_KEY");

    assert_eq!(
        find_env_keys("anthropic", None),
        Some(vec!["ANTHROPIC_AUTH_TOKEN".to_owned()])
    );
    assert_eq!(get_env_api_key("anthropic", None), None);
}

#[test]
fn preserves_anthropic_oauth_token_as_an_api_key() {
    let _env = EnvGuard::new();
    std::env::remove_var("ANTHROPIC_AUTH_TOKEN");
    std::env::set_var("ANTHROPIC_OAUTH_TOKEN", "oauth-token");
    std::env::remove_var("ANTHROPIC_API_KEY");

    assert_eq!(
        find_env_keys("anthropic", None),
        Some(vec!["ANTHROPIC_OAUTH_TOKEN".to_owned()])
    );
    assert_eq!(
        get_env_api_key("anthropic", None).as_deref(),
        Some("oauth-token")
    );
}

#[test]
fn falls_back_to_anthropic_api_key_for_api_key_lookup() {
    let _env = EnvGuard::new();
    std::env::remove_var("ANTHROPIC_AUTH_TOKEN");
    std::env::remove_var("ANTHROPIC_OAUTH_TOKEN");
    std::env::set_var("ANTHROPIC_API_KEY", "api-key");

    assert_eq!(
        get_env_api_key("anthropic", None).as_deref(),
        Some("api-key")
    );
}
