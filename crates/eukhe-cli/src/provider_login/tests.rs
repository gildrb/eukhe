//! The provider-login unit battery (moved beside its module at the
//! 2026-09-30 file-size cap: the flows and their tests stay one tree).

use super::*;

#[test]
fn the_status_indicator_maps_the_ts_labels() {
    let stored_api_key = AuthCredential::ApiKey {
        key: "k".to_string(),
    };
    // A matching stored credential is configured.
    assert_eq!(
        status_indicator(
            Some(&stored_api_key),
            &AuthStatus {
                source: Some(AuthSource::Stored),
                ..Default::default()
            },
            AuthType::ApiKey
        ),
        Some(AuthStatusIndicator {
            style: AuthStatusStyle::Success,
            label: "configured".to_string()
        })
    );
    // A subscription credential on an api-key row warns.
    assert_eq!(
        status_indicator(
            Some(&AuthCredential::Oauth {
                access: "a".to_string(),
                refresh: None,
                expires: 1,
                account_id: None,
                endpoint: None,
                token_endpoint: None,
                client_id: None,
                resource: None,
                issuer: None,
                enterprise_url: None,
            }),
            &AuthStatus::default(),
            AuthType::ApiKey
        ),
        Some(AuthStatusIndicator {
            style: AuthStatusStyle::Warning,
            label: "subscription configured".to_string()
        })
    );
    // An env key marks the api-key row configured.
    assert_eq!(
        status_indicator(
            None,
            &AuthStatus {
                source: Some(AuthSource::Environment),
                label: Some("OPENAI_API_KEY".to_string()),
                ..Default::default()
            },
            AuthType::ApiKey
        ),
        Some(AuthStatusIndicator {
            style: AuthStatusStyle::Success,
            label: "env: OPENAI_API_KEY".to_string()
        })
    );
    // An unconfigured subscription row stays muted.
    assert_eq!(
        status_indicator(None, &AuthStatus::default(), AuthType::Oauth),
        Some(AuthStatusIndicator {
            style: AuthStatusStyle::Muted,
            label: "unconfigured".to_string()
        })
    );
    // An unconfigured api-key row hides its meta (TS inline rule).
    assert_eq!(
        status_indicator(None, &AuthStatus::default(), AuthType::ApiKey),
        None
    );
    // A stale credential warns.
    assert_eq!(
        status_indicator(
            None,
            &AuthStatus {
                source: Some(AuthSource::Stale),
                label: Some("expired".to_string()),
                ..Default::default()
            },
            AuthType::Oauth
        ),
        Some(AuthStatusIndicator {
            style: AuthStatusStyle::Warning,
            label: "expired".to_string()
        })
    );
}

#[test]
fn the_display_names_match_the_ts_map() {
    assert_eq!(display_name("openai"), "OpenAI");
    assert_eq!(display_name("google"), "Google Gemini");
    assert_eq!(display_name("a-custom-provider"), "a-custom-provider");
}

#[test]
fn the_api_key_login_rule_matches_ts() {
    let mut built_in = std::collections::HashSet::new();
    built_in.insert("anthropic".to_string());
    // The display-name map marks api-key logins.
    assert!(is_api_key_login_provider("openai", &built_in));
    // A provider the built-in set does not know is a custom api-key
    // provider.
    assert!(is_api_key_login_provider("my-endpoint", &built_in));
    // A built-in provider without a display name is not an api-key
    // login (its subscription flows apply).
    assert!(!is_api_key_login_provider("faux", &{
        let mut set = std::collections::HashSet::new();
        set.insert("faux".to_string());
        set
    }));
}

#[tokio::test]
async fn login_options_list_providers_only() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = dir.path().join("agent");
    std::fs::create_dir_all(&agent).expect("agent dir");
    let auth = ProviderAuth::new(dir.path(), agent.clone());
    let rows = auth.login_options().await;
    // The TS OAuth registry rows render; every subscription flow is
    // ported, so every row selects (the flows answer through the
    // panel -- never an after-selection error wall).
    for (id, name) in SUBSCRIPTION_PROVIDERS {
        let row = rows
            .iter()
            .find(|row| row.id == id && row.name == name)
            .unwrap_or_else(|| panic!("the {id} subscription row renders"));
        assert!(
            row.available,
            "the {id} row's flow is ported and selectable"
        );
    }
    // The operator's 2026-09-24 directive: /login is providers only --
    // the MCP OAuth integration rows never appear; the /mcp view owns
    // MCP logins.
    assert!(!rows.iter().any(|row| row.id.starts_with("mcp:")));
}

/// `/accounts` heads its list with the migration notice exactly when
/// `auth.json` holds a Claude subscription login.
#[tokio::test]
async fn the_accounts_notice_names_a_stored_claude_subscription_login() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = dir.path().join("agent");
    std::fs::create_dir_all(&agent).expect("agent dir");
    let auth = ProviderAuth::new(dir.path(), agent.clone());
    let mut storage = eukhe_core::auth::AuthStorage::create(&agent);
    storage
        .set(
            "anthropic",
            AuthCredential::ApiKey {
                key: "sk-ant-api03-plain".to_string(),
            },
        )
        .unwrap();
    let with_api_key = auth.accounts_notice().await;
    storage
        .set(
            "anthropic",
            AuthCredential::Oauth {
                access: "a".to_string(),
                refresh: None,
                expires: i64::MAX,
                endpoint: None,
                token_endpoint: None,
                client_id: None,
                resource: None,
                issuer: None,
                account_id: None,
                enterprise_url: None,
            },
        )
        .unwrap();
    assert_eq!(
        (with_api_key, auth.accounts_notice().await),
        (
            None,
            Some(eukhe_ai::api::anthropic_messages::CLAUDE_LOGIN_MOVED)
        )
    );
}

#[tokio::test]
async fn login_stores_an_api_key_and_logout_removes_it() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = dir.path().join("agent");
    std::fs::create_dir_all(&agent).expect("agent dir");
    let auth = ProviderAuth::new(dir.path(), agent);
    let row = ProviderRow {
        id: "openai".to_string(),
        name: "OpenAI".to_string(),
        auth_type: AuthType::ApiKey,
        status: None,
        flow: AuthFlow::ApiKeyPrompt,
        configured: false,
        available: true,
        account: None,
    };
    match auth.login(&row, Some("sk-test")).await {
        ProviderAuthOutcome::Status(message) => {
            assert!(
                message.starts_with("Saved API key for OpenAI as key. Credentials saved to "),
                "the store status names the credential path: {message}"
            );
        }
        other => panic!("expected the store status, got {other:?}"),
    }
    // An empty key answers the TS error.
    assert_eq!(
        auth.login(&row, Some("")).await,
        ProviderAuthOutcome::Error(
            "Failed to save API key for OpenAI: API key cannot be empty.".to_string()
        )
    );
    // The logout lists the stored account and removes it.
    let stored = auth.logout_options().await;
    assert_eq!(
        stored
            .iter()
            .map(|row| (row.id.as_str(), row.name.as_str(), row.account.as_deref()))
            .collect::<Vec<_>>(),
        vec![("openai", "OpenAI: key", Some("key"))]
    );
    assert_eq!(
        auth.logout(&stored[0].id, stored[0].account.as_deref())
            .await,
        ProviderAuthOutcome::Status("Removed key from openai (0 left).".to_string())
    );
    assert!(auth.logout_options().await.is_empty());
}
