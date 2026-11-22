//! The stored accounts of each provider: the listing `/accounts` and
//! `eukhe provider accounts` print, and the removal of one account behind
//! `/logout <provider> [n|identity]` and `eukhe provider logout`.

use std::path::Path;

use eukhe_core::auth::{Account, AccountSelector, AuthStorage};
use eukhe_daemon::limits_text::LocalClock;
use eukhe_tui::provider_auth::{AccountRow, ProviderAccounts, ProviderAuthOutcome};
use serde_json::{json, Value};

/// The prefix of an MCP server's entry: one credential, never accounts.
const MCP_PREFIX: &str = "mcp:";

/// Each provider's stored accounts, sorted by provider id; MCP servers
/// and providers without an account are left out.
pub(crate) fn stored_accounts(auth: &AuthStorage) -> Vec<(String, Vec<Account>)> {
    let data = auth.get_all();
    let mut stored: Vec<(String, Vec<Account>)> = auth
        .list()
        .into_iter()
        .filter(|provider| !provider.starts_with(MCP_PREFIX))
        .map(|provider| {
            let accounts = data.accounts(&provider);
            (provider, accounts)
        })
        .filter(|(_, accounts)| !accounts.is_empty())
        .collect();
    stored.sort_by(|(left, _), (right, _)| left.cmp(right));
    stored
}

/// The listing rows of `stored`: each account's label, and while its limit
/// lasts at `now_ms`, the local time it resets.
pub(crate) fn listing(
    stored: &[(String, Vec<Account>)],
    now_ms: u64,
    clock: LocalClock<'_>,
) -> Vec<ProviderAccounts> {
    stored
        .iter()
        .map(|(provider, accounts)| ProviderAccounts {
            provider: provider.clone(),
            accounts: accounts
                .iter()
                .enumerate()
                .map(|(at, account)| AccountRow {
                    identity: account.identity.clone(),
                    label: account.label(at + 1),
                    limited_until: account
                        .limited_until_ms
                        .filter(|until| *until > now_ms)
                        .map(|until| {
                            eukhe_daemon::limits_text::local_when(until, now_ms, clock)
                                .unwrap_or_else(|| eukhe_daemon::util::iso_from_unix_ms(until))
                        }),
                })
                .collect(),
        })
        .collect()
}

/// The JSON listing: `{"providers":[{"provider", "accounts":[{"place",
/// "identity", "limitedUntilMs"}]}]}`.
pub(crate) fn listing_json(stored: &[(String, Vec<Account>)]) -> Value {
    let providers: Vec<Value> = stored
        .iter()
        .map(|(provider, accounts)| {
            let accounts: Vec<Value> = accounts
                .iter()
                .enumerate()
                .map(|(at, account)| {
                    json!({
                        "place": at + 1,
                        "identity": account.identity,
                        "limitedUntilMs": account.limited_until_ms,
                    })
                })
                .collect();
            json!({ "provider": provider, "accounts": accounts })
        })
        .collect();
    json!({ "providers": providers })
}

/// `1. a@x.com, 2. b@y.com`.
fn numbered(accounts: &[Account]) -> String {
    accounts
        .iter()
        .enumerate()
        .map(|(at, account)| format!("{}. {}", at + 1, account.label(at + 1)))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Remove one stored account of `provider` (blocking: the auth store's
/// file lock): the one `account` names (a place from 1 or an identity);
/// without one, the provider's only account, or an MCP server's
/// credential. Several accounts and none named, or a name no account has,
/// answer the error that lists them.
pub(crate) fn logout(
    agent_dir: &Path,
    provider: &str,
    account: Option<&str>,
) -> ProviderAuthOutcome {
    let mut auth = AuthStorage::create(agent_dir);
    if let Some(error) = auth.load_error() {
        return ProviderAuthOutcome::Error(format!(
            "Logout failed: {} could not be loaded: {error}",
            agent_dir.join(eukhe_core::auth::AUTH_FILE_NAME).display()
        ));
    }
    if let Some(server) = provider.strip_prefix(MCP_PREFIX) {
        if !auth.has(provider) {
            return ProviderAuthOutcome::Error(format!("{provider} has no stored credential."));
        }
        return match auth.remove(provider) {
            Ok(()) => ProviderAuthOutcome::Status(format!("Logged out of {server}.")),
            Err(error) => ProviderAuthOutcome::Error(format!("Logout failed: {error}")),
        };
    }
    let accounts = auth.get_all().accounts(provider);
    if accounts.is_empty() {
        return ProviderAuthOutcome::Error(format!("{provider} has no stored accounts."));
    }
    let named = account.map(str::trim).filter(|text| !text.is_empty());
    let selector = match named {
        Some(text) => AccountSelector::parse(text),
        None if accounts.len() == 1 => AccountSelector::Place(1),
        None => {
            return ProviderAuthOutcome::Error(format!(
                "{provider} has {} accounts: {}. Name one by its number or identity.",
                accounts.len(),
                numbered(&accounts)
            ));
        }
    };
    match auth.remove_account(provider, &selector) {
        Ok(Some(label)) => ProviderAuthOutcome::Status(format!(
            "Removed {label} from {provider} ({} left).",
            auth.get_all().accounts(provider).len()
        )),
        Ok(None) => ProviderAuthOutcome::Error(format!(
            "{provider} has no account {}. Its accounts: {}.",
            named.unwrap_or_default(),
            numbered(&accounts)
        )),
        Err(error) => ProviderAuthOutcome::Error(format!("Logout failed: {error}")),
    }
}

#[cfg(test)]
mod tests {
    use eukhe_core::auth::AuthCredential;
    use eukhe_core::platform::LocalTime;

    use super::*;

    /// An agent dir holding three fake API-key accounts of `openai`.
    fn three_openai_keys() -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("temp dir");
        let mut auth = AuthStorage::create(dir.path());
        for key in ["sk-fake-111111", "sk-fake-222222", "sk-fake-333333"] {
            auth.add_account(
                "openai",
                AuthCredential::ApiKey {
                    key: key.to_owned(),
                },
                "",
            )
            .expect("the fake account is stored");
        }
        dir
    }

    fn identities(agent_dir: &Path) -> Vec<String> {
        AuthStorage::create(agent_dir)
            .get_all()
            .accounts("openai")
            .into_iter()
            .map(|account| account.identity)
            .collect()
    }

    /// A place removes that account only; the others keep their order. No
    /// account named among several, and a name no account has, list them.
    #[test]
    fn logout_with_a_place_removes_only_that_account() {
        let dir = three_openai_keys();
        let unnamed = logout(dir.path(), "openai", None);
        let removed = logout(dir.path(), "openai", Some("2"));
        let missing = logout(dir.path(), "openai", Some("9"));
        assert_eq!(
            (unnamed, removed, missing, identities(dir.path())),
            (
                ProviderAuthOutcome::Error(
                    "openai has 3 accounts: 1. key ...111111, 2. key ...222222, \
                     3. key ...333333. Name one by its number or identity."
                        .to_owned()
                ),
                ProviderAuthOutcome::Status(
                    "Removed key ...222222 from openai (2 left).".to_owned()
                ),
                ProviderAuthOutcome::Error(
                    "openai has no account 9. Its accounts: 1. key ...111111, \
                     2. key ...333333."
                        .to_owned()
                ),
                vec!["key ...111111".to_owned(), "key ...333333".to_owned()],
            )
        );
    }

    /// Sat 2026-07-25 17:20:00 UTC.
    const NOW: u64 = 1_785_000_000_000;
    const HOUR: u64 = 3_600_000;

    /// The test zone: UTC, every instant read as 18:20.
    const AT: LocalTime = LocalTime {
        year: 2026,
        month: 7,
        day: 25,
        hour: 18,
        minute: 20,
        second: 0,
        millisecond: 0,
        offset_seconds: 0,
    };

    /// The rows carry each label and a limit only while it lasts; the JSON
    /// keeps the stored reset.
    #[test]
    fn the_listing_shows_a_lasting_limit() {
        let key = |key: &str, limited_until_ms: Option<u64>| Account {
            identity: format!("key ...{key}"),
            limited_until_ms,
            credential: serde_json::Map::new(),
        };
        let stored = vec![(
            "openai".to_owned(),
            vec![
                key("111111", Some(NOW - HOUR)),
                key("222222", Some(NOW + HOUR)),
            ],
        )];
        assert_eq!(
            (listing(&stored, NOW, &|_| Some(AT)), listing_json(&stored)),
            (
                vec![ProviderAccounts {
                    provider: "openai".to_owned(),
                    accounts: vec![
                        AccountRow {
                            identity: "key ...111111".to_owned(),
                            label: "key ...111111".to_owned(),
                            limited_until: None,
                        },
                        AccountRow {
                            identity: "key ...222222".to_owned(),
                            label: "key ...222222".to_owned(),
                            limited_until: Some("18:20".to_owned()),
                        },
                    ],
                }],
                json!({ "providers": [ { "provider": "openai", "accounts": [
                    { "place": 1, "identity": "key ...111111", "limitedUntilMs": NOW - HOUR },
                    { "place": 2, "identity": "key ...222222", "limitedUntilMs": NOW + HOUR },
                ] } ] }),
            )
        );
    }
}
