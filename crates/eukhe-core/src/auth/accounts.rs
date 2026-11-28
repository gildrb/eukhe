//! The accounts of one provider in the auth document: every login of a
//! provider is an account, named by its identity (the email and the
//! organization or workspace of a subscription login, the end of an API
//! key), kept in login order. A provider's entry is
//!
//! ```json
//! { "accounts": [ { "type": "oauth", ..., "identity": "a@x.com [org-1]",
//!                   "limitedUntil": 1700000000000 }, ... ] }
//! ```
//!
//! An entry written before accounts (one credential object) reads as one
//! account and is rewritten in this form at the next load
//! ([`migrated_entries`]). `mcp:<server>` entries keep one credential each.

use eukhe_ai::auth::oauth::oauth_identity;
use eukhe_ai::auth::OAuthCredential;
use serde_json::{Map, Value};

/// A credential's `type`: the two this file reads, or another.
#[derive(serde::Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum CredentialKind {
    Oauth,
    ApiKey,
    #[serde(other)]
    Other,
}

/// The `type` of `credential`; `None` when absent or not a string.
fn credential_kind(credential: &Map<String, Value>) -> Option<CredentialKind> {
    credential
        .get("type")
        .and_then(|kind| <CredentialKind as serde::Deserialize>::deserialize(kind).ok())
}

/// The key of a provider entry's account list.
const ACCOUNTS: &str = "accounts";
/// The key of an account's identity.
const IDENTITY: &str = "identity";
/// The key of the reset of an account's usage limit (epoch ms).
const LIMITED_UNTIL: &str = "limitedUntil";
/// The entries of MCP servers: one credential each, never accounts.
const MCP_PREFIX: &str = "mcp:";

/// One login of a provider.
#[derive(Debug, Clone, PartialEq)]
pub struct Account {
    /// Who the login signs in as; empty when the login names no one.
    pub identity: String,
    /// The reset of the usage limit the account last hit (epoch ms).
    pub limited_until_ms: Option<u64>,
    /// The credential: the stored object without the account's own keys.
    pub credential: Map<String, Value>,
}

impl Account {
    /// The account of `credential`, a login of `provider`, named by its
    /// identity ([`identity_of`]).
    #[must_use]
    pub fn new(provider: &str, credential: Map<String, Value>) -> Self {
        Self {
            identity: identity_of(provider, &credential),
            limited_until_ms: None,
            credential,
        }
    }

    /// How a list names the account: its identity, else `account <place>`
    /// (from 1).
    #[must_use]
    pub fn label(&self, place: usize) -> String {
        if self.identity.is_empty() {
            format!("account {place}")
        } else {
            self.identity.clone()
        }
    }

    fn entry(&self) -> Value {
        let mut entry = self.credential.clone();
        if !self.identity.is_empty() {
            entry.insert(IDENTITY.to_owned(), Value::String(self.identity.clone()));
        }
        if let Some(until) = self.limited_until_ms {
            entry.insert(LIMITED_UNTIL.to_owned(), Value::from(until));
        }
        Value::Object(entry)
    }
}

/// Which account of a provider: its place in the list (from 1) or its
/// identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccountSelector {
    Place(usize),
    Identity(String),
}

impl AccountSelector {
    /// A place when `text` is a number, else an identity.
    #[must_use]
    pub fn parse(text: &str) -> Self {
        match text.trim().parse::<usize>() {
            Ok(place) => Self::Place(place),
            Err(_) => Self::Identity(text.trim().to_owned()),
        }
    }

    /// The index of the account it names among `accounts`.
    #[must_use]
    pub fn index(&self, accounts: &[Account]) -> Option<usize> {
        match self {
            Self::Place(place) => place.checked_sub(1).filter(|at| *at < accounts.len()),
            Self::Identity(identity) => accounts
                .iter()
                .position(|account| account.identity == *identity),
        }
    }
}

/// The identity of a credential of `provider`: the subscription login's
/// email and organization ([`oauth_identity`]), the end of an
/// API key (`key ...<last 6>`), empty otherwise.
#[must_use]
pub fn identity_of(provider: &str, credential: &Map<String, Value>) -> String {
    match credential_kind(credential) {
        Some(CredentialKind::Oauth) => {
            <OAuthCredential as serde::Deserialize>::deserialize(credential)
                .map(|credential| oauth_identity(provider, &credential))
                .unwrap_or_default()
        }
        Some(CredentialKind::ApiKey) => credential
            .get("key")
            .and_then(Value::as_str)
            .map(key_identity)
            .unwrap_or_default(),
        Some(CredentialKind::Other) | None => String::new(),
    }
}

/// `key ...<last 6>` of an API key; a key of 11 chars or fewer is `key`.
fn key_identity(key: &str) -> String {
    let chars: Vec<char> = key.chars().collect();
    match chars.len() {
        0..=11 => "key".to_owned(),
        n => format!("key ...{}", chars[n - 6..].iter().collect::<String>()),
    }
}

/// The accounts of a provider entry, in order: the account list, or the
/// one credential an entry written before accounts holds. An entry of
/// neither shape has none.
#[must_use]
pub fn accounts_of(provider: &str, entry: &Value) -> Vec<Account> {
    let Some(object) = entry.as_object() else {
        return Vec::new();
    };
    match object.get(ACCOUNTS) {
        Some(Value::Array(accounts)) => accounts
            .iter()
            .filter_map(Value::as_object)
            .map(|account| {
                let mut credential = account.clone();
                let identity = credential.remove(IDENTITY);
                let limited = credential.remove(LIMITED_UNTIL);
                Account {
                    identity: match identity {
                        Some(Value::String(identity)) => identity,
                        Some(_) | None => identity_of(provider, &credential),
                    },
                    limited_until_ms: limited.as_ref().and_then(Value::as_u64),
                    credential,
                }
            })
            .collect(),
        None if object.contains_key("type") => vec![Account::new(provider, object.clone())],
        Some(_) | None => Vec::new(),
    }
}

/// A provider entry holding `accounts`.
#[must_use]
pub fn entry_of(accounts: &[Account]) -> Value {
    let mut entry = Map::new();
    entry.insert(
        ACCOUNTS.to_owned(),
        Value::Array(accounts.iter().map(Account::entry).collect()),
    );
    Value::Object(entry)
}

/// `accounts` with `account` added: in place of the account of the same
/// identity (a login again as the same account), else last.
#[must_use]
pub fn with_account(mut accounts: Vec<Account>, account: Account) -> Vec<Account> {
    match accounts
        .iter()
        .position(|known| known.identity == account.identity)
    {
        Some(at) => accounts[at] = account,
        None => accounts.push(account),
    }
    accounts
}

/// `accounts` with the credential of the account `identity` replaced (a
/// refresh); the account keeps its place, identity and limit. Unchanged
/// when no account has that identity.
#[must_use]
pub fn with_credential(
    mut accounts: Vec<Account>,
    identity: &str,
    credential: Map<String, Value>,
) -> Vec<Account> {
    if let Some(account) = accounts
        .iter_mut()
        .find(|account| account.identity == identity)
    {
        account.credential = credential;
    }
    accounts
}

/// `accounts` with the account `identity` limited until `until_ms`.
#[must_use]
pub fn with_limit(mut accounts: Vec<Account>, identity: &str, until_ms: u64) -> Vec<Account> {
    if let Some(account) = accounts
        .iter_mut()
        .find(|account| account.identity == identity)
    {
        account.limited_until_ms = Some(until_ms);
    }
    accounts
}

/// The entries of `document` written before accounts (one credential of
/// a provider), each rewritten as a one-account list. MCP entries stay.
#[must_use]
pub fn migrated_entries(document: &Map<String, Value>) -> Vec<(String, Value)> {
    document
        .iter()
        .filter(|(provider, _)| !provider.starts_with(MCP_PREFIX))
        .filter_map(|(provider, entry)| {
            let object = entry.as_object()?;
            match credential_kind(object) {
                Some(CredentialKind::ApiKey | CredentialKind::Oauth)
                    if !object.contains_key(ACCOUNTS) =>
                {
                    Some((provider.clone(), entry_of(&accounts_of(provider, entry))))
                }
                Some(CredentialKind::ApiKey | CredentialKind::Oauth | CredentialKind::Other)
                | None => None,
            }
        })
        .collect()
}

/// Whether `provider` keeps accounts (every provider but an MCP server).
#[must_use]
pub fn keeps_accounts(provider: &str) -> bool {
    !provider.starts_with(MCP_PREFIX)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn object(value: Value) -> Map<String, Value> {
        let Value::Object(object) = value else {
            panic!("the test value is not an object");
        };
        object
    }

    /// An entry written before accounts reads as one account and migrates
    /// to a one-account list; an MCP entry and an account list stay.
    #[test]
    fn a_single_credential_entry_is_one_account() {
        let document = object(json!({
            "openai": { "type": "api_key", "key": "sk-openai-123456" },
            "mcp:linear": { "type": "mcp_static_token", "bearer": "b" },
            "zai": { "accounts": [ { "type": "api_key", "key": "k", "identity": "key" } ] },
        }));
        assert_eq!(
            migrated_entries(&document),
            vec![(
                "openai".to_owned(),
                json!({ "accounts": [
                    { "type": "api_key", "key": "sk-openai-123456", "identity": "key ...123456" }
                ] })
            )]
        );
        assert_eq!(
            accounts_of("openai", &document["openai"]),
            vec![Account {
                identity: "key ...123456".to_owned(),
                limited_until_ms: None,
                credential: object(json!({ "type": "api_key", "key": "sk-openai-123456" })),
            }]
        );
    }

    /// A login as a known account replaces it in place; a new one comes
    /// last; a limit and a refresh touch only their account.
    #[test]
    fn a_login_adds_or_replaces_by_identity() {
        let key = |key: &str| object(json!({ "type": "api_key", "key": key }));
        let first = Account::new("p", key("sk-aaaa-111111"));
        let second = Account::new("p", key("sk-bbbb-222222"));
        let accounts = with_account(vec![first], second);
        let again = with_account(accounts.clone(), Account::new("p", key("sk-cccc-111111")));
        let limited = with_limit(again.clone(), "key ...222222", 99);
        let refreshed = with_credential(limited.clone(), "key ...111111", key("sk-dddd-111111"));
        assert_eq!(
            [
                accounts.len(),
                again.len(),
                usize::from(again[0].credential == key("sk-cccc-111111")),
                usize::from(limited[1].limited_until_ms == Some(99)),
                usize::from(refreshed[0].credential == key("sk-dddd-111111")),
            ],
            [2, 2, 1, 1, 1]
        );
        assert_eq!(
            accounts_of("p", &entry_of(&limited)),
            limited,
            "the entry round-trips"
        );
    }

    /// A place counts from 1; an identity names its account.
    #[test]
    fn a_selector_names_one_account() {
        let accounts = vec![
            Account::new(
                "p",
                object(json!({ "type": "api_key", "key": "sk-aaaa-111111" })),
            ),
            Account::new(
                "p",
                object(json!({ "type": "api_key", "key": "sk-bbbb-222222" })),
            ),
        ];
        assert_eq!(
            [
                AccountSelector::parse("2").index(&accounts),
                AccountSelector::parse("0").index(&accounts),
                AccountSelector::parse("3").index(&accounts),
                AccountSelector::parse("key ...111111").index(&accounts),
                AccountSelector::parse("nobody").index(&accounts),
            ],
            [Some(1), None, None, Some(0), None]
        );
    }
}
