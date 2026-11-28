//! The accounts of a session's providers: every provider login stored in
//! `auth.json` is an account (`crate::auth::accounts`). A session sticks to
//! one account per provider ([`AccountBook::pin`]): the session's
//! credential store ([`super::stores`]) serves that account's credential
//! to every request of the provider. When the account hits a usage or rate
//! limit, or its login cannot refresh, the provider runtime
//! ([`super::provider`]) asks for the account the request goes on with
//! ([`AccountBook::step`]: `bend/account.bend`,
//! `eukhe_bend::rules::account`; laws `laws/account.bend`), before any
//! other model. A limit is stored on its account (`limitedUntil`), so every
//! session and `/accounts` see it.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_bend::rules::account::{self as rules, Choice, Mark};
use eukhe_bend::rules::config;
use eukhe_bend::{expect_core, Entry};
use eukhe_types::pi_ai::AssistantMessage;
use serde_json::{Map, Value};

use super::park::{is_quota_block_failure, quota_failure_reset_ms};
use crate::durable::rlm::now_millis;

use crate::auth::accounts::{accounts_of, entry_of, keeps_accounts, with_limit, Account};
use crate::auth::{
    edit_storage_data, parse_storage_data, AuthStorageBackend, FileAuthStorageBackend,
};

/// What a request does after its account failed.
#[derive(Debug, Clone, PartialEq)]
pub enum AccountStep {
    /// It goes on now with this account.
    Use(Account),
    /// It waits until `until_ms`, then goes on with this account.
    Hold { account: Account, until_ms: u64 },
    /// Every account is limited past the wait; the earliest resets at
    /// `until_ms`: the model fallback's usage limit.
    Quota { until_ms: u64 },
    /// No account can sign in: the model fallback's login failure.
    Login,
}

/// Why an account failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccountFailure {
    /// Its usage or rate limit holds until `until_ms` (epoch ms).
    Limit { until_ms: u64 },
    /// Its login cannot refresh.
    Login,
}

impl AccountFailure {
    /// Why the failed `message` stops the request's account: a login whose
    /// refresh failed, or a usage or rate limit until the provider's reset
    /// (else for the run's wait limit, `wait_cap_ms`); `None` for any other
    /// failure.
    pub(super) fn of(message: &AssistantMessage, wait_cap_ms: u64) -> Option<Self> {
        let login = message.diagnostics.iter().flatten().any(|diagnostic| {
            diagnostic.kind.as_str() == super::provider::LOGIN_EXPIRED_DIAGNOSTIC
        }) || message
            .error_message
            .as_deref()
            .is_some_and(|error| error.contains(crate::models::registry::LOGIN_EXPIRED_REPORT));
        if login {
            return Some(Self::Login);
        }
        is_quota_block_failure(message).then(|| Self::Limit {
            until_ms: now_millis()
                .saturating_add(quota_failure_reset_ms(message).unwrap_or(wait_cap_ms)),
        })
    }
}

/// The accounts of one session's providers: the `auth.json` document, the
/// account each provider sticks to, and the logins this session found dead.
pub struct AccountBook {
    backend: Arc<FileAuthStorageBackend>,
    /// The identity of the account each provider's requests use.
    pins: Mutex<HashMap<String, String>>,
    /// The accounts (provider, identity) whose login could not refresh.
    dead: Mutex<HashSet<(String, String)>>,
}

impl AccountBook {
    #[must_use]
    pub fn new(auth_path: impl Into<std::path::PathBuf>) -> Self {
        Self {
            backend: Arc::new(FileAuthStorageBackend::new(auth_path)),
            pins: Mutex::new(HashMap::new()),
            dead: Mutex::new(HashSet::new()),
        }
    }

    pub(super) fn backend(&self) -> &Arc<FileAuthStorageBackend> {
        &self.backend
    }

    /// The provider's accounts as stored now, in order; none when the
    /// document does not read.
    #[must_use]
    pub fn accounts(&self, provider: &str) -> Vec<Account> {
        if !keeps_accounts(provider) {
            return Vec::new();
        }
        self.backend
            .read()
            .ok()
            .and_then(|content| parse_storage_data(content.as_deref()).ok())
            .and_then(|document| {
                document
                    .0
                    .get(provider)
                    .map(|entry| accounts_of(provider, entry))
            })
            .unwrap_or_default()
    }

    /// The identity of the account the provider's requests use, if the
    /// session chose one.
    #[must_use]
    pub fn pinned(&self, provider: &str) -> Option<String> {
        self.pins
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(provider)
            .cloned()
    }

    /// The provider's requests use the account `identity` from now on.
    pub fn pin(&self, provider: &str, identity: &str) {
        self.pins
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(provider.to_owned(), identity.to_owned());
    }

    /// Every provider's pinned account identity, by provider.
    #[must_use]
    pub fn pins(&self) -> std::collections::BTreeMap<String, String> {
        self.pins
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .iter()
            .map(|(provider, identity)| (provider.clone(), identity.clone()))
            .collect()
    }

    /// The pinned account of `accounts`, else the first.
    #[must_use]
    pub fn current(&self, provider: &str, accounts: &[Account]) -> Option<Account> {
        let pinned = self.pinned(provider);
        accounts
            .iter()
            .find(|account| Some(&account.identity) == pinned.as_ref())
            .or_else(|| accounts.first())
            .cloned()
    }

    /// The identity of the account of `accounts` (the provider's) its
    /// requests use now: the one its credential store serves
    /// ([`read_credential`]); empty for a provider with no stored account.
    pub(super) fn current_identity(&self, provider: &str, accounts: &[Account]) -> String {
        self.current(provider, accounts)
            .map(|account| account.identity)
            .unwrap_or_default()
    }

    /// Whether this session found the login of the provider's account
    /// `identity` dead.
    pub(super) fn is_dead(&self, provider: &str, identity: &str) -> bool {
        self.dead
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .contains(&(provider.to_owned(), identity.to_owned()))
    }

    /// A new login of the provider's account `identity`: its login is
    /// usable again.
    pub(super) fn revive(&self, provider: &str, identity: &str) {
        self.dead
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .remove(&(provider.to_owned(), identity.to_owned()));
    }

    /// The first send of the session to a provider with several accounts:
    /// it sticks to the account the core picks (the first usable one, else
    /// the earliest to reset). One account, or a session that already
    /// chose, keeps its account.
    pub fn stick(&self, provider: &str, accounts: &[Account], now_ms: u64) {
        if accounts.len() < 2 || self.pinned(provider).is_some() {
            return;
        }
        match self.choose(provider, accounts, now_ms, 0, 0) {
            Choice::Use(at) | Choice::Quota { at, .. } | Choice::Hold { at, .. } => {
                if let Some(account) = place(accounts, at) {
                    self.pin(provider, &account.identity);
                }
            }
            Choice::Login => {}
        }
    }

    /// The account the provider's request goes on with after its account
    /// failed (`laws/account.bend`): the failure is marked on the account
    /// (a limit stored in `auth.json`, a dead login for this session), then
    /// the core chooses with the run's wait limit `cap_ms` and the `waits`
    /// the request has left. `None` for a provider with fewer than two
    /// accounts: nothing to switch to.
    pub fn step(
        &self,
        provider: &str,
        failure: AccountFailure,
        now_ms: u64,
        cap_ms: u64,
        waits: u64,
    ) -> Option<AccountStep> {
        let accounts = self.accounts(provider);
        if accounts.len() < 2 {
            return None;
        }
        let failed = self.current(provider, &accounts)?;
        let accounts = match failure {
            AccountFailure::Limit { until_ms } => {
                self.store_limit(provider, &failed.identity, until_ms);
                with_limit(accounts, &failed.identity, until_ms)
            }
            AccountFailure::Login => {
                self.dead
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .insert((provider.to_owned(), failed.identity));
                accounts
            }
        };
        let step = match self.choose(provider, &accounts, now_ms, cap_ms, waits) {
            Choice::Use(at) => AccountStep::Use(place(&accounts, at)?),
            Choice::Hold { at, until_ms } => AccountStep::Hold {
                account: place(&accounts, at)?,
                until_ms,
            },
            Choice::Quota { at, until_ms } => {
                // The session sticks to the account that resets first.
                self.pin(provider, &place(&accounts, at)?.identity);
                AccountStep::Quota { until_ms }
            }
            Choice::Login => AccountStep::Login,
        };
        Some(step)
    }

    /// The core's choice over the accounts' marks.
    fn choose(
        &self,
        provider: &str,
        accounts: &[Account],
        now_ms: u64,
        cap_ms: u64,
        waits: u64,
    ) -> Choice {
        let dead = self.dead.lock().unwrap_or_else(PoisonError::into_inner);
        let marks: Vec<Mark> = accounts
            .iter()
            .map(|account| {
                if dead.contains(&(provider.to_owned(), account.identity.clone())) {
                    Mark::Dead
                } else {
                    account
                        .limited_until_ms
                        .map_or(Mark::Free, |until_ms| Mark::Until { until_ms })
                }
            })
            .collect();
        drop(dead);
        expect_core(Entry::Account, rules::choose(now_ms, cap_ms, waits, &marks))
    }

    /// Store the limit on the account (a failed write leaves it to this
    /// session's choice: the marks the core saw already hold it).
    fn store_limit(&self, provider: &str, identity: &str, until_ms: u64) {
        let written = self.backend.with_lock(&mut |current| {
            let data = edit_storage_data(current.as_deref(), |document| {
                let entry = document.0.get(provider)?;
                let accounts = with_limit(accounts_of(provider, entry), identity, until_ms);
                Some(config::Edit::Set(provider.to_owned(), entry_of(&accounts)))
            })?;
            let content = data
                .map(|data| serde_json::to_string_pretty(&data.0))
                .transpose()?;
            Ok(((), content))
        });
        if let Err(error) = written {
            tracing::warn!(%error, provider, "the account's usage limit was not stored");
        }
    }
}

/// The account at the core's place.
fn place(accounts: &[Account], at: u64) -> Option<Account> {
    usize::try_from(at)
        .ok()
        .and_then(|at| accounts.get(at))
        .cloned()
}

/// The credential object of the account a session's request reads: the
/// account the session sticks to (picked at its first read,
/// [`AccountBook::stick`]), else the entry's first; an MCP entry is its
/// own credential.
pub(super) fn read_credential(
    book: &AccountBook,
    provider: &str,
    entry: &Value,
) -> Option<(String, Map<String, Value>)> {
    if !keeps_accounts(provider) {
        return entry
            .as_object()
            .map(|object| (String::new(), object.clone()));
    }
    let accounts = accounts_of(provider, entry);
    book.stick(provider, &accounts, crate::durable::rlm::now_millis());
    book.current(provider, &accounts)
        .map(|account| (account.identity, account.credential))
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn book_with(document: &Value) -> (tempfile::TempDir, AccountBook) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("auth.json");
        std::fs::write(&path, document.to_string()).unwrap();
        (dir, AccountBook::new(path))
    }

    fn two_keys() -> Value {
        json!({ "p": { "accounts": [
            { "type": "api_key", "key": "sk-aaaa-111111", "identity": "key ...111111" },
            { "type": "api_key", "key": "sk-bbbb-222222", "identity": "key ...222222" },
        ] } })
    }

    /// A step as text: the account it names by identity.
    fn named(step: Option<AccountStep>) -> String {
        match step {
            Some(AccountStep::Use(account)) => format!("use {}", account.identity),
            Some(AccountStep::Hold { account, until_ms }) => {
                format!("hold {} {until_ms}", account.identity)
            }
            Some(AccountStep::Quota { until_ms }) => format!("quota {until_ms}"),
            Some(AccountStep::Login) => "login".to_owned(),
            None => "none".to_owned(),
        }
    }

    /// A session sticks to the account it first picked; a limit on it
    /// moves the session's request to its sibling, and the limit is stored
    /// for every session.
    #[test]
    fn a_session_keeps_its_account_until_it_fails() {
        let (dir, book) = book_with(&two_keys());
        book.stick("p", &book.accounts("p"), 10);
        let first = book.pinned("p");
        book.pin("p", "key ...222222");
        book.stick("p", &book.accounts("p"), 10);
        let kept = book.pinned("p");
        let step = named(book.step("p", AccountFailure::Limit { until_ms: 500 }, 10, 25, 1));
        let stored: Value =
            serde_json::from_str(&std::fs::read_to_string(dir.path().join("auth.json")).unwrap())
                .unwrap();
        assert_eq!(
            (
                first,
                kept,
                step,
                stored["p"]["accounts"][1]["limitedUntil"].clone()
            ),
            (
                Some("key ...111111".to_owned()),
                Some("key ...222222".to_owned()),
                "use key ...111111".to_owned(),
                json!(500)
            )
        );
    }

    /// Every account limited: a reset within the wait holds for it; past
    /// the wait the request goes to the model fallback with the earliest
    /// reset (and the session sticks to that account); dead logins leave
    /// none; one account switches nothing.
    #[test]
    fn every_account_failing_waits_or_hands_on() {
        let (_dir, book) = book_with(&two_keys());
        book.pin("p", "key ...111111");
        let first = named(book.step("p", AccountFailure::Limit { until_ms: 30 }, 10, 25, 1));
        book.pin("p", "key ...222222");
        let held = named(book.step("p", AccountFailure::Limit { until_ms: 40 }, 10, 25, 1));
        let handed = named(book.step("p", AccountFailure::Limit { until_ms: 40 }, 10, 5, 1));
        let stuck = book.pinned("p");
        let (_dir2, dead) = book_with(&two_keys());
        dead.pin("p", "key ...111111");
        let one_dead = named(dead.step("p", AccountFailure::Login, 10, 25, 1));
        dead.pin("p", "key ...222222");
        let both_dead = named(dead.step("p", AccountFailure::Login, 10, 25, 1));
        let (_dir3, single) = book_with(&json!({ "p": { "type": "api_key", "key": "k" } }));
        let alone = named(single.step("p", AccountFailure::Login, 10, 25, 1));
        assert_eq!(
            ([first, held, handed, one_dead, both_dead, alone], stuck),
            (
                [
                    "use key ...222222",
                    "hold key ...111111 30",
                    "quota 30",
                    "use key ...222222",
                    "login",
                    "none"
                ]
                .map(str::to_owned),
                Some("key ...111111".to_owned())
            )
        );
    }
}
