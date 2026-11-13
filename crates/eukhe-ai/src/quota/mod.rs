//! Plan quota readings of subscription logins: the windows a plan meters
//! (5 hours, 7 days, a month), how much of each the account used, and when
//! each resets.
//!
//! Readings come from what model requests already return (rate-limit
//! response headers, rate-limit stream frames) and from the plan usage
//! endpoint of the same provider, read on demand ([`fetch_plan_quota`]).
//! [`QuotaBoard`] keeps the newest reading per provider and credential for
//! the whole process. A provider with no readable quota has no reading.

mod anthropic;
mod codex;
mod copilot;
mod parse;

use std::collections::HashMap;
use std::sync::{LazyLock, Mutex, PoisonError};

pub use eukhe_types::quota::{PlanQuota, QuotaSource, QuotaWindow};
use sha2::{Digest, Sha256};
use tokio::sync::broadcast;

pub(crate) use anthropic::record_headers as record_anthropic_headers;
pub(crate) use codex::{
    record_frame as record_codex_frame, record_headers as record_codex_headers,
};

/// A credential's identity on the board: a digest of its token. The token
/// itself is never kept.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CredentialId(String);

impl CredentialId {
    /// The identity of the credential whose bearer token is `token`.
    #[must_use]
    pub fn of(token: &str) -> Self {
        let digest = Sha256::digest(token.as_bytes());
        Self(hex::encode(&digest[..8]))
    }
}

/// How a credential authenticates: a plan login or a metered API key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CredentialKind {
    OAuth,
    ApiKey,
}

/// The credential a plan usage read authenticates with.
#[derive(Debug, Clone, Copy)]
pub struct PlanCredential<'a> {
    pub kind: CredentialKind,
    /// The access token (or API key) the provider's model requests send.
    pub access: &'a str,
    /// The refresh token: the GitHub token of a Copilot login.
    pub refresh: Option<&'a str>,
    /// The `ChatGPT` account of a Codex login.
    pub account_id: Option<&'a str>,
    /// The GitHub Enterprise domain of a Copilot login.
    pub enterprise_url: Option<&'a str>,
}

/// Why a plan usage read failed (the caller knows the provider it asked).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum QuotaError {
    #[error("usage endpoint answered HTTP {status}")]
    Status { status: u16 },
    #[error("usage endpoint unreachable: {message}")]
    Transport { message: String },
    #[error("usage endpoint answered with no quota in it")]
    Unreadable,
}

struct Board {
    readings: Mutex<HashMap<(String, CredentialId), PlanQuota>>,
    updates: broadcast::Sender<PlanQuota>,
}

static BOARD: LazyLock<Board> = LazyLock::new(|| Board {
    readings: Mutex::new(HashMap::new()),
    updates: broadcast::channel(64).0,
});

/// The process-wide newest plan quota reading per provider and credential.
pub struct QuotaBoard;

impl QuotaBoard {
    /// The newest reading of `provider` across its credentials.
    #[must_use]
    pub fn latest(provider: &str) -> Option<PlanQuota> {
        Self::readings()
            .iter()
            .filter(|((name, _), _)| name == provider)
            .map(|(_, reading)| reading)
            .max_by_key(|reading| reading.read_at_ms)
            .cloned()
    }

    /// The newest reading of `provider` for one credential.
    #[must_use]
    pub fn latest_for(provider: &str, credential: &CredentialId) -> Option<PlanQuota> {
        Self::readings()
            .get(&(provider.to_owned(), credential.clone()))
            .cloned()
    }

    /// Keep `reading` as the newest of its provider and `credential`; an
    /// older reading than the one kept is dropped.
    pub fn record(credential: &CredentialId, reading: PlanQuota) {
        let key = (reading.provider.clone(), credential.clone());
        {
            let mut readings = Self::readings();
            if readings
                .get(&key)
                .is_some_and(|kept| kept.read_at_ms > reading.read_at_ms)
            {
                return;
            }
            readings.insert(key, reading.clone());
        }
        // No subscriber is no error: the reading stays on the board.
        let _ = BOARD.updates.send(reading);
    }

    /// Every reading recorded from now on.
    #[must_use]
    pub fn subscribe() -> broadcast::Receiver<PlanQuota> {
        BOARD.updates.subscribe()
    }

    /// The board's reading for `credential`, else one read from the
    /// provider's plan usage endpoint ([`fetch_plan_quota`]).
    ///
    /// # Errors
    ///
    /// The endpoint read failed.
    pub async fn latest_or_fetch(
        provider: &str,
        credential: &PlanCredential<'_>,
    ) -> Result<Option<PlanQuota>, QuotaError> {
        match Self::latest_for(provider, &CredentialId::of(credential.access)) {
            Some(reading) => Ok(Some(reading)),
            None => fetch_plan_quota(provider, credential).await,
        }
    }

    fn readings() -> std::sync::MutexGuard<'static, HashMap<(String, CredentialId), PlanQuota>> {
        BOARD
            .readings
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }
}

/// Read `provider`'s plan quota from its plan usage endpoint and record it
/// on the [`QuotaBoard`]. `None`: the provider or credential has no
/// readable plan quota (an API key, a provider without a usage endpoint).
///
/// # Errors
///
/// The endpoint was unreachable, refused the credential, or answered
/// without a quota.
pub async fn fetch_plan_quota(
    provider: &str,
    credential: &PlanCredential<'_>,
) -> Result<Option<PlanQuota>, QuotaError> {
    let reading = match provider {
        anthropic::PROVIDER => anthropic::fetch(credential).await?,
        codex::PROVIDER => codex::fetch(credential).await?,
        copilot::PROVIDER => copilot::fetch(credential).await?,
        _ => None,
    };
    if let Some(reading) = &reading {
        QuotaBoard::record(&CredentialId::of(credential.access), reading.clone());
    }
    Ok(reading)
}

#[cfg(test)]
mod tests;
