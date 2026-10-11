//! The built-in subscription providers' OAuth integration (TS the auth
//! storage delegates to the AI library's oauth registry): the stored
//! `openai-codex`, `anthropic`, `github-copilot`, and `xai`
//! credentials refresh through the pi-ai OAuth flows
//! ([`OAuthAuth::refresh`]) when they expire. Every other provider
//! serves its access token until expiry (no refresh flow exists for
//! it), so refresh answers that reason and resolution keeps the stored
//! credential for a later explicit re-login.
//!
//! The [`OAuthIntegration`](crate::auth::OAuthIntegration) seam is
//! synchronous by contract (it runs under the storage's file lock), so
//! the refresh runs on its own short-lived thread with a private runtime
//! — the same bridge the MCP integration uses. Refreshes are rare: token
//! expiry, once per hour at worst.
//!
//! The stored credential keeps the `auth.json` wire shape: the flows'
//! `accountId` (Codex) and `enterpriseUrl` (Copilot) extras ride the
//! credential's own fields; the flows' other extras are not stored.

use std::collections::BTreeMap;
use std::sync::Arc;

use eukhe_chord::context::AbortController;
use eukhe_pi_ai::auth::oauth::{
    anthropic_oauth, github_copilot_oauth, openai_codex_oauth, xai_oauth,
};
use eukhe_pi_ai::auth::{OAuthAuth, OAuthCredential};

use crate::auth::types::{AuthCredential, AuthStorageData};

/// The Codex Subscription provider id (the wire identifiers the TS
/// product registers; branding never renames a provider id).
pub const OPENAI_CODEX_PROVIDER_ID: &str = "openai-codex";
/// The Anthropic (Claude Pro/Max) subscription provider id.
pub const ANTHROPIC_PROVIDER_ID: &str = "anthropic";
/// The GitHub Copilot subscription provider id.
pub const GITHUB_COPILOT_PROVIDER_ID: &str = "github-copilot";
/// The xAI (Grok) subscription provider id.
pub const XAI_PROVIDER_ID: &str = "xai";

/// The credential extra naming the Codex Subscription account.
const ACCOUNT_ID_EXTRA: &str = "accountId";
/// The credential extra naming the GitHub Enterprise domain.
const ENTERPRISE_URL_EXTRA: &str = "enterpriseUrl";

/// The pi-ai flow that logs in to and refreshes one built-in subscription
/// provider; `None` for every other provider id.
#[must_use]
pub fn subscription_oauth_flow(provider_id: &str) -> Option<Arc<dyn OAuthAuth>> {
    match provider_id {
        OPENAI_CODEX_PROVIDER_ID => Some(openai_codex_oauth()),
        ANTHROPIC_PROVIDER_ID => Some(anthropic_oauth()),
        GITHUB_COPILOT_PROVIDER_ID => Some(github_copilot_oauth()),
        XAI_PROVIDER_ID => Some(xai_oauth()),
        _ => None,
    }
}

/// The stored shape of a flow's credential: the access and refresh
/// tokens, the expiry (epoch milliseconds), and the `accountId` /
/// `enterpriseUrl` extras.
#[must_use]
pub fn stored_oauth_credential(credential: &OAuthCredential) -> AuthCredential {
    let extra = |key: &str| {
        credential
            .extra_str(key)
            .filter(|value| !value.is_empty())
            .map(str::to_string)
    };
    AuthCredential::Oauth {
        access: credential.access.clone(),
        refresh: Some(credential.refresh.clone()),
        expires: epoch_millis(credential.expires),
        account_id: extra(ACCOUNT_ID_EXTRA),
        enterprise_url: extra(ENTERPRISE_URL_EXTRA),
        endpoint: None,
        token_endpoint: None,
        client_id: None,
        resource: None,
        issuer: None,
    }
}

/// The flow's view of a stored OAuth credential (the inverse of
/// [`stored_oauth_credential`]); `None` without a refresh token.
fn flow_credential(credential: &AuthCredential) -> Option<OAuthCredential> {
    let AuthCredential::Oauth {
        access,
        refresh: Some(refresh),
        expires,
        account_id,
        enterprise_url,
        ..
    } = credential
    else {
        return None;
    };
    let mut flow = OAuthCredential::new(refresh.clone(), access.clone(), js_millis(*expires));
    for (key, value) in [
        (ACCOUNT_ID_EXTRA, account_id),
        (ENTERPRISE_URL_EXTRA, enterprise_url),
    ] {
        if let Some(value) = value {
            flow = flow.with_extra(key, serde_json::Value::String(value.clone()));
        }
    }
    Some(flow)
}

/// A JS epoch-milliseconds number as the stored integer expiry.
#[allow(
    clippy::cast_possible_truncation,
    reason = "epoch milliseconds stay far inside the i64 range; the JS number's fraction is dropped"
)]
fn epoch_millis(expires: f64) -> i64 {
    expires as i64
}

/// The stored integer expiry as a JS epoch-milliseconds number.
#[allow(
    clippy::cast_precision_loss,
    reason = "epoch milliseconds stay below 2^53, where f64 is exact"
)]
fn js_millis(expires: i64) -> f64 {
    expires as f64
}

/// The AI library's oauth registry as the auth storage's default
/// integration.
pub struct ProviderOAuth {
    flows: BTreeMap<String, Arc<dyn OAuthAuth>>,
}

impl Default for ProviderOAuth {
    fn default() -> Self {
        Self::new()
    }
}

impl ProviderOAuth {
    /// The built-in subscription flows.
    #[must_use]
    pub fn new() -> Self {
        Self::with_flows(
            [
                OPENAI_CODEX_PROVIDER_ID,
                ANTHROPIC_PROVIDER_ID,
                GITHUB_COPILOT_PROVIDER_ID,
                XAI_PROVIDER_ID,
            ]
            .into_iter()
            .filter_map(|id| Some((id.to_string(), subscription_oauth_flow(id)?))),
        )
    }

    /// Fixed flows per provider id (tests and embedded hosts); a provider
    /// without a flow has no token refresh.
    pub fn with_flows(flows: impl IntoIterator<Item = (String, Arc<dyn OAuthAuth>)>) -> Self {
        ProviderOAuth {
            flows: flows.into_iter().collect(),
        }
    }

    /// Refresh one expired credential off the async runtime (the
    /// `AuthStorage` seam is synchronous by contract). Each
    /// subscription provider's refresh resolves through its own flow;
    /// a failure answers the flow's own error.
    fn refresh_blocking(
        flow: Arc<dyn OAuthAuth>,
        provider_id: &str,
        credential: &AuthCredential,
    ) -> Result<AuthCredential, String> {
        let credential = flow_credential(credential)
            .ok_or_else(|| format!("the stored {provider_id} credential has no refresh token"))?;
        std::thread::Builder::new()
            .name("provider-oauth-refresh".to_string())
            .spawn(move || {
                let runtime = tokio::runtime::Builder::new_current_thread()
                    .enable_all()
                    .build()
                    .map_err(|error| format!("could not start the refresh runtime: {error}"))?;
                let signal = AbortController::new().signal();
                runtime
                    .block_on(flow.refresh(credential, signal))
                    .map(|refreshed| stored_oauth_credential(&refreshed))
                    .map_err(|error| error.to_string())
            })
            .map_err(|error| format!("could not start the refresh thread: {error}"))?
            .join()
            .map_err(|_| "the refresh thread panicked".to_string())?
    }
}

impl crate::auth::OAuthIntegration for ProviderOAuth {
    fn api_key_for(&self, _provider: &str, credential: &AuthCredential) -> Option<String> {
        match credential {
            AuthCredential::Oauth { access, .. } => Some(access.clone()),
            AuthCredential::ApiKey { .. } | AuthCredential::McpStaticToken { .. } => None,
        }
    }

    fn refresh(
        &self,
        provider_id: &str,
        credentials: &AuthStorageData,
    ) -> Result<AuthCredential, String> {
        let flow = self
            .flows
            .get(provider_id)
            .ok_or_else(|| format!("{provider_id} has no token refresh flow"))?;
        let credential = credentials
            .credential(provider_id)
            .ok_or_else(|| format!("no stored credential for {provider_id}"))?;
        Self::refresh_blocking(Arc::clone(flow), provider_id, &credential)
    }
}

#[cfg(test)]
mod tests {
    use eukhe_chord::context::AbortSignal;
    use eukhe_pi_ai::auth::{LoginOptions, ModelAuth, ProviderAuthInteraction};
    use eukhe_pi_ai::utils::diagnostics::Thrown;
    use futures::future::BoxFuture;

    use super::*;

    /// A scripted refresh: the refreshed credential the flow answers
    /// (keeping the stored refresh token when the script has none, like
    /// the Copilot flow), or the flow's failure.
    struct ScriptedRefresh(Result<OAuthCredential, String>);

    impl OAuthAuth for ScriptedRefresh {
        fn name(&self) -> &'static str {
            "scripted"
        }

        fn login(
            &self,
            _interaction: ProviderAuthInteraction,
            _options: Option<LoginOptions>,
        ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
            Box::pin(async { Err(thrown("login is not scripted".to_string())) })
        }

        fn refresh(
            &self,
            credential: OAuthCredential,
            _signal: AbortSignal,
        ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
            let answer = self.0.clone().map(|mut refreshed| {
                if refreshed.refresh.is_empty() {
                    refreshed.refresh = credential.refresh;
                }
                for (key, value) in credential.extra {
                    refreshed.extra.entry(key).or_insert(value);
                }
                refreshed
            });
            Box::pin(async move { answer.map_err(thrown) })
        }

        fn to_auth<'a>(
            &'a self,
            credential: &'a OAuthCredential,
        ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
            Box::pin(async move {
                Ok(ModelAuth {
                    api_key: Some(credential.access.clone()),
                    headers: None,
                    base_url: None,
                })
            })
        }
    }

    fn thrown(message: String) -> Thrown {
        Arc::new(std::io::Error::other(message))
    }

    fn expired_codex_credential() -> AuthCredential {
        AuthCredential::Oauth {
            access: "stale-access".to_string(),
            refresh: Some("r-old".to_string()),
            expires: 1,
            account_id: Some("acct-1".to_string()),
            enterprise_url: None,
            endpoint: None,
            token_endpoint: None,
            client_id: None,
            resource: None,
            issuer: None,
        }
    }

    /// One expired subscription credential for a provider id.
    fn expired_credential(provider_id: &str) -> AuthCredential {
        match provider_id {
            GITHUB_COPILOT_PROVIDER_ID => AuthCredential::Oauth {
                access: "stale-copilot".to_string(),
                refresh: Some("gh-old".to_string()),
                expires: 1,
                account_id: None,
                enterprise_url: Some("company.ghe.com".to_string()),
                endpoint: None,
                token_endpoint: None,
                client_id: None,
                resource: None,
                issuer: None,
            },
            _ => AuthCredential::Oauth {
                access: "stale-access".to_string(),
                refresh: Some("r-old".to_string()),
                expires: 1,
                account_id: None,
                enterprise_url: None,
                endpoint: None,
                token_endpoint: None,
                client_id: None,
                resource: None,
                issuer: None,
            },
        }
    }

    /// The scripted refreshes of the four subscription flows.
    fn integrations() -> Arc<ProviderOAuth> {
        let in_an_hour = 4_000_000_000_000.0;
        let flow = |credential: OAuthCredential| -> Arc<dyn OAuthAuth> {
            Arc::new(ScriptedRefresh(Ok(credential)))
        };
        Arc::new(ProviderOAuth::with_flows([
            (
                OPENAI_CODEX_PROVIDER_ID.to_string(),
                flow(
                    OAuthCredential::new("r-new", "codex-access", in_an_hour).with_extra(
                        ACCOUNT_ID_EXTRA,
                        serde_json::Value::String("acct-2".to_string()),
                    ),
                ),
            ),
            (
                ANTHROPIC_PROVIDER_ID.to_string(),
                flow(OAuthCredential::new(
                    "anthropic-refresh",
                    "anthropic-access",
                    in_an_hour,
                )),
            ),
            (
                GITHUB_COPILOT_PROVIDER_ID.to_string(),
                flow(OAuthCredential::new("", "copilot-access", in_an_hour)),
            ),
            (
                XAI_PROVIDER_ID.to_string(),
                flow(OAuthCredential::new(
                    "grok-refresh",
                    "grok-access",
                    in_an_hour,
                )),
            ),
        ]))
    }

    fn storage_with_credential(
        provider_id: &str,
        credential: &AuthCredential,
    ) -> crate::auth::AuthStorage {
        let mut data = crate::auth::types::AuthStorageData::default();
        data.insert(provider_id, credential);
        crate::auth::AuthStorage::in_memory_without_env(&data, integrations())
    }

    #[test]
    fn the_builtin_integration_maps_the_four_subscription_flows() {
        let builtin = ProviderOAuth::new();
        let ids: Vec<&str> = builtin.flows.keys().map(String::as_str).collect();
        assert_eq!(
            ids,
            vec![
                ANTHROPIC_PROVIDER_ID,
                GITHUB_COPILOT_PROVIDER_ID,
                OPENAI_CODEX_PROVIDER_ID,
                XAI_PROVIDER_ID
            ]
        );
        assert!(subscription_oauth_flow("other-oauth").is_none());
    }

    #[test]
    fn the_stored_shape_round_trips_the_flow_extras() {
        let flow = OAuthCredential::new("r", "a", 1_700_000_000_123.0)
            .with_extra(
                ACCOUNT_ID_EXTRA,
                serde_json::Value::String("acct".to_string()),
            )
            .with_extra(
                ENTERPRISE_URL_EXTRA,
                serde_json::Value::String("company.ghe.com".to_string()),
            )
            .with_extra("availableModelIds", serde_json::json!(["m"]));
        let stored = stored_oauth_credential(&flow);
        assert_eq!(
            stored,
            AuthCredential::Oauth {
                access: "a".to_string(),
                refresh: Some("r".to_string()),
                expires: 1_700_000_000_123,
                account_id: Some("acct".to_string()),
                enterprise_url: Some("company.ghe.com".to_string()),
                endpoint: None,
                token_endpoint: None,
                client_id: None,
                resource: None,
                issuer: None,
            }
        );
        let back = flow_credential(&stored).expect("a refreshable credential");
        assert_eq!(back.refresh, "r");
        assert_eq!(back.access, "a");
        assert_eq!(back.expires, 1_700_000_000_123.0);
        assert_eq!(back.extra_str(ACCOUNT_ID_EXTRA), Some("acct"));
        assert_eq!(
            back.extra_str(ENTERPRISE_URL_EXTRA),
            Some("company.ghe.com")
        );
    }

    #[test]
    fn an_expired_codex_credential_refreshes_and_resolves() {
        let mut auth =
            storage_with_credential(OPENAI_CODEX_PROVIDER_ID, &expired_codex_credential());
        let api_key = auth
            .get_api_key(OPENAI_CODEX_PROVIDER_ID)
            .expect("the refreshed access token resolves");
        assert_eq!(api_key, "codex-access");
        // The refreshed credential persisted: the account id rode along
        // (TS stores the fresh login's `accountId`).
        let stored = auth.get_all().credential(OPENAI_CODEX_PROVIDER_ID).unwrap();
        let AuthCredential::Oauth {
            access,
            refresh,
            expires,
            account_id,
            ..
        } = stored
        else {
            panic!("the stored credential is OAuth");
        };
        assert_eq!(access, "codex-access");
        assert_eq!(refresh.as_deref(), Some("r-new"));
        assert!(expires > 1, "the fresh expiry landed");
        assert_eq!(account_id.as_deref(), Some("acct-2"));
    }

    #[test]
    fn an_expired_anthropic_credential_refreshes_and_resolves() {
        let mut auth = storage_with_credential(
            ANTHROPIC_PROVIDER_ID,
            &expired_credential(ANTHROPIC_PROVIDER_ID),
        );
        let api_key = auth
            .get_api_key(ANTHROPIC_PROVIDER_ID)
            .expect("the refreshed access token resolves");
        assert_eq!(api_key, "anthropic-access");
        let stored = auth.get_all().credential(ANTHROPIC_PROVIDER_ID).unwrap();
        let AuthCredential::Oauth {
            refresh, expires, ..
        } = stored
        else {
            panic!("the stored credential is OAuth");
        };
        assert_eq!(refresh.as_deref(), Some("anthropic-refresh"));
        assert!(expires > 1, "the fresh expiry landed");
    }

    #[test]
    fn an_expired_copilot_credential_refreshes_through_the_enterprise_domain() {
        let mut auth = storage_with_credential(
            GITHUB_COPILOT_PROVIDER_ID,
            &expired_credential(GITHUB_COPILOT_PROVIDER_ID),
        );
        let api_key = auth
            .get_api_key(GITHUB_COPILOT_PROVIDER_ID)
            .expect("the refreshed Copilot token resolves");
        assert_eq!(api_key, "copilot-access");
        let stored = auth
            .get_all()
            .credential(GITHUB_COPILOT_PROVIDER_ID)
            .unwrap();
        let AuthCredential::Oauth {
            refresh,
            expires,
            enterprise_url,
            ..
        } = stored
        else {
            panic!("the stored credential is OAuth");
        };
        // The GitHub token stays the refresh source and the enterprise
        // domain rides the credential (TS `enterpriseUrl`).
        assert_eq!(refresh.as_deref(), Some("gh-old"));
        assert_eq!(enterprise_url.as_deref(), Some("company.ghe.com"));
        assert!(expires > 1, "the fresh expiry landed");
    }

    #[test]
    fn an_expired_xai_credential_refreshes_and_resolves() {
        let mut auth =
            storage_with_credential(XAI_PROVIDER_ID, &expired_credential(XAI_PROVIDER_ID));
        let api_key = auth
            .get_api_key(XAI_PROVIDER_ID)
            .expect("the refreshed access token resolves");
        assert_eq!(api_key, "grok-access");
        let stored = auth.get_all().credential(XAI_PROVIDER_ID).unwrap();
        let AuthCredential::Oauth {
            refresh, expires, ..
        } = stored
        else {
            panic!("the stored credential is OAuth");
        };
        assert_eq!(refresh.as_deref(), Some("grok-refresh"));
        assert!(expires > 1, "the fresh expiry landed");
    }

    #[test]
    fn a_failed_refresh_keeps_the_stored_credential() {
        // The flow fails: resolution skips the provider, keeping the
        // stored credential for a later retry.
        let mut auth = crate::auth::AuthStorage::in_memory_without_env(
            &{
                let mut data = crate::auth::types::AuthStorageData::default();
                data.insert(OPENAI_CODEX_PROVIDER_ID, &expired_codex_credential());
                data
            },
            Arc::new(ProviderOAuth::with_flows([(
                OPENAI_CODEX_PROVIDER_ID.to_string(),
                Arc::new(ScriptedRefresh(Err("token endpoint down".to_string())))
                    as Arc<dyn OAuthAuth>,
            )])),
        );
        assert_eq!(auth.get_api_key(OPENAI_CODEX_PROVIDER_ID), None);
        assert!(
            auth.get_all()
                .credential(OPENAI_CODEX_PROVIDER_ID)
                .is_some(),
            "the failed refresh keeps the stored credential"
        );
    }

    #[test]
    fn non_subscription_providers_do_not_refresh() {
        // A stored OAuth credential for a provider outside the four
        // subscription ids never refreshes: resolution stays absent and
        // the credential stays.
        let mut auth = storage_with_credential("other-oauth", &expired_credential("other-oauth"));
        assert_eq!(auth.get_api_key("other-oauth"), None);
        assert!(auth.get_all().credential("other-oauth").is_some());
    }

    #[test]
    fn an_unexpired_credential_serves_without_a_refresh() {
        // A credential in its validity window resolves its access token
        // directly; no refresh runs.
        let unexpired = AuthCredential::Oauth {
            access: "live-access".to_string(),
            refresh: Some("r".to_string()),
            expires: i64::MAX,
            account_id: Some("acct-1".to_string()),
            enterprise_url: None,
            endpoint: None,
            token_endpoint: None,
            client_id: None,
            resource: None,
            issuer: None,
        };
        let mut auth = storage_with_credential(OPENAI_CODEX_PROVIDER_ID, &unexpired);
        assert_eq!(
            auth.get_api_key(OPENAI_CODEX_PROVIDER_ID),
            Some("live-access".to_string())
        );
    }
}
