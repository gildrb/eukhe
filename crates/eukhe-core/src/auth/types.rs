//! Auth credential types (auth-storage.ts).

use serde::{Deserialize, Serialize};

use super::provider_oauth::ANTHROPIC_PROVIDER_ID;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum AuthCredential {
    #[serde(rename = "api_key")]
    ApiKey { key: String },
    /// A pasted MCP static token (the inline paste flow for
    /// `requires-setup` token services): the literal bearer value plus the
    /// endpoint it is bound to. No expiry — usable until removed or replaced.
    /// Setup field ids are metadata, never environment variables to read.
    #[serde(rename = "mcp_static_token")]
    McpStaticToken {
        bearer: String,
        #[serde(rename = "endpoint", default, skip_serializing_if = "Option::is_none")]
        endpoint: Option<String>,
    },
    #[serde(rename = "oauth")]
    Oauth {
        access: String,
        refresh: Option<String>,
        expires: i64,
        /// The `ChatGPT` account the Codex Subscription token carries
        /// (TS stores the codex login's `accountId` next to the
        /// credentials; the request path re-extracts it from the token,
        /// like TS).
        #[serde(rename = "accountId", default, skip_serializing_if = "Option::is_none")]
        account_id: Option<String>,
        /// The GitHub Enterprise domain the Copilot login ran against (TS
        /// stores the copilot login's `enterpriseUrl` next to the
        /// credentials; the refresh and the model base URL resolve through
        /// it).
        #[serde(
            rename = "enterpriseUrl",
            default,
            skip_serializing_if = "Option::is_none"
        )]
        enterprise_url: Option<String>,
        /// Endpoint binding for MCP logins (`mcp:<server>` credentials): the
        /// MCP endpoint the token was issued for; consumers refuse to send
        /// it elsewhere.
        #[serde(rename = "endpoint", default, skip_serializing_if = "Option::is_none")]
        endpoint: Option<String>,
        /// The token endpoint the token was exchanged at (refreshes reuse it).
        #[serde(
            rename = "tokenEndpoint",
            default,
            skip_serializing_if = "Option::is_none"
        )]
        token_endpoint: Option<String>,
        /// The OAuth client the login registered/pre-configured.
        #[serde(rename = "clientId", default, skip_serializing_if = "Option::is_none")]
        client_id: Option<String>,
        /// RFC 9728 resource indicator; its presence marks a
        /// protected-resource-metadata login.
        #[serde(rename = "resource", default, skip_serializing_if = "Option::is_none")]
        resource: Option<String>,
        /// RFC 8414/OIDC issuer selected by the protected-resource metadata.
        #[serde(rename = "issuer", default, skip_serializing_if = "Option::is_none")]
        issuer: Option<String>,
    },
}

impl AuthCredential {
    #[must_use]
    pub fn credential_type(&self) -> &'static str {
        match self {
            AuthCredential::ApiKey { .. } => "api_key",
            AuthCredential::McpStaticToken { .. } => "mcp_static_token",
            AuthCredential::Oauth { .. } => "oauth",
        }
    }
}

/// auth.json document: provider id -> its accounts (`super::accounts`), or
/// an MCP server's one credential. Unknown providers (custom OAuth shapes)
/// survive round-trips.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AuthStorageData(pub serde_json::Map<String, serde_json::Value>);

impl AuthStorageData {
    #[must_use]
    pub fn get(&self, provider: &str) -> Option<&serde_json::Value> {
        self.0.get(provider)
    }

    /// The provider's credential: its first account's (a Claude
    /// subscription login skipped), or an MCP server's own.
    #[must_use]
    pub fn credential(&self, provider: &str) -> Option<AuthCredential> {
        let entry = self.0.get(provider)?;
        if !super::accounts::keeps_accounts(provider) {
            return serde_json::from_value(entry.clone()).ok();
        }
        let first = super::accounts::accounts_of(provider, entry)
            .into_iter()
            .find(|account| !is_moved_claude_login(provider, &account.credential))?;
        serde_json::from_value(serde_json::Value::Object(first.credential)).ok()
    }

    /// Whether `auth.json` holds a Claude subscription login: an
    /// `anthropic` OAuth credential, which eukhe ignores.
    #[must_use]
    pub fn has_moved_claude_login(&self) -> bool {
        self.accounts(ANTHROPIC_PROVIDER_ID)
            .iter()
            .any(|account| is_moved_claude_login(ANTHROPIC_PROVIDER_ID, &account.credential))
    }

    /// The provider's accounts, in order (none for an MCP server).
    #[must_use]
    pub fn accounts(&self, provider: &str) -> Vec<super::accounts::Account> {
        match self.0.get(provider) {
            Some(entry) if super::accounts::keeps_accounts(provider) => {
                super::accounts::accounts_of(provider, entry)
            }
            Some(_) | None => Vec::new(),
        }
    }

    /// Make `credential` the provider's one credential (its only account).
    pub fn insert(&mut self, provider: &str, credential: &AuthCredential) {
        if let Ok(serde_json::Value::Object(object)) = serde_json::to_value(credential) {
            let entry = if super::accounts::keeps_accounts(provider) {
                super::accounts::entry_of(&[super::accounts::Account::new(provider, object)])
            } else {
                serde_json::Value::Object(object)
            };
            self.0.insert(provider.to_string(), entry);
        }
    }

    pub fn remove(&mut self, provider: &str) {
        self.0.remove(provider);
    }

    #[must_use]
    pub fn keys(&self) -> Vec<String> {
        self.0.keys().cloned().collect()
    }
}

/// Whether `credential`, stored for `provider`, is a Claude subscription
/// login: an `anthropic` OAuth credential. eukhe never sends nor refreshes
/// it; the claude-code provider serves the subscription
/// (`eukhe_ai::api::anthropic_messages::CLAUDE_LOGIN_MOVED`).
pub(crate) fn is_moved_claude_login(
    provider: &str,
    credential: &serde_json::Map<String, serde_json::Value>,
) -> bool {
    provider == ANTHROPIC_PROVIDER_ID
        && credential.get("type").and_then(serde_json::Value::as_str) == Some("oauth")
}

/// Where a usable credential came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum AuthSource {
    Stored,
    Runtime,
    Environment,
    Fallback,
    ModelsJsonKey,
    ModelsJsonCommand,
    /// Marked stale; kept for a later explicit re-login.
    Stale,
}

/// Auth status without credential values.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AuthStatus {
    pub configured: bool,
    pub source: Option<AuthSource>,
    pub label: Option<String>,
}

/// A stale-marking token for one credential source value.
#[derive(Debug, Clone, PartialEq)]
pub struct AuthSourceToken {
    pub provider: String,
    pub source: AuthSource,
    pub identity_fingerprint: String,
    pub value_fingerprint: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn credential_wire_shapes() {
        let api_key: AuthCredential =
            serde_json::from_value(serde_json::json!({ "type": "api_key", "key": "sk" })).unwrap();
        assert!(matches!(api_key, AuthCredential::ApiKey { .. }));
        let oauth: AuthCredential = serde_json::from_value(
            serde_json::json!({ "type": "oauth", "access": "a", "refresh": "r", "expires": 123 }),
        )
        .unwrap();
        assert!(matches!(oauth, AuthCredential::Oauth { .. }));
        // The codex subscription login stores its `accountId` (the TS
        // auth.json shape) and the field round-trips.
        let codex: AuthCredential = serde_json::from_value(serde_json::json!({
            "type": "oauth", "access": "a", "refresh": "r", "expires": 123,
            "accountId": "acct-1"
        }))
        .unwrap();
        assert!(matches!(
            &codex,
            AuthCredential::Oauth { account_id: Some(account_id), .. } if account_id == "acct-1"
        ));
        let emitted = serde_json::to_value(&codex).unwrap();
        assert_eq!(emitted["accountId"], "acct-1");
    }

    /// An `api_key` credential with a field this build does not read (an
    /// earlier release's team selection) still loads; the field is dropped.
    #[test]
    fn an_api_key_with_an_unread_field_loads() {
        let stored: AuthCredential = serde_json::from_value(serde_json::json!({
            "type": "api_key", "key": "sk",
            "team": { "teamId": "t-1", "name": "Team" }
        }))
        .unwrap();
        assert_eq!(
            stored,
            AuthCredential::ApiKey {
                key: "sk".to_string()
            }
        );
    }

    /// A stored Claude subscription login is never the `anthropic`
    /// credential: the next account serves, and the document reports it.
    #[test]
    fn a_claude_subscription_login_is_skipped_and_reported() {
        let data = AuthStorageData(
            serde_json::from_value(serde_json::json!({
                "anthropic": { "accounts": [
                    { "type": "oauth", "access": "sk-ant-oat01-a", "refresh": "r", "expires": 1 },
                    { "type": "api_key", "key": "sk-ant-api03-k" },
                ] },
                "xai": { "type": "oauth", "access": "a", "refresh": "r", "expires": 1 },
            }))
            .unwrap(),
        );
        assert_eq!(
            (
                data.credential("anthropic"),
                data.has_moved_claude_login(),
                AuthStorageData::default().has_moved_claude_login(),
            ),
            (
                Some(AuthCredential::ApiKey {
                    key: "sk-ant-api03-k".to_string()
                }),
                true,
                false,
            )
        );
    }
}
