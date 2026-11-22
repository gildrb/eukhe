//! The identity of a subscription login: the account it signs in as, by
//! email and the organization or workspace it acts for. Two logins of one
//! provider with the same identity are the same account.

use super::decode_jwt_payload;
use crate::auth::OAuthCredential;

/// The `openai-codex` provider id.
const OPENAI_CODEX: &str = "openai-codex";
/// The access token's claim holding the `ChatGPT` workspace.
const AUTH_CLAIM: &str = "https://api.openai.com/auth";
/// The access token's claim holding the user's profile.
const PROFILE_CLAIM: &str = "https://api.openai.com/profile";
/// The extra a login flow stores the account's email in.
pub const EMAIL_EXTRA: &str = "email";
/// The extra a login flow stores the account's organization in.
pub const ORGANIZATION_EXTRA: &str = "organizationId";
/// The extra the Codex login stores its workspace in.
const ACCOUNT_ID_EXTRA: &str = "accountId";

/// The identity of `credential`, a login of `provider_id`: `email
/// [organization]`, `email`, `[organization]`, or empty when the login
/// carries neither. The Codex token names its email and workspace itself.
#[must_use]
pub fn oauth_identity(provider_id: &str, credential: &OAuthCredential) -> String {
    let extra = |key: &str| {
        credential
            .extra_str(key)
            .filter(|value| !value.is_empty())
            .map(str::to_owned)
    };
    let (email, organization) = if provider_id == OPENAI_CODEX {
        let claims = decode_jwt_payload(&credential.access);
        let claim = |path: &str, key: &str| {
            claims
                .as_ref()
                .and_then(|claims| claims.get(path)?.get(key)?.as_str().map(str::to_owned))
                .filter(|value| !value.is_empty())
        };
        (
            claim(PROFILE_CLAIM, "email").or_else(|| extra(EMAIL_EXTRA)),
            claim(AUTH_CLAIM, "chatgpt_account_id").or_else(|| extra(ACCOUNT_ID_EXTRA)),
        )
    } else {
        (
            extra(EMAIL_EXTRA),
            extra(ORGANIZATION_EXTRA).or_else(|| extra(ACCOUNT_ID_EXTRA)),
        )
    };
    match (email, organization) {
        (Some(email), Some(organization)) => format!("{email} [{organization}]"),
        (Some(email), None) => email,
        (None, Some(organization)) => format!("[{organization}]"),
        (None, None) => String::new(),
    }
}

#[cfg(test)]
mod tests {
    use base64::Engine as _;
    use serde_json::json;

    use super::*;

    fn jwt(claims: &serde_json::Value) -> String {
        let encode = |value: &serde_json::Value| {
            base64::engine::general_purpose::STANDARD_NO_PAD.encode(value.to_string())
        };
        format!("{}.{}.sig", encode(&json!({"alg": "none"})), encode(claims))
    }

    /// The Codex token names the email and the workspace; another login
    /// names them in its extras; a login with neither has no identity.
    #[test]
    fn a_login_is_named_by_its_email_and_organization() {
        let codex = OAuthCredential::new(
            "r",
            jwt(&json!({
                AUTH_CLAIM: { "chatgpt_account_id": "ws-1" },
                PROFILE_CLAIM: { "email": "a@example.com" },
            })),
            1.0,
        );
        let anthropic = OAuthCredential::new("r", "a", 1.0)
            .with_extra(EMAIL_EXTRA, json!("b@example.com"))
            .with_extra(ORGANIZATION_EXTRA, json!("org-2"));
        let email_only =
            OAuthCredential::new("r", "a", 1.0).with_extra(EMAIL_EXTRA, json!("c@example.com"));
        assert_eq!(
            [
                oauth_identity(OPENAI_CODEX, &codex),
                oauth_identity("anthropic", &anthropic),
                oauth_identity("xai", &email_only),
                oauth_identity("github-copilot", &OAuthCredential::new("r", "a", 1.0)),
            ],
            [
                "a@example.com [ws-1]".to_owned(),
                "b@example.com [org-2]".to_owned(),
                "c@example.com".to_owned(),
                String::new(),
            ]
        );
    }
}
