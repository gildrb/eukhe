//! The `claude-code` provider: Anthropic's models through the user's own
//! `claude` CLI and its sign-in.

use std::sync::Arc;

use futures::future::BoxFuture;

use super::claude_code_models::CLAUDE_CODE_MODELS;
use super::{builtin_baseline, chat_models};
use crate::api::builtin::claude_code_api;
use crate::api::claude_code::{find_claude, CLAUDE_BIN_ENV};
use crate::auth::{
    ApiKeyAuth, ApiKeyResolveInput, AuthCheck, AuthResult, AuthType, ModelAuth, ProviderAuth,
};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};
use crate::utils::diagnostics::Thrown;

/// The CLI holds the sign-in: requests carry no eukhe credential.
struct ClaudeCliAuth;

impl ApiKeyAuth for ClaudeCliAuth {
    // The trait returns a borrowed name; this one is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        "claude CLI sign-in"
    }

    /// Available where the `claude` binary is.
    fn check(
        &self,
        input: ApiKeyResolveInput,
    ) -> Option<BoxFuture<'_, Result<Option<AuthCheck>, Thrown>>> {
        Some(Box::pin(async move {
            input.signal.throw_if_aborted()?;
            let explicit = input.ctx.env(CLAUDE_BIN_ENV).await;
            let path = input.ctx.env("PATH").await;
            Ok(
                find_claude(explicit.as_deref(), path.as_deref()).map(|binary| AuthCheck {
                    source: Some(binary.display().to_string()),
                    kind: AuthType::ApiKey,
                }),
            )
        }))
    }

    /// Always resolves: a request without the CLI fails with its install
    /// hint.
    fn resolve(
        &self,
        input: ApiKeyResolveInput,
    ) -> BoxFuture<'_, Result<Option<AuthResult>, Thrown>> {
        Box::pin(async move {
            input.signal.throw_if_aborted()?;
            Ok(Some(AuthResult {
                auth: ModelAuth::default(),
                env: None,
                source: Some("claude CLI".to_owned()),
            }))
        })
    }
}

/// The `claude-code` provider.
#[must_use]
pub fn claude_code_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "claude-code".to_owned(),
        name: Some("Claude (claude CLI)".to_owned()),
        auth: ProviderAuth {
            api_key: Some(Arc::new(ClaudeCliAuth)),
            oauth: None,
        },
        models: builtin_baseline("claude-code", || chat_models(&CLAUDE_CODE_MODELS)),
        api: Some(ProviderApi::Single(claude_code_api())),
        ..CreateProviderOptions::default()
    })
}
