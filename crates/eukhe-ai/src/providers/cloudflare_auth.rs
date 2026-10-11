//! Cloudflare api-key auth for Workers AI and AI Gateway. Port of
//! `providers/cloudflare-auth.ts`.

use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::ProviderHeaders;
use futures::future::BoxFuture;

use crate::auth::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthContext, AuthPrompt, AuthPromptKind,
    AuthResult, ModelAuth, ProviderAuthInteraction,
};
use crate::types::ProviderEnv;
use crate::utils::diagnostics::Thrown;

const CLOUDFLARE_API_KEY: &str = "CLOUDFLARE_API_KEY";
const CLOUDFLARE_ACCOUNT_ID: &str = "CLOUDFLARE_ACCOUNT_ID";
const CLOUDFLARE_GATEWAY_ID: &str = "CLOUDFLARE_GATEWAY_ID";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CloudflareAuthKind {
    WorkersAi,
    AiGateway,
}

/// Per-field merge: prefer the credential value, fall back to ambient env. A
/// credential carrying only the API key must still pick up the account /
/// gateway id from the environment.
async fn resolve_value(
    name: &str,
    ctx: &Arc<dyn AuthContext>,
    credential: Option<&ApiKeyCredential>,
    signal: &AbortSignal,
) -> Result<Option<String>, Thrown> {
    let from_credential = credential.and_then(|credential| {
        if name == CLOUDFLARE_API_KEY {
            credential.key.clone()
        } else {
            credential
                .env
                .as_ref()
                .and_then(|env| env.get(name))
                .cloned()
        }
    });
    if from_credential.is_some() {
        return Ok(from_credential);
    }
    signal.throw_if_aborted()?;
    let value = ctx.env(name).await;
    signal.throw_if_aborted()?;
    Ok(value)
}

struct ResolvedCloudflareEnv {
    api_key: String,
    env: ProviderEnv,
    source: String,
}

fn truthy(value: Option<String>) -> Option<String> {
    value.filter(|value| !value.is_empty())
}

async fn resolve_cloudflare_env(
    kind: CloudflareAuthKind,
    ctx: &Arc<dyn AuthContext>,
    credential: Option<&ApiKeyCredential>,
    signal: &AbortSignal,
) -> Result<Option<ResolvedCloudflareEnv>, Thrown> {
    let api_key = resolve_value(CLOUDFLARE_API_KEY, ctx, credential, signal).await?;
    let account_id = resolve_value(CLOUDFLARE_ACCOUNT_ID, ctx, credential, signal).await?;
    let gateway_id = match kind {
        CloudflareAuthKind::AiGateway => {
            resolve_value(CLOUDFLARE_GATEWAY_ID, ctx, credential, signal).await?
        }
        CloudflareAuthKind::WorkersAi => None,
    };

    let (Some(api_key), Some(account_id)) = (truthy(api_key), truthy(account_id)) else {
        return Ok(None);
    };
    let gateway_id = truthy(gateway_id);
    if kind == CloudflareAuthKind::AiGateway && gateway_id.is_none() {
        return Ok(None);
    }

    let mut env = ProviderEnv::from([(CLOUDFLARE_ACCOUNT_ID.to_owned(), account_id)]);
    if let Some(gateway_id) = gateway_id {
        env.insert(CLOUDFLARE_GATEWAY_ID.to_owned(), gateway_id);
    }
    Ok(Some(ResolvedCloudflareEnv {
        api_key,
        env,
        source: if credential.is_some() {
            "stored credential".to_owned()
        } else {
            CLOUDFLARE_API_KEY.to_owned()
        },
    }))
}

fn secret(message: &str) -> AuthPrompt {
    AuthPrompt::new(AuthPromptKind::Secret {
        message: message.to_owned(),
        placeholder: None,
    })
}

fn text(message: &str) -> AuthPrompt {
    AuthPrompt::new(AuthPromptKind::Text {
        message: message.to_owned(),
        placeholder: None,
    })
}

struct CloudflareAuth {
    kind: CloudflareAuthKind,
}

impl ApiKeyAuth for CloudflareAuth {
    // The trait returns a borrowed name; this one is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        "Cloudflare API key"
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
    ) -> Option<BoxFuture<'_, Result<ApiKeyCredential, Thrown>>> {
        Some(Box::pin(async move {
            let key = interaction
                .prompt(secret("Enter Cloudflare API key"))
                .await?;
            let account_id = interaction
                .prompt(text("Enter Cloudflare account ID"))
                .await?;
            let mut env = ProviderEnv::from([(CLOUDFLARE_ACCOUNT_ID.to_owned(), account_id)]);
            if self.kind == CloudflareAuthKind::AiGateway {
                let gateway_id = interaction
                    .prompt(text("Enter Cloudflare AI Gateway ID"))
                    .await?;
                env.insert(CLOUDFLARE_GATEWAY_ID.to_owned(), gateway_id);
            }
            Ok(ApiKeyCredential {
                key: Some(key),
                env: Some(env),
                ..ApiKeyCredential::default()
            })
        }))
    }

    fn resolve(
        &self,
        input: ApiKeyResolveInput,
    ) -> BoxFuture<'_, Result<Option<AuthResult>, Thrown>> {
        Box::pin(async move {
            let Some(resolved) = resolve_cloudflare_env(
                self.kind,
                &input.ctx,
                input.credential.as_ref(),
                &input.signal,
            )
            .await?
            else {
                return Ok(None);
            };
            let auth = match self.kind {
                CloudflareAuthKind::WorkersAi => ModelAuth {
                    api_key: Some(resolved.api_key),
                    ..ModelAuth::default()
                },
                CloudflareAuthKind::AiGateway => ModelAuth {
                    headers: Some(ProviderHeaders::from([
                        (
                            "cf-aig-authorization".to_owned(),
                            Some(format!("Bearer {}", resolved.api_key)),
                        ),
                        ("Authorization".to_owned(), None),
                        ("x-api-key".to_owned(), None),
                    ])),
                    ..ModelAuth::default()
                },
            };
            Ok(Some(AuthResult {
                auth,
                env: Some(resolved.env),
                source: Some(resolved.source),
            }))
        })
    }
}

/// TS `cloudflareWorkersAIAuth()`.
#[must_use]
pub fn cloudflare_workers_ai_auth() -> Arc<dyn ApiKeyAuth> {
    Arc::new(CloudflareAuth {
        kind: CloudflareAuthKind::WorkersAi,
    })
}

/// TS `cloudflareAIGatewayAuth()`.
#[must_use]
pub fn cloudflare_ai_gateway_auth() -> Arc<dyn ApiKeyAuth> {
    Arc::new(CloudflareAuth {
        kind: CloudflareAuthKind::AiGateway,
    })
}
