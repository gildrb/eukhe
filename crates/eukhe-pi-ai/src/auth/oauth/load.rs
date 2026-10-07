//! OAuth flow loaders for lazily constructed provider auth. Port of
//! `auth/oauth/load.ts`. The TS loaders hide Node-only flow modules from
//! browser bundlers behind dynamic imports; Rust links every flow
//! statically, so each loader constructs its flow on first use.
//! `registerBundledOAuthFlowLoaders` (the Bun standalone-binary hook for the
//! same bundling concern) has no Rust counterpart.

use std::sync::Arc;

use futures::future::BoxFuture;

use super::{
    anthropic_oauth, create_radius_oauth, github_copilot_oauth, kimi_coding_oauth, meta_oauth,
    open_router_oauth, openai_chatgpt_oauth, openai_codex_oauth, xai_oauth, RadiusOAuthOptions,
};
use crate::auth::types::OAuthAuth;
use crate::utils::diagnostics::Thrown;

type Loaded = BoxFuture<'static, Result<Arc<dyn OAuthAuth>, Thrown>>;

fn ready(auth: Arc<dyn OAuthAuth>) -> Loaded {
    Box::pin(async move { Ok(auth) })
}

/// Loads [`anthropic_oauth`].
#[must_use]
pub fn load_anthropic_oauth() -> Loaded {
    ready(anthropic_oauth())
}

/// Loads [`openai_codex_oauth`].
#[must_use]
pub fn load_openai_codex_oauth() -> Loaded {
    ready(openai_codex_oauth())
}

/// Loads [`openai_chatgpt_oauth`].
#[must_use]
pub fn load_openai_chatgpt_oauth() -> Loaded {
    ready(openai_chatgpt_oauth())
}

/// Loads [`github_copilot_oauth`].
#[must_use]
pub fn load_github_copilot_oauth() -> Loaded {
    ready(github_copilot_oauth())
}

/// Loads [`open_router_oauth`].
#[must_use]
pub fn load_openrouter_oauth() -> Loaded {
    ready(open_router_oauth())
}

/// Loads [`kimi_coding_oauth`].
#[must_use]
pub fn load_kimi_coding_oauth() -> Loaded {
    ready(kimi_coding_oauth())
}

/// Loads [`meta_oauth`].
#[must_use]
pub fn load_meta_oauth() -> Loaded {
    ready(meta_oauth())
}

/// Loads [`xai_oauth`].
#[must_use]
pub fn load_xai_oauth() -> Loaded {
    ready(xai_oauth())
}

/// Loads [`create_radius_oauth`] for one gateway.
#[must_use]
pub fn load_radius_oauth(name: String, gateway: String) -> Loaded {
    ready(create_radius_oauth(&RadiusOAuthOptions { name, gateway }))
}
