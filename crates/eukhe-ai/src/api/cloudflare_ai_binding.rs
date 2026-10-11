//! AI Gateway transport over the Workers AI binding (port of
//! `src/api/cloudflare-ai-binding.ts`).
//!
//! A Worker talks to an AI Gateway through the AI binding's `fetch`
//! passthrough (`env.AI.fetch()`), which serves the gateway's provider
//! passthrough at
//! `https://workers-binding.ai/ai-gateway/gateways/{gateway}/{provider}/{endpoint...}`.
//! Binding calls are pre-authenticated in-account and return the provider's
//! native wire format, so API implementations behave identically over the
//! binding and over HTTPS. A model whose `baseUrl` names that route needs no
//! translation: pass [`create_ai_binding_fetch`] as the request `fetch`.
//! Nothing is rewritten, buffered or re-encoded.

use std::sync::Arc;

use crate::types::FetchFunction;
use crate::utils::diagnostics::{ErrorObject, Thrown};

/// The Workers AI binding (`env.AI`), described structurally.
///
/// Implementations expose the binding's `aiGatewayLogId` and, when the
/// runtime provides it, its `fetch` passthrough. `fetch` returns `None` only
/// for bindings that predate `Ai#fetch`; every real binding has it.
pub trait AiBinding: Send + Sync {
    /// `aiGatewayLogId`: the member unique to the AI binding.
    fn ai_gateway_log_id(&self) -> Option<String>;
    /// The binding's `fetch`, bound to the binding; `None` when the runtime
    /// does not expose it.
    fn fetch(&self) -> Option<FetchFunction>;
}

/// Placeholder value for auth headers on binding-routed requests. API
/// implementations require an API key or a recognized auth header before
/// dispatch; binding calls are pre-authenticated, so pass
/// `cf-aig-authorization: Bearer {CLOUDFLARE_GATEWAY_BINDING_AUTH_SENTINEL}`
/// to satisfy the check. The gateway ignores (and strips)
/// `cf-aig-authorization` on binding-routed requests. Pair it with
/// `Authorization: None` / `x-api-key: None` so SDK placeholder auth headers
/// never reach the gateway, which would treat them as BYOK provider keys.
pub const CLOUDFLARE_GATEWAY_BINDING_AUTH_SENTINEL: &str = "cloudflare-gateway-binding";

/// Create a `fetch` backed by the AI binding, for models whose `baseUrl`
/// already names a route the binding serves. Requests pass through
/// untouched.
///
/// # Errors
///
/// `TypeError: createAiBindingFetch: the AI binding does not expose fetch()`
/// when the binding has no `fetch`: checked here, early, rather than as a
/// confusing failure on the first inference request.
pub fn create_ai_binding_fetch(binding: &dyn AiBinding) -> Result<FetchFunction, Thrown> {
    // Bound eagerly, as TS binds `binding.fetch` at construction.
    let Some(binding_fetch) = binding.fetch() else {
        return Err(ErrorObject::named(
            "TypeError",
            "createAiBindingFetch: the AI binding does not expose fetch()",
        )
        .thrown());
    };
    Ok(Arc::new(move |request| binding_fetch(request)))
}

#[cfg(test)]
#[path = "cloudflare_ai_binding_tests.rs"]
mod tests;
