//! Default auth context. Port of `auth/context.ts`.

use std::sync::Arc;

use futures::future::BoxFuture;

use super::types::AuthContext;

struct DefaultProviderAuthContext;

impl AuthContext for DefaultProviderAuthContext {
    fn env<'a>(&'a self, name: &'a str) -> BoxFuture<'a, Option<String>> {
        Box::pin(async move {
            std::env::var(name)
                .ok()
                .filter(|value| !value.trim().is_empty())
        })
    }

    fn file_exists<'a>(&'a self, path: &'a str) -> BoxFuture<'a, bool> {
        Box::pin(async move {
            let resolved = match path.strip_prefix('~') {
                Some(rest) => match std::env::home_dir() {
                    Some(home) => format!("{}{rest}", home.display()),
                    None => return false,
                },
                None => path.to_owned(),
            };
            tokio::fs::metadata(resolved).await.is_ok()
        })
    }
}

/// Default auth context: env vars from the process environment, file
/// existence via the filesystem.
#[must_use]
pub fn default_provider_auth_context() -> Arc<dyn AuthContext> {
    Arc::new(DefaultProviderAuthContext)
}
