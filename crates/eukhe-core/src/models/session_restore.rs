//! Session-model restore: a revived session's saved model, looked up in the
//! local registry (port of `findRestorable` in model-resolver.ts). The
//! catalog is fully local, so the lookup is final — there is no refresh to
//! wait for.

use eukhe_types::ai::Model;

use super::registry::ModelRegistry;

/// TS `findRestorable`: the saved session model, when it is registered and
/// its provider has configured auth. `None` leaves the caller to fall back
/// (and to say so: the fallback must never be silent).
#[must_use]
pub fn find_session_model(
    registry: &ModelRegistry,
    provider: &str,
    model_id: &str,
) -> Option<Model> {
    registry
        .get_all()
        .iter()
        .find(|model| model.provider == provider && model.id == model_id)
        .filter(|model| registry.has_configured_auth(model))
        .cloned()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The restore predicate is find + configured auth: a registered model
    /// without provider auth is not restorable (TS `findRestorable`), and a
    /// model missing from the registry is not either.
    #[test]
    fn restore_requires_a_registered_model_with_configured_auth() {
        let auth = crate::auth::AuthStorage::in_memory_without_env(
            &crate::auth::AuthStorageData::default(),
            std::sync::Arc::new(crate::auth::NoOAuth),
        );
        let registry = ModelRegistry::in_memory(auth);
        assert!(
            find_session_model(&registry, "prime-inference", "z-ai/glm-5.3").is_none(),
            "no provider auth configured: not restorable"
        );
        assert!(
            find_session_model(&registry, "anthropic", "missing").is_none(),
            "not registered: not restorable"
        );
    }
}
