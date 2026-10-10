//! The daemon's enforcement of the settings `allowedModels` allowlist: the
//! worker-side model-resolution seams (`set_model`, the RLM child-model
//! resolution, and the worker's startup model chain) refuse a model
//! outside the allowlist loudly (a [`ModelAllowlistRefusal`] error
//! surfaces to the caller; the daemon never falls back to a different
//! model).

use anyhow::Result;
use std::path::Path;

use eukhe_core::models::ModelAllowlistRefusal;

/// The daemon allowlist's loaded state (settings `allowedModels`, global
/// scope). A security guardrail fails CLOSED: a settings document that
/// could not be loaded is an unknown policy, never an unrestricted one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DaemonAllowlist {
    /// No `allowedModels` configured: unrestricted (TS parity).
    Unrestricted,
    /// The configured patterns.
    Allowed(Vec<String>),
    /// The global settings document could not be loaded (lock contention,
    /// read, or parse failure): the configured policy is unknown, so every
    /// resolution fails loudly instead of bypassing it.
    Unreadable(String),
}

/// Load the daemon allowlist state (settings `allowedModels`, global
/// scope).
pub(crate) fn load(cwd: &Path, agent_dir: &Path) -> DaemonAllowlist {
    let settings = eukhe_core::settings::SettingsManager::create(cwd, agent_dir);
    // Only a global document that failed to load is an unknown policy; a
    // setting-level error (a relative `trustedProjects` entry) is not.
    if let Some(error) = settings.global_load_error() {
        return DaemonAllowlist::Unreadable(error.to_string());
    }
    if let Some(patterns) = settings.get_allowed_models() {
        DaemonAllowlist::Allowed(patterns)
    } else {
        // A PRESENT-but-malformed `allowedModels` (the lenient load
        // drops wrong-typed known fields to unset) fails closed: the
        // restriction was requested, so an unreadable shape is never an
        // unrestricted gate. Explicit `null` stays unset (TS parity).
        // A syntactically valid NON-OBJECT root (`[]`, `"bad"`) is a
        // corrupted document too: the guard fails closed rather than
        // reading a policy out of a shapeless document.
        let unreadable = settings.global_raw().and_then(|raw| {
            if !raw.is_object() {
                return Some("the global settings document is not a JSON object".to_string());
            }
            let malformed = match raw.get("allowedModels") {
                None | Some(serde_json::Value::Null) => false,
                Some(value) => value
                    .as_array()
                    .is_none_or(|items| items.iter().any(|item| item.as_str().is_none())),
            };
            malformed.then(|| "allowedModels is present but is not an array of strings".to_string())
        });
        match unreadable {
            Some(message) => DaemonAllowlist::Unreadable(message),
            None => DaemonAllowlist::Unrestricted,
        }
    }
}

/// Enforce the allowlist on a resolved selector: `Ok(())` when allowed
/// (and when no allowlist is configured), the loud typed refusal for an
/// off-allowlist model, and a fail-closed error when the configured
/// policy could not be read.
pub(crate) fn assert_allowed(allowlist: &DaemonAllowlist, selector: &str) -> Result<()> {
    match allowlist {
        DaemonAllowlist::Unrestricted => Ok(()),
        DaemonAllowlist::Allowed(patterns) => {
            if eukhe_core::models::model_allowed(selector, patterns) {
                Ok(())
            } else {
                Err(ModelAllowlistRefusal {
                    selector: selector.to_string(),
                }
                .into())
            }
        }
        DaemonAllowlist::Unreadable(error) => Err(anyhow::anyhow!(
            "The daemon model allowlist could not be read ({error}); \
             refusing to resolve model \"{selector}\" -- the daemon fails closed instead of \
             bypassing the configured allowedModels policy. Fix settings.json and retry."
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_settings(dir: &Path, value: &str) {
        std::fs::create_dir_all(dir).unwrap();
        std::fs::write(dir.join("settings.json"), value).unwrap();
    }

    #[test]
    fn load_reads_the_global_scope_only() {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent_dir = dir.path().join("agent");
        // No settings: unrestricted.
        assert!(matches!(
            load(dir.path(), &agent_dir),
            DaemonAllowlist::Unrestricted
        ));
        // The global scope carries the allowlist.
        write_settings(&agent_dir, r#"{"allowedModels": ["prime-inference/*"]}"#);
        assert_eq!(
            load(dir.path(), &agent_dir),
            DaemonAllowlist::Allowed(vec!["prime-inference/*".to_string()])
        );
        // A project scope cannot weaken the global pin: the project dir is
        // the temp dir itself.
        write_settings(&dir.path().join(".eukhe"), r#"{"allowedModels": []}"#);
        assert_eq!(
            load(dir.path(), &agent_dir),
            DaemonAllowlist::Allowed(vec!["prime-inference/*".to_string()])
        );
    }

    #[test]
    fn load_trims_and_drops_empty_lists() {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent_dir = dir.path().join("agent");
        write_settings(
            &agent_dir,
            r#"{"allowedModels": ["  prime-inference/internal/*  ", ""]}"#,
        );
        assert_eq!(
            load(dir.path(), &agent_dir),
            DaemonAllowlist::Allowed(vec!["prime-inference/internal/*".to_string()])
        );
        // A list that trims to empty behaves as unset.
        write_settings(&agent_dir, r#"{"allowedModels": [" ", ""]}"#);
        assert!(matches!(
            load(dir.path(), &agent_dir),
            DaemonAllowlist::Unrestricted
        ));
    }

    #[test]
    fn assert_allowed_passes_without_an_allowlist_and_types_the_refusal() {
        // No allowlist: everything passes (TS parity).
        assert_allowed(&DaemonAllowlist::Unrestricted, "anything/model").unwrap();
        // Allowed by the allowlist.
        let allow = DaemonAllowlist::Allowed(vec!["prime-inference/*".to_string()]);
        assert_allowed(&allow, "prime-inference/internal/glm-5.3-fast").unwrap();
        // Refused: the typed error downcasts for callers.
        let error = assert_allowed(&allow, "zai/glm-5.3").expect_err("refused");
        let refusal = error
            .downcast_ref::<ModelAllowlistRefusal>()
            .expect("typed refusal");
        assert_eq!(refusal.selector, "zai/glm-5.3");
    }

    /// A settings document that cannot be loaded fails CLOSED: the
    /// configured policy is unknown, so the gate refuses every resolution
    /// with a loud error instead of bypassing the allowlist.
    #[test]
    fn an_unreadable_settings_document_fails_closed() {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&agent_dir).unwrap();
        std::fs::write(agent_dir.join("settings.json"), "{ not json").unwrap();
        let state = load(dir.path(), &agent_dir);
        assert!(matches!(state, DaemonAllowlist::Unreadable(_)));
        // The gate refuses a would-be-allowed model while unreadable...
        let error = assert_allowed(&state, "prime-inference/mock-1").expect_err("fail closed");
        let message = error.to_string();
        assert!(message.contains("could not be read"), "{message}");
        assert!(message.contains("fails closed"), "{message}");
        assert!(
            error.downcast_ref::<ModelAllowlistRefusal>().is_none(),
            "fail-closed is not a pattern refusal"
        );
        // ...and passes nothing as Unrestricted when the document is gone.
        std::fs::remove_file(agent_dir.join("settings.json")).unwrap();
        let state = load(dir.path(), &agent_dir);
        assert!(matches!(state, DaemonAllowlist::Unrestricted));
    }

    /// A PRESENT-but-malformed `allowedModels` (a wrong-typed known field,
    /// which the lenient settings load drops to unset) fails closed instead
    /// of silently unrestricted; an explicit `null` stays unset (TS parity).
    #[test]
    fn a_malformed_allowed_models_value_fails_closed() {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&agent_dir).unwrap();
        std::fs::write(
            agent_dir.join("settings.json"),
            r#"{"allowedModels": "prime-inference/*"}"#,
        )
        .unwrap();
        assert!(matches!(
            load(dir.path(), &agent_dir),
            DaemonAllowlist::Unreadable(_)
        ));
        std::fs::write(
            agent_dir.join("settings.json"),
            r#"{"allowedModels": ["prime-inference/*", 42]}"#,
        )
        .unwrap();
        assert!(matches!(
            load(dir.path(), &agent_dir),
            DaemonAllowlist::Unreadable(_)
        ));
        // Explicit null behaves as unset, and a valid empty list stays
        // unrestricted (the documented trim rule).
        std::fs::write(
            agent_dir.join("settings.json"),
            r#"{"allowedModels": null}"#,
        )
        .unwrap();
        assert!(matches!(
            load(dir.path(), &agent_dir),
            DaemonAllowlist::Unrestricted
        ));
        std::fs::write(agent_dir.join("settings.json"), r#"{"allowedModels": []}"#).unwrap();
        assert!(matches!(
            load(dir.path(), &agent_dir),
            DaemonAllowlist::Unrestricted
        ));
    }

    /// A syntactically valid NON-OBJECT global document (`[]`, `"bad"`)
    /// is a corrupted settings document, not an absent key: the guard
    /// fails closed (a shapeless document must never read as an
    /// unrestricted policy).
    #[test]
    fn a_non_object_global_document_fails_closed() {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&agent_dir).unwrap();
        for corrupted in ["[]", r#""bad""#, "42"] {
            std::fs::write(agent_dir.join("settings.json"), corrupted).unwrap();
            let state = load(dir.path(), &agent_dir);
            assert!(
                matches!(state, DaemonAllowlist::Unreadable(_)),
                "{corrupted} must fail closed, got {state:?}"
            );
            // The gate refuses every resolution while the document is
            // shapeless — never the typed pattern refusal.
            let error = assert_allowed(&state, "prime-inference/mock-1").expect_err("closed");
            assert!(
                error.downcast_ref::<ModelAllowlistRefusal>().is_none(),
                "fail-closed is not a pattern refusal"
            );
        }
    }
}
