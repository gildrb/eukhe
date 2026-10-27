//! The `codemode` extension of an eukhe session (`eukhe_durable::codemode`):
//! the `codemode` tool, whose JavaScript scripts call the session's other
//! tools (`read`, `edit`, `grep`, `glob`, `ipython`, MCP tools, ...) as
//! durable nested calls and survive a worker restart by deterministic
//! replay, the internal tools behind its `models.*` globals, and the
//! `codemode` prompt section listing the tools scripts can call. A
//! `models.classify()` call that names no model takes the `judge` role's
//! model.

use std::sync::Arc;

use eukhe_durable::codemode::sandbox::{CodemodeSandbox, CodemodeSandboxOptions};
use eukhe_durable::codemode::{
    create_codemode_extension, ClassifierDefault, ClassifierResolver, CodemodeToolOptions,
};
use eukhe_durable::harness::types::Extension;

use super::deps::HostDeps;
use crate::tiny::judge::judge_classifier;
use crate::tiny::{role_settings, Role, TinyHome};

/// The extension of one session, with its own sandbox: every script runs in
/// a fresh `QuickJS` VM on its own thread, without a memory limit beyond the
/// process's. The `judge` role reads the session's current settings at
/// each call.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let settings = Arc::clone(&deps.settings);
    let home = TinyHome::under(&deps.agent_dir);
    let resolver: ClassifierResolver = Arc::new(move |models, session_model| {
        let role = role_settings(settings.manager().cvars(), Role::Judge);
        let home = home.clone();
        Box::pin(async move {
            judge_classifier(&models, &role, &session_model, |model| {
                eukhe_tiny::installed(&home, model)
            })
            .await
            .map_err(|error| error.to_string())
        })
    });
    create_codemode_extension(CodemodeToolOptions {
        classifier: ClassifierDefault::Resolver(resolver),
        ..CodemodeToolOptions::new(CodemodeSandbox::new(CodemodeSandboxOptions::default()))
    })
}
