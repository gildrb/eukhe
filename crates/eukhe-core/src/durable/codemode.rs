//! The `codemode` extension of an eukhe session (`eukhe_durable::codemode`):
//! the `codemode` tool, whose JavaScript scripts call the session's other
//! tools (`read`, `edit`, `grep`, `glob`, `ipython`, MCP tools, ...) as
//! durable nested calls and survive a worker restart by deterministic
//! replay, the internal tools behind its `models.*` globals, and the
//! `codemode` prompt section listing the tools scripts can call.

use std::sync::Arc;

use eukhe_durable::codemode::sandbox::{CodemodeSandbox, CodemodeSandboxOptions};
use eukhe_durable::codemode::{create_codemode_extension, CodemodeToolOptions};
use eukhe_durable::harness::types::Extension;

/// The extension of one session, with its own sandbox: every script runs in
/// a fresh `QuickJS` VM on its own thread, without a memory limit beyond the
/// process's.
#[must_use]
pub fn extension() -> Arc<Extension> {
    create_codemode_extension(CodemodeToolOptions::new(CodemodeSandbox::new(
        CodemodeSandboxOptions::default(),
    )))
}
