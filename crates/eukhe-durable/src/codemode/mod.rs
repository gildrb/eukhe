//! Durable code mode (`@earendil-works/pi-durable/codemode` 1.2, with the
//! parts of `@earendil-works/pi-codemode` it runs on): a `codemode` tool that
//! runs model-written JavaScript in an embedded `QuickJS` sandbox, whose
//! scripts call the conversation's tools as nested calls and survive a
//! restart.
//!
//! Problem: a script is in-memory VM state. A restart while
//!
//! ```js
//! const results = await Promise.all(paths.map((path) => tools.read({ path })));
//! ```
//!
//! waits for the last of 200 reads would lose the script and every read it
//! made.
//!
//! Solution: deterministic replay ([`sandbox::CodemodeSandbox::start`]). The
//! VM only runs when the host hands it a result; given the same start data,
//! clock, seed, and results in the same order, it makes the same calls with
//! the same arguments. The tool is replay-safe: after a restart its
//! execution runs again, starts the script again from the stored start
//! data, and hands it the results it got before, in the order it got them,
//! from a journal written before each delivery. Nested tool calls reattach
//! to their tasks by key (`c<VM call id>`), so they never run twice unless
//! their own replay policy reruns them. Then the script continues live.
//!
//! Documents, scoped to the code mode call's task and gone when it settles:
//! - `pi.codemode.run`: the start data, written once before the VM starts,
//!   and the outcome, written once when the call decides it (with the store
//!   writes, in one transaction), so a rerun after that returns it without a
//!   VM.
//! - `pi.codemode.journal`: one entry per delivered result, in delivery
//!   order: the VM call ID, the clock value, the calls the VM had issued
//!   after processing it (once acknowledged), and a global's outcome, which
//!   nothing else stores.
//!
//! A rerun refuses to replay (no new nested calls) when this module's
//! version or the VM's fingerprint changed, when the deadline passed, or
//! when the script diverges: it makes another call, or calls in another
//! order, than the journal says. Each ends the call with an error result.
//!
//! The sandbox is `QuickJS` (`rquickjs`), as upstream's: the replay contract
//! needs a VM that runs only when the host delivers, with no I/O, timers,
//! or ambient clock, so a script is a pure function of its start data and
//! its results. A persistent Python kernel cannot give that (its namespace,
//! files, and clock outlive and leak into the script).

mod call;
pub mod declarations;
mod describe;
mod discover;
mod docs;
pub mod identifier;
mod models;
mod output;
pub mod sandbox;
pub mod source;
mod task;
mod tool;
mod types;

#[cfg(test)]
mod tests;

pub use describe::{
    codemode_description, codemode_section, declaration_of, sample_of, CodemodeModels,
    CodemodeNamespace, DEFAULT_CODEMODE_INLINE_BUDGET,
};
pub use docs::{
    CodemodeJournal, CodemodeRunState, CodemodeStart, CodemodeStore, JournalEntry, JournalGlobal,
    StartNamespace, StartTool, CODEMODE_JOURNAL_DOC, CODEMODE_RUN_DOC, CODEMODE_STORE_DOC,
};
pub use models::{
    create_model_tools, ClassifierDefault, ClassifierResolver, CODEMODE_INTERNAL_PREFIX,
};
pub use output::DEFAULT_MAX_OUTPUT_TOKENS;
pub use task::run_codemode_task;
pub use tool::{
    create_codemode_extension, create_codemode_tool, CodemodeGlobal, CodemodeGlobalExecute,
    CodemodeToolOptions, CODEMODE_MODULE_VERSION, CODEMODE_TOOL_NAME,
};
pub use types::{
    CodemodeCallStatus, CodemodeCallTarget, CodemodeDeclaredGlobal, CodemodeDeclaredTool,
    CodemodeDuring, CodemodeEnding, CodemodeError, CodemodeErrorKind, CodemodeHostCall,
    CodemodeNestedCall, CodemodeOutcome, CodemodeOutputItem, CodemodeResult, CodemodeStoreWrites,
    CodemodeToolDetails, TextOrigin,
};
