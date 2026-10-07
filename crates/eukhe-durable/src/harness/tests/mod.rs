//! Harness tests and their shared support (ports of `test/harness-*.test.ts`
//! with `test/harness-support.ts`, `test/chat-support.ts`, and
//! `test/task-support.ts`).
//!
//! Harness tests need crate-internal functions (`resolve_agent`, the
//! scheduler), so they are unit tests of this crate rather than integration
//! tests under `tests/`; the support modules are `pub(crate)` for every test
//! module of the harness.

pub(crate) mod chat_support;
mod events;
mod registry;
pub(crate) mod support;
mod task_graph;
pub(crate) mod task_support;
mod view;
// HarnessCore tests.
mod context;
mod conversations;
mod inbox;
mod inspect;
mod lifecycle;
mod ownership;
mod submissions;
// HarnessCompaction tests.
mod compaction;
