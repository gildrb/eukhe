//! Scheduler tests: ports of `test/harness-tasks.test.ts`,
//! `test/harness-tasks-recovery.test.ts`, `test/harness-structured.test.ts`,
//! and `test/harness-cancellation-barrier.test.ts` over a full Harness, with
//! `test/task-support.ts` in [`crate::harness::tests::task_support`].

mod cancellation_barrier;
mod recovery;
mod structured;
mod tasks;
