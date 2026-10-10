//! Port of `test/harness-nested-tools.test.ts`, one submodule per group of
//! its `describe("nested tool calls")` cases, and `describe("tool task
//! version 1 records")` in [`version1`]. Shared helpers are in
//! [`super::nested_support`].

mod aborts;
mod calls;
mod progress;
mod version1;

use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;

use crate::harness::tests::chat_support::{chat_setup, ChatSetup};

fn setup() -> ChatSetup {
    chat_setup(RegisterFauxProviderOptions::default())
}
