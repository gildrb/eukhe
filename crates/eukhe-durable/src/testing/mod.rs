//! Runner-independent conformance suites for implementations of the crate's
//! interfaces. Port of `testing/index.ts` (the `Storage` and `ExecutionEnv`
//! suites).
//!
//! The TS runner adapters (`createExpectAssertions`, `registerStorageConformance`,
//! `registerEnvConformance`) bind the cases to Vitest/Jest. Rust has one test
//! harness, so the cases assert with the std macros and
//! [`run_storage_conformance`] / [`run_env_conformance`] run them all.

mod env_conformance;
mod storage_conformance;
mod types;

pub use env_conformance::{create_env_conformance, run_env_conformance};
pub use storage_conformance::{create_storage_conformance, run_storage_conformance};
pub use types::{
    EnvConformanceCase, EnvConformanceOptions, EnvConformanceProvider, EnvTest,
    StorageConformanceCase, StorageConformanceOptions, StorageConformanceProvider, StorageTest,
};
