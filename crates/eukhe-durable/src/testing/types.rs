//! Port of `testing/types.ts`.

use std::fmt;
use std::sync::Arc;

use futures::future::BoxFuture;

use crate::env::ExecutionEnv;
use crate::types::Storage;

/// One storage case's body: runs against the storage it is given.
pub type StorageTest = Box<dyn FnOnce(Arc<dyn Storage>) -> BoxFuture<'static, ()> + Send>;

/// Calls its test exactly once with a fresh storage, awaits it, then cleans up.
pub type StorageConformanceProvider =
    Arc<dyn Fn(StorageTest) -> BoxFuture<'static, ()> + Send + Sync>;

/// What [`create_storage_conformance`](super::create_storage_conformance) needs.
#[derive(Clone)]
pub struct StorageConformanceOptions {
    pub with_storage: StorageConformanceProvider,
}

impl fmt::Debug for StorageConformanceOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("StorageConformanceOptions")
            .finish_non_exhaustive()
    }
}

/// One storage conformance case. A case fails by panicking.
pub struct StorageConformanceCase {
    pub name: &'static str,
    pub(super) run: Arc<dyn Fn() -> BoxFuture<'static, ()> + Send + Sync>,
}

impl StorageConformanceCase {
    /// Run the case once with a fresh storage from the provider.
    #[must_use]
    pub fn run(&self) -> BoxFuture<'static, ()> {
        (self.run)()
    }
}

impl fmt::Debug for StorageConformanceCase {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("StorageConformanceCase")
            .field("name", &self.name)
            .finish_non_exhaustive()
    }
}

/// One case's body: runs against the environment it is given.
pub type EnvTest = Box<dyn FnOnce(Arc<dyn ExecutionEnv>) -> BoxFuture<'static, ()> + Send>;

/// Calls its test once with an environment whose `cwd` is a fresh, empty,
/// writable directory, then cleans up.
pub type EnvConformanceProvider = Arc<dyn Fn(EnvTest) -> BoxFuture<'static, ()> + Send + Sync>;

/// What [`create_env_conformance`](super::create_env_conformance) needs.
#[derive(Clone)]
pub struct EnvConformanceOptions {
    pub with_env: EnvConformanceProvider,
    /// Program and flag that run a POSIX shell script from the next argument;
    /// default `["sh", "-c"]`.
    pub shell: Option<Vec<String>>,
    /// Whether the shell's `ln -s` creates symbolic links; default true.
    pub symlinks: Option<bool>,
}

impl fmt::Debug for EnvConformanceOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("EnvConformanceOptions")
            .field("shell", &self.shell)
            .field("symlinks", &self.symlinks)
            .finish_non_exhaustive()
    }
}

/// One conformance case. A case fails by panicking.
pub struct EnvConformanceCase {
    pub name: &'static str,
    /// Cases that wait for an environment's watch latency need longer than a
    /// test runner's default timeout.
    pub timeout_ms: Option<u64>,
    pub(super) run: Arc<dyn Fn() -> BoxFuture<'static, ()> + Send + Sync>,
}

impl EnvConformanceCase {
    /// Run the case once with a fresh environment from the provider.
    #[must_use]
    pub fn run(&self) -> BoxFuture<'static, ()> {
        (self.run)()
    }
}

impl fmt::Debug for EnvConformanceCase {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("EnvConformanceCase")
            .field("name", &self.name)
            .field("timeout_ms", &self.timeout_ms)
            .finish_non_exhaustive()
    }
}
