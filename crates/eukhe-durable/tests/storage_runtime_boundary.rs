//! Port of `test/storage-runtime-boundary.test.ts`.
//!
//! TS checks the import graph of each portable entry point for Node
//! built-ins. The Rust equivalent is source-level: the portable modules must
//! not reach the native adapters (`rusqlite`, `NativeExecutionEnv`, the
//! `native` submodules), which own every OS-specific dependency.

use std::path::Path;

fn source(relative: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join(relative);
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

#[track_caller]
fn assert_free_of(relative: &str, forbidden: &[&str]) {
    let text = source(relative);
    for needle in forbidden {
        assert!(!text.contains(needle), "{relative} references {needle}");
    }
}

#[test]
fn keeps_the_package_root_limited_to_portable_core_storage() {
    for file in [
        "storage/memory.rs",
        "storage/common.rs",
        "types.rs",
        "ids.rs",
        "errors.rs",
    ] {
        assert_free_of(
            file,
            &[
                "crate::env",
                "storage::jsonl",
                "storage::sqlite",
                "rusqlite",
                "jsonl::",
                "sqlite::",
            ],
        );
    }
}

#[test]
fn keeps_the_portable_sqlite_subpath_free_of_native_imports() {
    for file in [
        "storage/sqlite/database.rs",
        "storage/sqlite/migrations.rs",
        "storage/sqlite/storage.rs",
    ] {
        assert_free_of(file, &["rusqlite", "native", "crate::env"]);
    }
}

#[test]
fn keeps_the_portable_environment_subpath_free_of_native_imports() {
    let module = source("env/mod.rs");
    for line in module
        .lines()
        .filter(|line| line.trim_start().starts_with("use "))
    {
        assert!(
            !line.contains("native"),
            "env/mod.rs imports native code: {line}"
        );
    }
}

#[test]
fn keeps_the_portable_jsonl_subpath_free_of_native_imports() {
    assert_free_of(
        "storage/jsonl/storage.rs",
        &["NativeExecutionEnv", "env::native", "rusqlite", "std::fs"],
    );
}
