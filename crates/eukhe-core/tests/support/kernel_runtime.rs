//! The kernel interpreter of the real-kernel tests: a venv of this
//! checkout's `eukhe-runtime` (editable, synced from
//! `eukhe-runtime/uv.lock`) with this checkout's Python skills installed
//! editable. Never the user's installed kernel venv: the tests validate
//! the runtime and skills of the tree under test.
//!
//! The venv lives in the temp dir, keyed by the checkout path, `HOME`
//! (uv's managed interpreters live under it), the lock, and the skill
//! manifests. A file lock serializes concurrent test processes; a `ready`
//! stamp marks a finished build. `uv` must be on `PATH`.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use sha2::{Digest, Sha256};

/// The kernel python every real-kernel test hands to its kernels. Builds
/// the venv on first use; panics with the cause when it cannot.
pub fn kernel_python() -> PathBuf {
    static PYTHON: OnceLock<PathBuf> = OnceLock::new();
    PYTHON.get_or_init(provision).clone()
}

fn provision() -> PathBuf {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("resolve the checkout root");
    let runtime = root.join("eukhe-runtime");
    let mut skills = std::fs::read_dir(root.join("skills"))
        .expect("read the checkout's skills/")
        .map(|entry| entry.expect("read a skills/ entry").path())
        .filter(|dir| dir.join("pyproject.toml").is_file())
        .collect::<Vec<_>>();
    skills.sort();

    let mut key = Sha256::new();
    key.update(root.as_os_str().as_encoded_bytes());
    key.update([0]);
    key.update(
        std::env::var_os("HOME")
            .unwrap_or_default()
            .as_encoded_bytes(),
    );
    key.update([0]);
    key.update(std::fs::read(runtime.join("uv.lock")).expect("read eukhe-runtime/uv.lock"));
    for skill in &skills {
        key.update([0]);
        key.update(skill.as_os_str().as_encoded_bytes());
        key.update([0]);
        key.update(std::fs::read(skill.join("pyproject.toml")).expect("read a skill pyproject"));
    }
    let key = format!("{:x}", key.finalize());
    let base = std::env::temp_dir().join("eukhe-test-kernel");
    std::fs::create_dir_all(&base).expect("create the test kernel dir");
    let venv = base.join(&key[..16]);
    let python = venv.join("bin").join("python");

    let lock = std::fs::File::create(base.join(format!("{}.lock", &key[..16])))
        .expect("create the test kernel lock");
    lock.lock().expect("lock the test kernel venv");
    let ready = venv.join("ready");
    if ready.is_file() {
        return python;
    }
    if venv.exists() {
        std::fs::remove_dir_all(&venv).expect("remove a half-built test kernel venv");
    }
    let mut sync = Command::new("uv");
    sync.args([
        "sync",
        "--no-config",
        "--locked",
        "--group",
        "kernel",
        "--python",
        "3.11",
    ])
    .arg("--project")
    .arg(&runtime)
    .env("UV_PROJECT_ENVIRONMENT", &venv);
    run_uv(&mut sync);
    let mut install = Command::new("uv");
    install
        .args(["pip", "install", "--no-config", "--python"])
        .arg(&python)
        .args(["--no-deps", "--no-index", "--no-build-isolation"]);
    for skill in &skills {
        install.arg("--editable").arg(skill);
    }
    run_uv(&mut install);
    std::fs::write(&ready, "").expect("stamp the test kernel venv");
    python
}

fn run_uv(command: &mut Command) {
    let output = command.output().unwrap_or_else(|error| {
        panic!(
            "the real-kernel tests need uv on PATH to build the test kernel venv from \
             eukhe-runtime/uv.lock: {error}"
        )
    });
    assert!(
        output.status.success(),
        "building the test kernel venv failed ({command:?}): {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
