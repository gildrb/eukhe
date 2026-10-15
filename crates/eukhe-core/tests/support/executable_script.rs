//! Executable fixture scripts that a concurrent fork can never make
//! unexecutable.
//!
//! A script this test process writes itself can fail to exec with
//! `ETXTBSY` ("Text file busy"): another test thread's child, still
//! between its `fork` and its `exec`, holds a copy of the write
//! descriptor (`O_CLOEXEC` only closes it at the exec), and Linux refuses
//! to exec a file open for writing. A short-lived `/bin/sh` writes the
//! script instead, so this process never holds a descriptor of it that a
//! sibling's fork could copy, and the writer has exited when this returns.

use std::path::Path;
use std::process::Command;

/// Write `script` to `path` with the permission bits `mode` (e.g. `0o700`).
pub fn write_executable_script(path: &Path, script: &str, mode: u32) {
    let status = Command::new("/bin/sh")
        .args([
            "-c",
            "printf '%s' \"$1\" > \"$2\" && chmod \"$3\" \"$2\"",
            "sh",
        ])
        .arg(script)
        .arg(path)
        .arg(format!("{mode:o}"))
        .status()
        .expect("spawn /bin/sh to write the script");
    assert!(
        status.success(),
        "writing the script {} failed: {status}",
        path.display()
    );
}
