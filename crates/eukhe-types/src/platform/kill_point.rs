//! Kill points: where the exactly-once tests kill a process (spec O1-O8,
//! the Rust side).
//!
//! The runtime names each point of an effect's lifecycle as it passes it:
//! `intended` once the intent is durable, `started` once the start is
//! durable and before the launch, `finished` once the end is durable. A
//! test sets [`KILL_AT_ENV`] to `<kind>:<point>@<marker file>`; the first
//! process that reaches that point creates the marker and dies there by
//! `SIGKILL`, as `kill -9` at that instant would: no handler runs,
//! nothing is flushed. The marker makes it once: the replacement process
//! inherits the variable, finds the marker, and passes the point. Unset
//! (every real run), a point is a no-op.

use std::fs::OpenOptions;
use std::sync::LazyLock;

/// The variable a test names a kill point with:
/// `<kind>:<point>@<marker file>`.
pub const KILL_AT_ENV: &str = "EUKHE_TEST_KILL_AT";

/// The kill point the environment names, as `(kind:point, marker)`.
static TARGET: LazyLock<Option<(String, String)>> = LazyLock::new(|| {
    let value = std::env::var(KILL_AT_ENV).ok()?;
    let (point, marker) = value.split_once('@')?;
    Some((point.to_owned(), marker.to_owned()))
});

/// The process passes the point `point` of an effect of kind `kind`: it
/// dies here by `SIGKILL` when the environment names this point and no
/// process died at it before.
pub fn kill_point(kind: &str, point: &str) {
    let Some((target, marker)) = TARGET.as_ref() else {
        return;
    };
    if target.split_once(':') != Some((kind, point)) {
        return;
    }
    // The marker's creation decides which process dies: one, ever.
    if OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(marker)
        .is_err()
    {
        return;
    }
    let _ = nix::sys::signal::kill(nix::unistd::Pid::this(), nix::sys::signal::Signal::SIGKILL);
    // SIGKILL cannot be caught: the process is gone before this runs.
    std::process::abort();
}
