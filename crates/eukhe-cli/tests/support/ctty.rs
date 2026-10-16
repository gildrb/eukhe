//! The pty child's session and controlling-terminal claim. The pty e2es
//! re-execute their own test binary as the product-under-test with the
//! harness's pty slave on stdin/stdout/stderr; the child mode calls
//! [`claim_controlling_tty`] first, before anything touches the terminal.

/// Become a session leader (`setsid`) and claim stdin — the harness's pty
/// slave — as the controlling terminal (`TIOCSCTTY`), so `/dev/tty`, job
/// control, and hangup all bind to the harness pty, never the runner's own
/// terminal.
///
/// # Panics
///
/// When either step fails (the child would otherwise run against the wrong
/// terminal topology).
pub fn claim_controlling_tty() {
    nix::unistd::setsid().expect("the pty child could not become a session leader");
    rustix::process::ioctl_tiocsctty(std::io::stdin())
        .expect("the pty child could not claim its pty slave as the controlling terminal");
}
