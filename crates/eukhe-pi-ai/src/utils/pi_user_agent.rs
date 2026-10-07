//! The `pi (<platform> <release>; <arch>)` user agent.

use std::sync::LazyLock;

/// Node `os.platform()` for the supported platforms.
fn node_platform() -> &'static str {
    match std::env::consts::OS {
        "macos" => "darwin",
        other => other,
    }
}

/// Node `os.arch()` for the supported platforms.
fn node_arch() -> &'static str {
    match std::env::consts::ARCH {
        "x86_64" => "x64",
        "aarch64" => "arm64",
        other => other,
    }
}

/// Node `os.release()`: the kernel release (`uname -r`).
fn node_release() -> String {
    rustix::system::uname()
        .release()
        .to_string_lossy()
        .into_owned()
}

/// The user agent, computed once per process.
static USER_AGENT: LazyLock<String> = LazyLock::new(|| {
    format!(
        "pi ({} {}; {})",
        node_platform(),
        node_release(),
        node_arch()
    )
});

/// TS `getPiUserAgent()` in a Node runtime.
#[must_use]
pub fn get_pi_user_agent() -> &'static str {
    &USER_AGENT
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_platform_release_and_arch() {
        let agent = get_pi_user_agent();
        assert!(agent.starts_with(&format!("pi ({} ", node_platform())));
        assert!(agent.ends_with(&format!("; {})", node_arch())));
        assert!(!node_release().is_empty());
    }
}
