//! `ssh://<host>/<path>` reads: the user's own `ssh`
//! program, with the user's `~/.ssh/config`, runs `cat` on one file of a
//! host that the setting `ssh.hosts` allows. eukhe handles no key and no
//! password: `BatchMode=yes` makes a host that asks for one fail at once,
//! as a typed `auth` rejection. The path goes to the remote shell as one
//! single-quoted word, so no character of it is shell syntax there.
//!
//! The read is bounded twice. The call's output cap
//! keeps the first bytes and counts the rest as dropped; the reply names
//! the count. The blocking budget ends the read: `ssh` runs in a process
//! group of its own, and the group is killed at the deadline.

use std::ffi::OsStr;
use std::process::Stdio;
use std::time::Duration;

use eukhe_docs::Remote;
use tokio::io::{AsyncRead, AsyncReadExt};
use tokio::process::Command;

use crate::platform::process::{signal_process_group, termination_signal, Signal};
use crate::settings::cvar::table::SSH_HOSTS;

/// The stderr bytes kept for the error message; the rest is drained.
const STDERR_CAP: usize = 8 * 1024;

/// Why an `ssh://` read gave no text; the message is model-facing.
#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub(super) enum SshError {
    /// The host is not in `ssh.hosts`.
    #[error("{url}: the host {host} is not in the setting `{setting}` ({allowed}); add the host to `{setting}` in the global settings.json to read from it", setting = SSH_HOSTS.id)]
    NotAllowed {
        url: String,
        host: String,
        /// The hosts the setting allows, as the message says them.
        allowed: String,
    },
    /// A kernel read outside a tool call: no output cap bounds it.
    #[error("ssh:// reads run in a tool call (the call's output cap bounds them); there is none")]
    NoCall,
    /// No `ssh` program on `PATH`.
    #[error("{url}: no `ssh` program on PATH; eukhe reads ssh:// URLs through the user's own ssh")]
    NoSsh { url: String },
    /// `ssh` did not start, or its pipes failed.
    #[error("{url}: ssh failed to run: {detail}")]
    Run { url: String, detail: String },
    /// `ssh` cannot resolve the host name.
    #[error("{url}: unknown host: {detail}")]
    UnknownHost { url: String, detail: String },
    /// `ssh` cannot connect to the host.
    #[error("{url}: cannot connect: {detail}")]
    Unreachable { url: String, detail: String },
    /// The host key is not in `known_hosts`, or it changed.
    #[error("{url}: the host key is not known or it changed: {detail}; check and accept the key with a plain `ssh` first")]
    HostKey { url: String, detail: String },
    /// The host refused every key `ssh` offered without a prompt.
    #[error("{url}: authentication failed: {detail}; eukhe gives ssh no password or passphrase (BatchMode), so load the key into ssh-agent or name it in ~/.ssh/config")]
    Auth { url: String, detail: String },
    /// Another `ssh` failure (exit 255).
    #[error("{url}: ssh failed: {detail}")]
    Ssh { url: String, detail: String },
    /// The remote file does not exist.
    #[error("{url}: not found: {detail}")]
    NotFound { url: String, detail: String },
    /// The remote path is a directory.
    #[error("{url}: is a directory; ssh:// reads one file")]
    IsDirectory { url: String },
    /// The remote user may not read the file.
    #[error("{url}: permission denied: {detail}")]
    PermissionDenied { url: String, detail: String },
    /// The remote `cat` failed for another reason.
    #[error("{url}: the remote read failed ({status}): {detail}")]
    Remote {
        url: String,
        /// `exit N` or `signal N`.
        status: String,
        detail: String,
    },
    /// The file is not UTF-8 text.
    #[error("{url}: binary file ({bytes} bytes read); ssh:// reads text")]
    Binary { url: String, bytes: usize },
    /// The read did not end within the blocking budget.
    #[error("{url}: the read did not end within the blocking budget ({budget_ms} ms; {bytes} bytes came)")]
    Timeout {
        url: String,
        budget_ms: u128,
        bytes: u64,
    },
}

impl SshError {
    /// The rejection reason.
    pub(super) fn reason(&self) -> &'static str {
        match self {
            Self::NotAllowed { .. } => "not_allowed",
            Self::NoCall => "arguments",
            Self::NoSsh { .. } | Self::Run { .. } | Self::Ssh { .. } | Self::Remote { .. } => "io",
            Self::UnknownHost { .. } | Self::Unreachable { .. } | Self::HostKey { .. } => "host",
            Self::Auth { .. } => "auth",
            Self::NotFound { .. } => "not_found",
            Self::IsDirectory { .. } => "is_directory",
            Self::PermissionDenied { .. } => "permission_denied",
            Self::Binary { .. } => "binary",
            Self::Timeout { .. } => "timeout",
        }
    }
}

/// The bytes a stream produced: the first `cap` kept, every byte counted.
struct Collected {
    kept: Vec<u8>,
    /// `None`: keep every byte (the output cap's opt-out).
    cap: Option<usize>,
    total: u64,
}

impl Collected {
    fn new(cap: Option<usize>) -> Self {
        Self {
            kept: Vec::new(),
            cap,
            total: 0,
        }
    }

    /// Read `stream` to its end.
    async fn drain(&mut self, mut stream: impl AsyncRead + Unpin) -> std::io::Result<()> {
        let mut chunk = [0_u8; 16 * 1024];
        loop {
            let read = stream.read(&mut chunk).await?;
            if read == 0 {
                return Ok(());
            }
            self.total += read as u64;
            let room = self
                .cap
                .map_or(read, |cap| cap.saturating_sub(self.kept.len()).min(read));
            self.kept.extend_from_slice(&chunk[..room]);
        }
    }

    fn full(&self) -> bool {
        self.cap.is_some_and(|cap| self.kept.len() >= cap)
    }
}

/// One `ssh://` read of a host that `ssh.hosts` allows.
pub(super) struct SshRead<'a> {
    /// The `ssh` program: `ssh` (found on `PATH`) outside the tests.
    program: &'a OsStr,
    /// The URL as authored, for the messages.
    url: &'a str,
    remote: Remote<'a>,
    budget: Duration,
    /// The call's output cap in bytes; `None` under the opt-out.
    cap: Option<usize>,
}

impl<'a> SshRead<'a> {
    /// A read of `remote` when `hosts` (the setting `ssh.hosts`) has its
    /// host.
    ///
    /// # Errors
    ///
    /// [`SshError::NotAllowed`].
    pub(super) fn new(
        program: &'a OsStr,
        url: &'a str,
        remote: Remote<'a>,
        hosts: &[String],
        budget: Duration,
        cap: Option<usize>,
    ) -> Result<Self, SshError> {
        if !hosts.iter().any(|allowed| allowed == remote.host) {
            return Err(SshError::NotAllowed {
                url: url.to_owned(),
                host: remote.host.to_owned(),
                allowed: if hosts.is_empty() {
                    "it is empty, so every ssh:// read is rejected".to_owned()
                } else {
                    format!("it allows {}", hosts.join(", "))
                },
            });
        }
        Ok(Self {
            program,
            url,
            remote,
            budget,
            cap,
        })
    }

    /// The `ssh` arguments: no TTY, no prompt, no forwarding, a connect
    /// timeout within the budget, `--` before the host, and the remote
    /// command as one word with the path single-quoted (`'` as `'\''`).
    fn arguments(&self) -> Vec<String> {
        vec![
            "-T".to_owned(),
            "-o".to_owned(),
            "BatchMode=yes".to_owned(),
            "-o".to_owned(),
            format!(
                "ConnectTimeout={}",
                self.budget.as_millis().div_ceil(1000).max(1)
            ),
            "-o".to_owned(),
            "ClearAllForwardings=yes".to_owned(),
            "--".to_owned(),
            self.remote.host.to_owned(),
            format!("cat -- '{}'", self.remote.path.replace('\'', r"'\''")),
        ]
    }

    /// Run the read: the file's text, with a first line that counts the
    /// bytes the output cap dropped when it dropped any.
    ///
    /// # Errors
    ///
    /// Every [`SshError`] but [`SshError::NotAllowed`] and
    /// [`SshError::NoCall`].
    #[tracing::instrument(name = "documents.read_ssh", skip_all, fields(host = self.remote.host))]
    pub(super) async fn run(&self) -> Result<String, SshError> {
        let url = || self.url.to_owned();
        let run_error = |error: std::io::Error| SshError::Run {
            url: url(),
            detail: error.to_string(),
        };
        let mut child = Command::new(self.program)
            .args(self.arguments())
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .process_group(0)
            .kill_on_drop(true)
            .spawn()
            .map_err(|error| {
                if error.kind() == std::io::ErrorKind::NotFound {
                    SshError::NoSsh { url: url() }
                } else {
                    run_error(error)
                }
            })?;
        let (Some(stdout), Some(stderr)) = (child.stdout.take(), child.stderr.take()) else {
            return Err(run_error(std::io::Error::other("ssh has no output pipes")));
        };
        let mut out = Collected::new(self.cap);
        let mut err = Collected::new(Some(STDERR_CAP));
        let ended = tokio::time::timeout(self.budget, async {
            let (read_out, read_err) = tokio::join!(out.drain(stdout), err.drain(stderr));
            read_out?;
            read_err?;
            child.wait().await
        })
        .await;
        let cut_at_budget = match ended {
            Ok(Ok(status)) => {
                let stderr = String::from_utf8_lossy(&err.kept);
                let detail = stderr
                    .lines()
                    .rev()
                    .find(|line| !line.trim().is_empty())
                    .unwrap_or("")
                    .trim()
                    .to_owned();
                let has = |needles: &[&str]| needles.iter().any(|needle| stderr.contains(needle));
                match status.code() {
                    Some(0) => false,
                    Some(255) => {
                        return Err(
                            if has(&[
                                "Host key verification failed",
                                "REMOTE HOST IDENTIFICATION HAS CHANGED",
                            ]) {
                                SshError::HostKey { url: url(), detail }
                            } else if has(&[
                                "Permission denied",
                                "Too many authentication failures",
                                "No more authentication methods",
                            ]) {
                                SshError::Auth { url: url(), detail }
                            } else if has(&["Could not resolve hostname"]) {
                                SshError::UnknownHost { url: url(), detail }
                            } else if has(&[
                                "Connection refused",
                                "Connection timed out",
                                "Operation timed out",
                                "No route to host",
                                "Network is unreachable",
                                "Connection closed",
                                "Connection reset",
                            ]) {
                                SshError::Unreachable { url: url(), detail }
                            } else {
                                SshError::Ssh { url: url(), detail }
                            },
                        );
                    }
                    code => {
                        return Err(if has(&["No such file or directory", "Not a directory"]) {
                            SshError::NotFound { url: url(), detail }
                        } else if has(&["Is a directory"]) {
                            SshError::IsDirectory { url: url() }
                        } else if has(&["Permission denied"]) {
                            SshError::PermissionDenied { url: url(), detail }
                        } else {
                            SshError::Remote {
                                url: url(),
                                status: code.map_or_else(
                                    || {
                                        termination_signal(&status).map_or_else(
                                            || "no exit code".to_owned(),
                                            |signal| format!("signal {signal}"),
                                        )
                                    },
                                    |code| format!("exit {code}"),
                                ),
                                detail,
                            }
                        });
                    }
                }
            }
            Ok(Err(error)) => return Err(run_error(error)),
            Err(_elapsed) => {
                let reaped = match child.id().and_then(|pid| i32::try_from(pid).ok()) {
                    Some(group) => {
                        let _gone = signal_process_group(group, Signal::Kill);
                        child.wait().await.map(drop)
                    }
                    None => Ok(()),
                };
                reaped.map_err(run_error)?;
                if !out.full() {
                    return Err(SshError::Timeout {
                        url: url(),
                        budget_ms: self.budget.as_millis(),
                        bytes: out.total,
                    });
                }
                true
            }
        };
        let complete = !out.full() || out.total == out.kept.len() as u64;
        let text = match std::str::from_utf8(&out.kept) {
            Ok(text) => text,
            // The cap cut a character: its first bytes count as dropped.
            Err(error) if error.error_len().is_none() && !complete => {
                std::str::from_utf8(&out.kept[..error.valid_up_to()]).map_err(|_| {
                    SshError::Binary {
                        url: url(),
                        bytes: out.kept.len(),
                    }
                })?
            }
            Err(_) => {
                return Err(SshError::Binary {
                    url: url(),
                    bytes: out.kept.len(),
                })
            }
        };
        if text.contains('\0') {
            return Err(SshError::Binary {
                url: url(),
                bytes: out.kept.len(),
            });
        }
        let shown = text.len() as u64;
        let dropped = out.total - shown;
        Ok(match (dropped, cut_at_budget) {
            (0, false) => text.to_owned(),
            (_, false) => format!(
                "[{}: {shown} of {} bytes shown; the output cap dropped {dropped}]\n{text}",
                self.url, out.total
            ),
            (_, true) => format!(
                "[{}: the first {shown} bytes shown; the output cap dropped {dropped} or more (the read stopped at the blocking budget)]\n{text}",
                self.url
            ),
        })
    }
}

#[cfg(test)]
mod tests;
