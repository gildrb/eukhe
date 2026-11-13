//! The state a verdict judges: one number made of the conversation's
//! newest effect (a tool result or a user shell run), its newest message
//! of the user, and a fingerprint of the workspace. Any of them moving
//! moves the state, so a verdict taken before the worker's last effect,
//! before the user's last message, or before an edit made outside the
//! session no longer counts.
//!
//! The fingerprint of a git workspace is its `HEAD`, its staged and
//! unstaged diffs, and the content of every untracked file that is not
//! ignored; of any other directory, the path and content of each file
//! under it. Both count a file by its content (a large one by its size and
//! modification time), so a check that rewrites a file with the same bytes
//! (a `touch`, a regenerated report) leaves the state where it was. Both
//! read the disk only: no index lock is taken and nothing is written.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use eukhe_chord::context::Context;
use eukhe_durable::entries::{TOOL_RESULT_ENTRY, USER_ENTRY};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{EntryRecord, ScanOrder};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{Message, UserContent, UserContentBlock};
use sha2::{Digest, Sha256};

use crate::agent_messaging::AGENT_MESSAGE_CUSTOM_TYPE;
use crate::durable::entries::{CustomEntryData, BASH_ENTRY, CUSTOM_ENTRY};

/// How many entries one read of the conversation takes.
const PAGE: usize = 64;
/// The largest untracked file whose bytes the fingerprint reads; a larger
/// one counts by its size and modification time.
const MAX_HASHED_FILE: u64 = 4 << 20;
/// The most files one fingerprint visits; past it the count stands in.
const MAX_FILES: usize = 20_000;
/// The largest state: a wire `Nat` has at most 14 digits.
const MAX_STATE: u64 = 99_999_999_999_999;
/// Directories a non-git walk skips: build output and dependency stores
/// the worker's checks rewrite.
const SKIPPED_DIRS: &[&str] = &[".git", "target", "node_modules", "__pycache__", ".venv"];

/// The conversation's newest effect and newest message of the user.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct Marks {
    effect: u64,
    user: u64,
}

fn is_effect(entry: &EntryRecord) -> bool {
    entry.kind == TOOL_RESULT_ENTRY.kind() || entry.kind == BASH_ENTRY.kind()
}

/// Whether `entry` holds the words of the task's owner: a message the user
/// wrote (not a continuation the harness, a goal or a director added), or
/// in a child, a message of its parent (its task, the user's words relayed
/// by main).
fn is_users(entry: &EntryRecord) -> bool {
    if entry.kind == USER_ENTRY.kind() {
        return USER_ENTRY
            .narrow(entry.clone())
            .ok()
            .flatten()
            .is_some_and(|user| user.data().origin == InputOrigin::User);
    }
    entry.kind == CUSTOM_ENTRY.kind() && entry.model.is_some() && is_parents_message(entry)
}

/// Whether the custom `entry` is a message its parent sent this child.
fn is_parents_message(entry: &EntryRecord) -> bool {
    let Some(data) = entry
        .data
        .as_ref()
        .and_then(|data| serde_json::to_value(data).ok())
        .and_then(|data| serde_json::from_value::<CustomEntryData>(data).ok())
    else {
        return false;
    };
    data.custom_type == AGENT_MESSAGE_CUSTOM_TYPE
        && data
            .details
            .as_ref()
            .and_then(|details| details.get("fromRelationship"))
            .and_then(serde_json::Value::as_str)
            == Some("parent")
}

/// The newest effect and the newest user message of `conversation` (0 for
/// none).
async fn marks(conversation: &Conversation, cx: &Context) -> SessionResult<Marks> {
    let mut found = Marks::default();
    let mut cursor = None;
    loop {
        // Newest first.
        let page = conversation
            .entries(ConversationEntryQuery::default(), PAGE, cursor, cx)
            .await?;
        for entry in &page.items {
            if found.effect == 0 && is_effect(entry) {
                found.effect = entry.id.get();
            }
            if found.user == 0 && is_users(entry) {
                found.user = entry.id.get();
            }
            if found.effect != 0 && found.user != 0 {
                return Ok(found);
            }
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(found),
        }
    }
}

/// The state of `conversation` now, with `workspace` fingerprinted when
/// given: a number from 1 to 99999999999999 that changes with the newest
/// effect, the newest user message and the workspace; 0 while there is
/// none of them (no effect, no user message, no workspace), the state of
/// a conversation that never had an acceptance or a turn.
///
/// # Errors
///
/// Read failures.
pub(crate) async fn state_now(
    conversation: &Conversation,
    workspace: Option<&Path>,
    cx: &Context,
) -> SessionResult<u64> {
    let marks = marks(conversation, cx).await?;
    let print = match workspace {
        Some(cwd) => fingerprint(cwd).await,
        None if marks == Marks::default() => return Ok(0),
        None => [0; 32],
    };
    let mut hasher = Sha256::new();
    hasher.update(marks.effect.to_le_bytes());
    hasher.update(marks.user.to_le_bytes());
    hasher.update(print);
    let digest = hasher.finalize();
    let mut head = [0_u8; 8];
    head.copy_from_slice(&digest[..8]);
    Ok(u64::from_le_bytes(head) % MAX_STATE + 1)
}

/// The fingerprint of the workspace at `cwd`.
pub(crate) async fn fingerprint(cwd: &Path) -> [u8; 32] {
    let cwd = cwd.to_path_buf();
    // A panicked walk fingerprints as nothing: the state still moves with
    // the conversation.
    tokio::task::spawn_blocking(move || fingerprint_blocking(&cwd))
        .await
        .unwrap_or([0; 32])
}

/// `git <args>` in `dir`, its stdout when it succeeds. No optional lock is
/// taken, so a concurrent git of the worker never meets a held index.
fn git(dir: &Path, args: &[&str]) -> Option<Vec<u8>> {
    let output = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_OPTIONAL_LOCKS", "0")
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .output()
        .ok()?;
    output.status.success().then_some(output.stdout)
}

fn fingerprint_blocking(cwd: &Path) -> [u8; 32] {
    let mut hasher = Sha256::new();
    if let Some(top) = git(cwd, &["rev-parse", "--show-toplevel"]) {
        let top = PathBuf::from(String::from_utf8_lossy(&top).trim_end_matches('\n'));
        hasher.update(b"git\0");
        hash_git(&top, &mut hasher);
    } else {
        hasher.update(b"dir\0");
        hash_dir(cwd, &mut hasher);
    }
    let mut print = [0_u8; 32];
    print.copy_from_slice(&hasher.finalize());
    print
}

/// One field of the fingerprint: its length, then its bytes.
fn field(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn hash_git(top: &Path, hasher: &mut Sha256) {
    for args in [
        &["rev-parse", "--verify", "--quiet", "HEAD"][..],
        &[
            "diff",
            "--cached",
            "--binary",
            "--no-ext-diff",
            "--no-color",
        ][..],
        &["diff", "--binary", "--no-ext-diff", "--no-color"][..],
    ] {
        field(hasher, &git(top, args).unwrap_or_default());
    }
    let untracked =
        git(top, &["ls-files", "--others", "--exclude-standard", "-z"]).unwrap_or_default();
    let mut count = 0_usize;
    for path in untracked
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
    {
        count += 1;
        if count > MAX_FILES {
            break;
        }
        field(hasher, path);
        hash_file(&top.join(String::from_utf8_lossy(path).as_ref()), hasher);
    }
    hasher.update(count.to_le_bytes());
}

/// A file's bytes when small, else its size and modification time.
fn hash_file(path: &Path, hasher: &mut Sha256) {
    let Ok(meta) = std::fs::symlink_metadata(path) else {
        field(hasher, b"gone");
        return;
    };
    if meta.is_file() && meta.len() <= MAX_HASHED_FILE {
        match std::fs::read(path) {
            Ok(bytes) => field(hasher, &Sha256::digest(&bytes)),
            Err(_) => field(hasher, b"unreadable"),
        }
    } else {
        hash_meta(&meta, hasher);
    }
}

fn hash_meta(meta: &std::fs::Metadata, hasher: &mut Sha256) {
    let modified = meta
        .modified()
        .ok()
        .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
        .map_or(0, |since| since.as_nanos());
    hasher.update(meta.len().to_le_bytes());
    hasher.update(modified.to_le_bytes());
}

/// Every file under `root` (no symlink followed), in path order.
fn hash_dir(root: &Path, hasher: &mut Sha256) {
    let mut stack = vec![root.to_path_buf()];
    let mut count = 0_usize;
    while let Some(dir) = stack.pop() {
        let Ok(read) = std::fs::read_dir(&dir) else {
            continue;
        };
        let mut children: Vec<_> = read.filter_map(Result::ok).collect();
        children.sort_by_key(std::fs::DirEntry::file_name);
        // Pushed in reverse so the walk visits them in path order.
        for child in children.into_iter().rev() {
            let Ok(meta) = child.metadata() else {
                continue;
            };
            let path = child.path();
            if meta.is_dir() {
                if !SKIPPED_DIRS.iter().any(|skip| child.file_name() == *skip) {
                    stack.push(path);
                }
                continue;
            }
            count += 1;
            if count > MAX_FILES {
                hasher.update(count.to_le_bytes());
                return;
            }
            let relative = path.trim_prefix(root);
            field(hasher, relative.to_string_lossy().as_bytes());
            hash_file(&path, hasher);
        }
    }
    hasher.update(count.to_le_bytes());
}

/// The files a judge reads besides git's diff, each with its text: in a
/// git workspace the untracked files that are not ignored (a diff never
/// shows them), elsewhere every file under `cwd` (build output and
/// dependency stores skipped). Cut to `max_chars` in all; a binary file
/// shows its size only. `None` when `cwd` cannot be read.
pub(crate) async fn workspace_files(cwd: &Path, max_chars: usize) -> Option<String> {
    let cwd = cwd.to_path_buf();
    tokio::task::spawn_blocking(move || files_blocking(&cwd, max_chars))
        .await
        .ok()
        .flatten()
}

fn files_blocking(cwd: &Path, max_chars: usize) -> Option<String> {
    let (title, root, paths) = if let Some(top) = git(cwd, &["rev-parse", "--show-toplevel"]) {
        let top = PathBuf::from(String::from_utf8_lossy(&top).trim_end_matches('\n'));
        let listed = git(&top, &["ls-files", "--others", "--exclude-standard", "-z"])?;
        let paths: Vec<String> = listed
            .split(|byte| *byte == 0)
            .filter(|path| !path.is_empty())
            .take(MAX_FILES)
            .map(|path| String::from_utf8_lossy(path).into_owned())
            .collect();
        ("Files git does not track yet", top, paths)
    } else {
        std::fs::read_dir(cwd).ok()?;
        ("Files of the workspace", cwd.to_path_buf(), list_dir(cwd))
    };
    if paths.is_empty() {
        return Some(format!("{title}: none."));
    }
    let mut text = format!("{title}:");
    for path in paths {
        if text.chars().count() >= max_chars {
            text.push_str("\n... [more files not shown]");
            break;
        }
        let bytes = std::fs::read(root.join(&path)).unwrap_or_default();
        if bytes.contains(&0) {
            let _ = write!(text, "\n\n--- {path} (binary, {} bytes)", bytes.len());
            continue;
        }
        let body = String::from_utf8_lossy(&bytes);
        let left = max_chars.saturating_sub(text.chars().count());
        let shown: String = body.chars().take(left).collect();
        let cut = if shown.chars().count() < body.chars().count() {
            "\n... [truncated]"
        } else {
            ""
        };
        let _ = write!(text, "\n\n--- {path}\n{shown}{cut}");
    }
    Some(text)
}

/// The files under `root`, relative, in path order (no symlink followed;
/// [`SKIPPED_DIRS`] skipped), at most [`MAX_FILES`].
fn list_dir(root: &Path) -> Vec<String> {
    let mut found = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(read) = std::fs::read_dir(&dir) else {
            continue;
        };
        let mut children: Vec<_> = read.filter_map(Result::ok).collect();
        children.sort_by_key(std::fs::DirEntry::file_name);
        for child in children.into_iter().rev() {
            let Ok(meta) = child.metadata() else {
                continue;
            };
            let path = child.path();
            if meta.is_dir() {
                if !SKIPPED_DIRS.iter().any(|skip| child.file_name() == *skip) {
                    stack.push(path);
                }
            } else if found.len() < MAX_FILES {
                let relative = path.trim_prefix(root);
                found.push(relative.to_string_lossy().into_owned());
            }
        }
    }
    found.sort();
    found
}

/// The text of a user message: its text blocks; an image stands as
/// `[image]`.
fn user_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .map(|block| match block {
                UserContentBlock::Text(text) => text.text.clone(),
                UserContentBlock::Image(_) => "[image]".to_owned(),
            })
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

/// The messages the user wrote in `conversation` (in a child: its parent's
/// messages), oldest first, each cut to `max_chars`: what the intent judge
/// reads. Continuations the harness, a goal or a director added are not
/// the owner's and never enter.
///
/// # Errors
///
/// Read failures.
pub(crate) async fn user_messages(
    conversation: &Conversation,
    max_chars: usize,
    cx: &Context,
) -> SessionResult<Vec<String>> {
    let mut messages = Vec::new();
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(
                ConversationEntryQuery {
                    order: Some(ScanOrder::Ascending),
                    ..ConversationEntryQuery::default()
                },
                PAGE,
                cursor,
                cx,
            )
            .await?;
        for entry in page.items.iter().filter(|entry| is_users(entry)) {
            let Some(Message::User(message)) = entry.model.as_ref().and_then(|model| model.first())
            else {
                continue;
            };
            let text = user_text(&message.content);
            messages.push(if text.chars().count() > max_chars {
                let prefix: String = text.chars().take(max_chars).collect();
                format!("{prefix}\n... [truncated]")
            } else {
                text
            });
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(messages),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The fingerprint of a plain directory moves with a file's content
    /// change, a new file and a removed one, and stands when nothing
    /// changed, a file rewritten with the same bytes included.
    #[test]
    fn a_directory_fingerprint_moves_with_every_file_change() {
        let dir = tempfile::tempdir().expect("tempdir");
        let first = fingerprint_blocking(dir.path());
        assert_eq!(first, fingerprint_blocking(dir.path()));
        std::fs::write(dir.path().join("a.txt"), "one").expect("write");
        let written = fingerprint_blocking(dir.path());
        assert_ne!(written, first);
        std::fs::write(dir.path().join("a.txt"), "one more").expect("write");
        let grown = fingerprint_blocking(dir.path());
        assert_ne!(grown, written);
        std::thread::sleep(std::time::Duration::from_millis(20));
        std::fs::write(dir.path().join("a.txt"), "one more").expect("write");
        assert_eq!(fingerprint_blocking(dir.path()), grown);
        std::fs::remove_file(dir.path().join("a.txt")).expect("remove");
        assert_eq!(fingerprint_blocking(dir.path()), first);
    }

    /// The fingerprint of a git workspace moves with a tracked edit and
    /// with an untracked file's content, never with an ignored file.
    #[test]
    fn a_git_fingerprint_moves_with_tracked_and_untracked_changes() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        let run = |args: &[&str]| {
            let status = Command::new("git")
                .args(args)
                .current_dir(root)
                .env("GIT_AUTHOR_NAME", "t")
                .env("GIT_AUTHOR_EMAIL", "t@t")
                .env("GIT_COMMITTER_NAME", "t")
                .env("GIT_COMMITTER_EMAIL", "t@t")
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status()
                .expect("git runs");
            assert!(status.success(), "git {args:?}");
        };
        run(&["init", "-q"]);
        std::fs::write(root.join(".gitignore"), "ignored.txt\n").expect("write");
        std::fs::write(root.join("tracked.txt"), "v1").expect("write");
        run(&["add", "."]);
        run(&["commit", "-q", "-m", "init"]);
        let clean = fingerprint_blocking(root);
        std::fs::write(root.join("ignored.txt"), "noise").expect("write");
        assert_eq!(fingerprint_blocking(root), clean, "an ignored file");
        std::fs::write(root.join("tracked.txt"), "v2").expect("write");
        let edited = fingerprint_blocking(root);
        assert_ne!(edited, clean, "a tracked edit");
        std::fs::write(root.join("new.txt"), "a").expect("write");
        let untracked = fingerprint_blocking(root);
        assert_ne!(untracked, edited, "an untracked file");
        std::fs::write(root.join("new.txt"), "b").expect("write");
        assert_ne!(fingerprint_blocking(root), untracked, "its content");
    }
}
