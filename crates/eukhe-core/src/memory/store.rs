//! The two append-only streams on disk: `main/` holds the messages and
//! `tree/` the summary nodes, one JSONL file per local day. Every line is
//! written with one `write` and an `fsync` before the append returns; a
//! torn last line (a crash mid-write) is reported and skipped at load.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use super::Kind;

/// One message line of `main/`.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct MessageRecord {
    pub i: u64,
    pub kind: Kind,
    pub text: String,
    /// Bytes of `kind + ": " + text`.
    pub size: usize,
    /// ISO time the message was written (imports keep their source date).
    pub date: String,
}

/// One node line of `tree/`.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct NodeRecord {
    pub l: u32,
    pub i: u64,
    pub text: String,
    /// Bytes of `text`.
    pub size: usize,
}

/// Where one message lives on disk: its text is read back on demand, so
/// the process never holds the whole log in memory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MessageMeta {
    pub kind: Kind,
    pub size: usize,
    pub date: String,
    /// Index into [`Store::files`].
    pub file: usize,
    pub offset: u64,
    pub len: usize,
}

/// Whether a load may fix the files it reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LoadMode {
    /// The owner's load: a file without a final newline gets one, so the
    /// next write starts on its own line.
    Repair,
    /// A reader beside a live owner (the browse page): nothing is written.
    ReadOnly,
}

/// The loaded chat: every message (by id) and every node.
#[derive(Debug, Default)]
pub(crate) struct Loaded {
    pub messages: Vec<MessageMeta>,
    pub nodes: Vec<NodeRecord>,
    /// Problems found and skipped (torn lines, foreign nodes).
    pub problems: Vec<String>,
}

/// The files of the chat directory and the two appenders.
#[derive(Debug)]
pub(crate) struct Store {
    files: Vec<PathBuf>,
    main: Appender,
    tree: Appender,
}

#[derive(Debug)]
struct Appender {
    dir: PathBuf,
    open: Option<OpenDay>,
}

#[derive(Debug)]
struct OpenDay {
    day: String,
    file: File,
    len: u64,
    /// The file's index in [`Store::files`] (messages only).
    index: Option<usize>,
}

impl Store {
    /// Load the chat at `root`, creating its directories when missing.
    ///
    /// # Errors
    ///
    /// Returns an error when a directory or file cannot be read, a repair
    /// write fails, or the message ids are not exactly `0..T`.
    pub(crate) fn open(root: &Path, mode: LoadMode) -> io::Result<(Store, Loaded)> {
        let main_dir = root.join("main");
        let tree_dir = root.join("tree");
        if mode == LoadMode::Repair {
            fs::create_dir_all(&main_dir)?;
            fs::create_dir_all(&tree_dir)?;
            crate::platform::restrict_dir(root)?;
        }
        let mut loaded = Loaded::default();
        let mut files = Vec::new();
        let mut messages: Vec<(u64, MessageMeta)> = Vec::new();
        for path in day_files(&main_dir)? {
            let index = files.len();
            files.push(path.clone());
            for (offset, line) in read_lines(&path, mode, &mut loaded.problems)? {
                match serde_json::from_slice::<MessageRecord>(&line) {
                    Ok(record) => messages.push((
                        record.i,
                        MessageMeta {
                            kind: record.kind,
                            size: super::labeled(record.kind, &record.text).len(),
                            date: record.date,
                            file: index,
                            offset,
                            len: line.len(),
                        },
                    )),
                    Err(error) => loaded.problems.push(format!(
                        "{}: skipped a torn message line at byte {offset}: {error}",
                        path.display()
                    )),
                }
            }
        }
        messages.sort_by_key(|(i, _)| *i);
        for (position, (i, _)) in messages.iter().enumerate() {
            if *i != position as u64 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "the chat log at {} is not contiguous: expected message {position}, found {i}",
                        main_dir.display()
                    ),
                ));
            }
        }
        loaded.messages = messages.into_iter().map(|(_, meta)| meta).collect();
        for path in day_files(&tree_dir)? {
            for (offset, line) in read_lines(&path, mode, &mut loaded.problems)? {
                match serde_json::from_slice::<NodeRecord>(&line) {
                    Ok(record) => loaded.nodes.push(record),
                    Err(error) => loaded.problems.push(format!(
                        "{}: skipped a torn node line at byte {offset}: {error}",
                        path.display()
                    )),
                }
            }
        }
        Ok((
            Store {
                files,
                main: Appender {
                    dir: main_dir,
                    open: None,
                },
                tree: Appender {
                    dir: tree_dir,
                    open: None,
                },
            },
            loaded,
        ))
    }

    /// Append one message (write + fsync) to the file of `day`.
    ///
    /// # Errors
    ///
    /// Returns an error when the record cannot be written and synced.
    pub(crate) fn append_message(
        &mut self,
        record: &MessageRecord,
        day: &str,
    ) -> io::Result<MessageMeta> {
        let line = json_line(record)?;
        let offset = self.main.append(&line, day)?;
        let open = self
            .main
            .open
            .as_mut()
            .ok_or_else(|| io::Error::other("day file is not open"))?;
        let file = if let Some(index) = open.index {
            index
        } else {
            let path = self.main.dir.join(format!("{day}.jsonl"));
            // A reopened day keeps the index its file got at load.
            let index = if let Some(index) = self.files.iter().position(|known| *known == path) {
                index
            } else {
                self.files.push(path);
                self.files.len() - 1
            };
            open.index = Some(index);
            index
        };
        Ok(MessageMeta {
            kind: record.kind,
            size: record.size,
            date: record.date.clone(),
            file,
            offset,
            len: line.len() - 1,
        })
    }

    /// Append one node (write + fsync) to the file of `day`.
    ///
    /// # Errors
    ///
    /// Returns an error when the record cannot be written and synced.
    pub(crate) fn append_node(&mut self, record: &NodeRecord, day: &str) -> io::Result<()> {
        let line = json_line(record)?;
        self.tree.append(&line, day).map(|_| ())
    }

    /// Read one message back from its line.
    ///
    /// # Errors
    ///
    /// Returns an error when the line cannot be read or parsed.
    pub(crate) fn read_message(&self, meta: &MessageMeta) -> io::Result<MessageRecord> {
        let path = self.files.get(meta.file).ok_or_else(|| {
            io::Error::new(io::ErrorKind::NotFound, "message file index out of range")
        })?;
        let mut file = File::open(path)?;
        file.seek(SeekFrom::Start(meta.offset))?;
        let mut line = vec![0; meta.len];
        file.read_exact(&mut line)?;
        serde_json::from_slice(&line)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
    }
}

impl Appender {
    /// Write `line` to the day file (created on first use), then fsync it.
    /// Returns the line's offset.
    fn append(&mut self, line: &[u8], day: &str) -> io::Result<u64> {
        let reopen = self.open.as_ref().is_none_or(|open| open.day != day);
        if reopen {
            let path = self.dir.join(format!("{day}.jsonl"));
            let existed = path.exists();
            let mut options = OpenOptions::new();
            options.create(true).append(true);
            crate::platform::set_private_mode(&mut options);
            let file = options.open(&path)?;
            if !existed {
                // The new name must survive a crash too.
                File::open(&self.dir)?.sync_all()?;
            }
            let len = file.metadata()?.len();
            self.open = Some(OpenDay {
                day: day.to_string(),
                file,
                len,
                index: None,
            });
        }
        let open = self
            .open
            .as_mut()
            .ok_or_else(|| io::Error::other("day file is not open"))?;
        let offset = open.len;
        open.file.write_all(line)?;
        open.file.sync_all()?;
        open.len += line.len() as u64;
        Ok(offset)
    }
}

/// A record as one JSON line, newline included.
fn json_line<T: serde::Serialize>(record: &T) -> io::Result<Vec<u8>> {
    let mut line = serde_json::to_vec(record).map_err(io::Error::other)?;
    line.push(b'\n');
    Ok(line)
}

/// The `*.jsonl` files of a stream directory, sorted by name (day).
fn day_files(dir: &Path) -> io::Result<Vec<PathBuf>> {
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => return Err(error),
    };
    let mut files = Vec::new();
    for entry in entries {
        let path = entry?.path();
        if path
            .extension()
            .is_some_and(|extension| extension == "jsonl")
            && path.is_file()
        {
            files.push(path);
        }
    }
    files.sort();
    Ok(files)
}

/// The non-empty lines of a file with their byte offsets. In repair mode a
/// file whose last line has no newline gets one (fsynced), so the next
/// write starts on its own line.
fn read_lines(
    path: &Path,
    mode: LoadMode,
    problems: &mut Vec<String>,
) -> io::Result<Vec<(u64, Vec<u8>)>> {
    let bytes = fs::read(path)?;
    let mut lines = Vec::new();
    let mut start = 0;
    for (at, byte) in bytes.iter().enumerate() {
        if *byte == b'\n' {
            if at > start {
                lines.push((start as u64, bytes[start..at].to_vec()));
            }
            start = at + 1;
        }
    }
    if start < bytes.len() {
        lines.push((start as u64, bytes[start..].to_vec()));
        if mode == LoadMode::Repair {
            problems.push(format!(
                "{}: the last line had no newline; one was appended",
                path.display()
            ));
            let mut file = OpenOptions::new().append(true).open(path)?;
            file.write_all(b"\n")?;
            file.sync_all()?;
        }
    }
    Ok(lines)
}
