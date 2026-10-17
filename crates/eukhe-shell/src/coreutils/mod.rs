//! The shell's own coreutils: the common commands with their common
//! options, in process. [`run`] answers `None` for a command or option it
//! does not implement, before it reads or writes anything; the step then
//! runs the external program on the same streams.
//!
//! The commands that read input (`cat`, `head`, `tail`, `wc`, `grep`)
//! stream it: `head` stops reading when it has its lines, so its input
//! pipe closes. A write to a closed pipe ends a command with status 141,
//! as SIGPIPE ends a program.
//!
//! `ls` sorts names by byte (as `LC_ALL=C`), `grep -r` walks in name
//! order; messages follow GNU coreutils.

mod files;
mod grep;
mod text;

use std::io::{Read, Write};
use std::path::Path;

/// The status of a command that wrote to a closed pipe (128 + SIGPIPE).
pub(crate) const BROKEN_PIPE: i32 = 141;

/// The streams of one command.
pub(crate) struct Io<'a> {
    pub stdin: &'a mut dyn Read,
    pub stdout: &'a mut dyn Write,
    pub stderr: &'a mut dyn Write,
}

/// What one command that does not stream wrote, and its exit status.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Output {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub status: i32,
}

impl Output {
    /// Add a `name: message` line to stderr and fail with `status`.
    fn fail(&mut self, name: &str, message: &str, status: i32) {
        self.stderr
            .extend_from_slice(format!("{name}: {message}\n").as_bytes());
        self.status = status;
    }

    /// Write the output to `io`; the command's status.
    fn deliver(self, name: &str, io: &mut Io) -> i32 {
        if let Err(error) = io.stdout.write_all(&self.stdout) {
            return broken(name, &error, io.stderr);
        }
        // A closed stderr loses only the messages.
        let _ = io.stderr.write_all(&self.stderr);
        self.status
    }
}

/// Write a `name: message` line to `stderr` (a closed stderr loses it).
fn message(stderr: &mut dyn Write, name: &str, message: &str) {
    let _ = writeln!(stderr, "{name}: {message}");
}

/// The status of a command whose output could not be written: a closed
/// pipe ends it as SIGPIPE ends a program; another error is reported.
fn broken(name: &str, error: &std::io::Error, stderr: &mut dyn Write) -> i32 {
    if error.kind() == std::io::ErrorKind::BrokenPipe {
        return BROKEN_PIPE;
    }
    message(stderr, name, &format!("write error: {}", reason(error)));
    1
}

/// A failed copy: reading the input or writing the output.
enum Failure {
    Read(std::io::Error),
    Write(std::io::Error),
}

/// Copy `from` to `to` as it arrives.
fn copy(from: &mut dyn Read, to: &mut dyn Write) -> Result<(), Failure> {
    let mut buffer = [0u8; 16 * 1024];
    loop {
        let read = match from.read(&mut buffer) {
            Ok(0) => return Ok(()),
            Ok(read) => read,
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(Failure::Read(error)),
        };
        to.write_all(&buffer[..read]).map_err(Failure::Write)?;
    }
}

/// GNU's wording of an I/O error.
fn reason(error: &std::io::Error) -> String {
    match error.kind() {
        std::io::ErrorKind::NotFound => "No such file or directory".to_string(),
        std::io::ErrorKind::PermissionDenied => "Permission denied".to_string(),
        std::io::ErrorKind::AlreadyExists => "File exists".to_string(),
        std::io::ErrorKind::IsADirectory => "Is a directory".to_string(),
        std::io::ErrorKind::NotADirectory => "Not a directory".to_string(),
        std::io::ErrorKind::DirectoryNotEmpty => "Directory not empty".to_string(),
        std::io::ErrorKind::BrokenPipe => "Broken pipe".to_string(),
        _ => error.to_string(),
    }
}

/// Single-letter flags from `args` while they are in `allowed`; the
/// operands after them (`--` ends the flags). `None` for any other flag.
fn flags<'a>(args: &'a [String], allowed: &str) -> Option<(String, Vec<&'a String>)> {
    let mut set = String::new();
    let mut operands = Vec::new();
    let mut ended = false;
    for arg in args {
        if ended || arg == "-" || !arg.starts_with('-') {
            operands.push(arg);
        } else if arg == "--" {
            ended = true;
        } else {
            for flag in arg[1..].chars() {
                if !allowed.contains(flag) {
                    return None;
                }
                set.push(flag);
            }
        }
    }
    Some((set, operands))
}

/// Run `words` in process on `io`: its exit status, or `None` (before
/// any I/O) when it needs the external program.
pub(crate) fn run(words: &[String], cwd: &Path, io: &mut Io) -> Option<i32> {
    let (name, args) = words.split_first()?;
    let done = |out: Output, io: &mut Io| out.deliver(name, io);
    match name.as_str() {
        "true" | ":" => Some(0),
        "false" => Some(1),
        "echo" => text::echo(args).map(|out| done(out, io)),
        "pwd" => args.is_empty().then(|| {
            let out = Output {
                stdout: format!("{}\n", cwd.display()).into_bytes(),
                ..Output::default()
            };
            done(out, io)
        }),
        "cat" => text::cat(args, cwd, io),
        "head" => text::head_tail(text::End::Head, args, cwd, io),
        "tail" => text::head_tail(text::End::Tail, args, cwd, io),
        "wc" => text::wc(args, cwd, io),
        "ls" => files::ls(args, cwd).map(|out| done(out, io)),
        "mkdir" => files::mkdir(args, cwd).map(|out| done(out, io)),
        "rm" => files::rm(args, cwd).map(|out| done(out, io)),
        "rmdir" => files::rmdir(args, cwd).map(|out| done(out, io)),
        "touch" => files::touch(args, cwd).map(|out| done(out, io)),
        "cp" => files::cp(args, cwd).map(|out| done(out, io)),
        "mv" => files::mv(args, cwd).map(|out| done(out, io)),
        "grep" => grep::grep(args, cwd, io),
        _ => None,
    }
}

/// [`run`] on `stdin`, with its output kept.
#[cfg(test)]
fn captured(words: &[String], cwd: &Path, stdin: &[u8]) -> Option<Output> {
    let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
    let status = run(
        words,
        cwd,
        &mut Io {
            stdin: &mut &stdin[..],
            stdout: &mut stdout,
            stderr: &mut stderr,
        },
    )?;
    Some(Output {
        stdout,
        stderr,
        status,
    })
}
