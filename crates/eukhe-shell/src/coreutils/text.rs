//! `echo`, `cat`, `head`, `tail`, `wc`. The last four stream their input.

use std::collections::VecDeque;
use std::io::{BufRead, BufReader, Read};
use std::path::Path;

use super::{broken, copy, flags, message, reason, Failure, Io, Output};

pub(super) fn echo(args: &[String]) -> Option<Output> {
    let (newline, words) = match args.first().map(String::as_str) {
        Some("-n") => (false, &args[1..]),
        Some(first) if first.starts_with('-') && first.len() > 1 => return None,
        Some(_) | None => (true, args),
    };
    let mut stdout = words.join(" ").into_bytes();
    if newline {
        stdout.push(b'\n');
    }
    Some(Output {
        stdout,
        ..Output::default()
    })
}

/// One operand's input: stdin for `-`, else the opened file.
enum Input<'a> {
    Stdin(&'a mut dyn Read),
    File(std::fs::File),
}

impl Input<'_> {
    fn reader(&mut self) -> &mut dyn Read {
        match self {
            Input::Stdin(stdin) => &mut **stdin,
            Input::File(file) => file,
        }
    }
}

/// Open `operand` (`-` is stdin).
fn open<'a>(operand: &str, cwd: &Path, stdin: &'a mut dyn Read) -> std::io::Result<Input<'a>> {
    if operand == "-" {
        return Ok(Input::Stdin(stdin));
    }
    std::fs::File::open(cwd.join(operand)).map(Input::File)
}

pub(super) fn cat(args: &[String], cwd: &Path, io: &mut Io) -> Option<i32> {
    let (_, operands) = flags(args, "")?;
    let dash = "-".to_string();
    let operands = if operands.is_empty() {
        vec![&dash]
    } else {
        operands
    };
    let mut status = 0;
    for operand in operands {
        let copied = match open(operand, cwd, io.stdin) {
            Ok(mut input) => copy(input.reader(), io.stdout),
            Err(error) => Err(Failure::Read(error)),
        };
        match copied {
            Ok(()) => {}
            Err(Failure::Write(error)) => return Some(broken("cat", &error, io.stderr)),
            Err(Failure::Read(error)) => {
                message(io.stderr, "cat", &format!("{operand}: {}", reason(&error)));
                status = 1;
            }
        }
    }
    Some(status)
}

/// Which end of the input `head`/`tail` keeps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum End {
    Head,
    Tail,
}

/// `head`/`tail` with `-n N`, `-nN`, `-N`, on one operand or stdin.
/// `head` reads only the lines it writes.
pub(super) fn head_tail(end: End, args: &[String], cwd: &Path, io: &mut Io) -> Option<i32> {
    let mut count = 10usize;
    let mut operands = Vec::new();
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        if arg == "-n" {
            count = rest.next()?.parse().ok()?;
        } else if let Some(value) = arg.strip_prefix("-n") {
            count = value.parse().ok()?;
        } else if arg.len() > 1 && arg.starts_with('-') {
            count = arg[1..].parse().ok()?;
        } else {
            operands.push(arg.as_str());
        }
    }
    let name = match end {
        End::Head => "head",
        End::Tail => "tail",
    };
    let operand = match operands.as_slice() {
        [] => "-",
        [one] => one,
        [_, _, ..] => return None,
    };
    let mut input = match open(operand, cwd, io.stdin) {
        Ok(input) => input,
        Err(error) => {
            let text = format!("cannot open '{operand}' for reading: {}", reason(&error));
            message(io.stderr, name, &text);
            return Some(1);
        }
    };
    let mut lines = BufReader::new(input.reader());
    let mut kept: VecDeque<Vec<u8>> = VecDeque::new();
    let mut taken = 0;
    while end == End::Tail || taken < count {
        let mut line = Vec::new();
        match lines.read_until(b'\n', &mut line) {
            Ok(0) => break,
            Ok(_) => {}
            Err(error) => {
                message(io.stderr, name, &format!("{operand}: {}", reason(&error)));
                return Some(1);
            }
        }
        taken += 1;
        match end {
            End::Head => {
                if let Err(error) = io.stdout.write_all(&line) {
                    return Some(broken(name, &error, io.stderr));
                }
            }
            End::Tail => {
                kept.push_back(line);
                if kept.len() > count {
                    kept.pop_front();
                }
            }
        }
    }
    for line in kept {
        if let Err(error) = io.stdout.write_all(&line) {
            return Some(broken(name, &error, io.stderr));
        }
    }
    Some(0)
}

/// `wc` with one of `-l`, `-w`, `-c` on one operand or stdin.
pub(super) fn wc(args: &[String], cwd: &Path, io: &mut Io) -> Option<i32> {
    let (set, operands) = flags(args, "lwc")?;
    if set.len() != 1 || operands.len() > 1 {
        return None;
    }
    let operand = operands.first().map_or("-", |operand| operand.as_str());
    let mut input = match open(operand, cwd, io.stdin) {
        Ok(input) => input,
        Err(error) => {
            message(io.stderr, "wc", &format!("{operand}: {}", reason(&error)));
            return Some(1);
        }
    };
    let (mut lines, mut words, mut bytes) = (0usize, 0usize, 0usize);
    let mut in_word = false;
    let mut buffer = [0u8; 16 * 1024];
    loop {
        let read = match input.reader().read(&mut buffer) {
            Ok(0) => break,
            Ok(read) => read,
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => {
                message(io.stderr, "wc", &format!("{operand}: {}", reason(&error)));
                return Some(1);
            }
        };
        bytes += read;
        for &byte in &buffer[..read] {
            lines += usize::from(byte == b'\n');
            let space = byte.is_ascii_whitespace();
            words += usize::from(!space && !in_word);
            in_word = !space;
        }
    }
    let count = match set.as_str() {
        "l" => lines,
        "w" => words,
        _ => bytes,
    };
    let line = if operand == "-" {
        format!("{count}\n")
    } else {
        format!("{count} {operand}\n")
    };
    match io.stdout.write_all(line.as_bytes()) {
        Ok(()) => Some(0),
        Err(error) => Some(broken("wc", &error, io.stderr)),
    }
}
