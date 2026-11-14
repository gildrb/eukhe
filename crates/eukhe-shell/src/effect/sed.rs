//! The `sed` row of the classification table: a `sed` step reads unless
//! it edits in place, and only while every script is a known-safe form.

use super::long;
use eukhe_types::shell::{ShellEffect, ShellEffects};

/// `sed` long options that only change how the script reads its input
/// (`--expression` and `--in-place` are checked apart).
const SED_LONG: &[&str] = &[
    "null-data",
    "posix",
    "quiet",
    "regexp-extended",
    "sandbox",
    "separate",
    "silent",
    "unbuffered",
    "zero-terminated",
];

/// The scripts given by option, the first operand and the in-place flag
/// of a `sed` step's arguments.
struct SedCall<'a> {
    scripts: Vec<&'a str>,
    first_operand: Option<&'a str>,
    in_place: bool,
}

/// The effects of `sed` with `args`: every script must be a known-safe
/// form, with no `e`, `r`, `w` command and no `e` or `w` flag of `s`.
pub(super) fn classify(args: &[String]) -> ShellEffects {
    let Some(mut call) = sed_call(args) else {
        return ShellEffects::of(&[ShellEffect::Exec]);
    };
    // Without `-e`, the first operand is the script.
    if call.scripts.is_empty() {
        match call.first_operand {
            Some(script) => call.scripts.push(script),
            None => return ShellEffects::of(&[ShellEffect::Read]),
        }
    }
    if !call.scripts.into_iter().all(known_script) {
        ShellEffects::of(&[ShellEffect::Exec])
    } else if call.in_place {
        ShellEffects::of(&[ShellEffect::Write])
    } else {
        ShellEffects::of(&[ShellEffect::Read])
    }
}

/// The options and operands of `args`; `None` when an option is unknown
/// or `-e` lacks its script.
fn sed_call(args: &[String]) -> Option<SedCall<'_>> {
    let mut call = SedCall {
        scripts: Vec::new(),
        first_operand: None,
        in_place: false,
    };
    let mut options_end = false;
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        if options_end || arg == "-" || !arg.starts_with('-') {
            call.first_operand.get_or_insert(arg);
        } else if arg == "--" {
            options_end = true;
        } else if arg.starts_with("--") {
            if long(arg, "in-place") {
                call.in_place = true;
            } else if long(arg, "expression") {
                match arg.split_once('=') {
                    Some((_, script)) => call.scripts.push(script),
                    None => call.scripts.push(rest.next()?),
                }
            } else if !SED_LONG.iter().any(|name| long(arg, name)) {
                return None;
            }
        } else {
            let flags = &arg[1..];
            for (at, flag) in flags.char_indices() {
                match flag {
                    'n' | 'E' | 'r' | 's' | 'u' | 'z' => {}
                    // The rest of the word is the backup suffix.
                    'i' => {
                        call.in_place = true;
                        break;
                    }
                    // The rest of the word, else the next word, is the
                    // script.
                    'e' => {
                        let attached = &flags[at + 1..];
                        if attached.is_empty() {
                            call.scripts.push(rest.next()?);
                        } else {
                            call.scripts.push(attached);
                        }
                        break;
                    }
                    _ => return None,
                }
            }
        }
    }
    Some(call)
}

/// Whether `script` holds only known-safe commands: print, delete, quit,
/// hold-space moves, blocks, `s` and `y` (with `s` flags that run and
/// write nothing).
fn known_script(script: &str) -> bool {
    let bytes = script.as_bytes();
    let mut at = 0;
    loop {
        while bytes
            .get(at)
            .is_some_and(|byte| matches!(byte, b' ' | b'\t' | b'\n' | b';'))
        {
            at += 1;
        }
        if at == bytes.len() {
            return true;
        }
        if address(bytes, &mut at) && bytes.get(at) == Some(&b',') {
            at += 1;
            if !address(bytes, &mut at) {
                return false;
            }
        }
        blank(bytes, &mut at);
        if bytes.get(at) == Some(&b'!') {
            at += 1;
            blank(bytes, &mut at);
        }
        let Some(&command) = bytes.get(at) else {
            return false;
        };
        at += 1;
        match command {
            b'{' => continue,
            b'=' | b'}' | b'd' | b'D' | b'g' | b'G' | b'h' | b'H' | b'n' | b'N' | b'p' | b'P'
            | b'q' | b'Q' | b'x' => {}
            b's' | b'y' => {
                let Some(&delimiter) = bytes.get(at) else {
                    return false;
                };
                if matches!(delimiter, b'\\' | b'\n') {
                    return false;
                }
                at += 1;
                if !(past(bytes, &mut at, delimiter) && past(bytes, &mut at, delimiter)) {
                    return false;
                }
                if command == b's' {
                    while bytes
                        .get(at)
                        .is_some_and(|flag| b"gimpIM0123456789".contains(flag))
                    {
                        at += 1;
                    }
                }
            }
            _ => return false,
        }
        // A command ends at a blank, `;`, a newline, `}` or the end of the
        // script.
        if !matches!(
            bytes.get(at),
            None | Some(b' ' | b'\t' | b'\n' | b';' | b'}')
        ) {
            return false;
        }
    }
}

/// Move `at` past the next `end` in `bytes` that no `\` escapes: false
/// when none follows.
fn past(bytes: &[u8], at: &mut usize, end: u8) -> bool {
    while let Some(&byte) = bytes.get(*at) {
        *at += 1;
        if byte == b'\\' {
            *at += 1;
        } else if byte == end {
            return true;
        }
    }
    false
}

/// Move `at` past an address (`N`, `$`, `/regex/`): false when none is
/// there.
fn address(bytes: &[u8], at: &mut usize) -> bool {
    match bytes.get(*at) {
        Some(byte) if byte.is_ascii_digit() => {
            while bytes.get(*at).is_some_and(u8::is_ascii_digit) {
                *at += 1;
            }
            true
        }
        Some(b'$') => {
            *at += 1;
            true
        }
        Some(b'/') => {
            *at += 1;
            past(bytes, at, b'/')
        }
        Some(_) | None => false,
    }
}

/// Move `at` past blanks.
fn blank(bytes: &[u8], at: &mut usize) {
    while bytes
        .get(*at)
        .is_some_and(|byte| matches!(byte, b' ' | b'\t'))
    {
        *at += 1;
    }
}
