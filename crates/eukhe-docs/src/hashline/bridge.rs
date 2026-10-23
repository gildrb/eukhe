//! The bridge from a real read and hashline edit to the line model
//! (`bend/doc_lines.bend`, laws `load_persist_roundtrip` and
//! `edit_keeps_untouched_bytes` of `LAWS.bend` section `documents`): generated files
//! of content bytes, `\r`, `\n` and `\r\n`, with or without a BOM, get one
//! generated edit through [`Documents::read`] and [`Documents::edit`], and
//! `bridge/bridge_doc_lines.bend` must print the bytes the edit wrote, byte
//! for byte.
//!
//! A scenario file (no trailing newline) has one file and edit a line:
//! `M BODY OP ARGS` (see the model's header). Each prints the bytes on
//! disk after the edit: `B` for a BOM, then `a`, `r`, `n` for each byte
//! (`-` for an empty body).

use crate::read::ReadContent;
use crate::testing::{compare, Rng, Scenario};
use crate::Documents;

const MODEL: &str = "bridge/bridge_doc_lines.bend";
const BOM: &[u8] = b"\xEF\xBB\xBF";

/// One generated edit: the model's words and the hashline op.
struct Op {
    words: String,
    payload: String,
}

/// New line `i` of an edit: 10 + i content bytes, unlike every line of a
/// generated body.
fn news(count: u64) -> String {
    let mut rows = String::new();
    for at in 0..count {
        rows.push_str("\n+");
        rows.push_str(&"a".repeat(10 + usize::try_from(at).unwrap()));
    }
    rows
}

/// A random edit of a body whose read shows `lines` lines.
fn op(rng: &mut Rng, lines: u64, empty: bool) -> Op {
    let start = rng.range(1, lines);
    let end = rng.range(start, lines);
    let count = rng.range(1, 3);
    let choice = if empty { rng.below(5) } else { rng.below(6) };
    let (words, header) = match choice {
        0 => (
            format!("p {start} {end} {count}"),
            format!("PUT {start}.={end}:"),
        ),
        1 if start > 1 => (format!("b {start} {count}"), format!("PUT <{start}:")),
        1 | 3 => (format!("h {count}"), "PUT <1:".to_owned()),
        2 => (format!("a {start} {count}"), format!("PUT >{start}:")),
        4 => (format!("t {count}"), "PUT >$:".to_owned()),
        5.. => {
            return Op {
                words: format!("c {start} {end}"),
                payload: format!("CUT {start}.={end}"),
            }
        }
    };
    Op {
        words,
        payload: format!("{header}{}", news(count)),
    }
}

/// The bytes as the model writes them.
fn escaped(bytes: &[u8]) -> String {
    let (mut out, body) = match bytes.strip_prefix(BOM) {
        Some(body) => ("B".to_owned(), body),
        None => (String::new(), bytes),
    };
    if body.is_empty() {
        out.push('-');
    }
    for byte in body {
        out.push(match byte {
            b'\r' => 'r',
            b'\n' => 'n',
            b'a' => 'a',
            _ => '?',
        });
    }
    out
}

/// One generated file and edit: the model's words and the bytes the real
/// read and edit leave on disk.
fn case(rng: &mut Rng, dir: &std::path::Path) -> (String, String) {
    let bom = rng.below(2) == 1;
    let mut body = Vec::new();
    for _ in 0..rng.below(9) {
        body.extend_from_slice(match rng.below(4) {
            0 => b"a".as_slice(),
            1 => b"\r",
            2 => b"\n",
            3.. => b"\r\n",
        });
    }
    let mut bytes = if bom { BOM.to_vec() } else { Vec::new() };
    bytes.extend_from_slice(&body);
    let cwd = dir.join("w");
    std::fs::create_dir_all(&cwd).unwrap();
    let path = cwd.join("f.txt");
    std::fs::write(&path, &bytes).unwrap();
    let docs = Documents::new(dir.join("locks"), None);
    let view = docs.read(&cwd, "f.txt", &crate::gate::Open).unwrap();
    let ReadContent::File(file) = &view.content else {
        panic!("f.txt is a file");
    };
    let lines: Vec<u32> = file.rows.iter().map(|row| row.line).collect();
    let tag = file.tag.clone().unwrap();
    docs.mark_seen(&view.absolute, &tag, &lines);
    let op = op(rng, u64::try_from(lines.len()).unwrap(), body.is_empty());
    docs.edit(
        &cwd,
        &format!("[f.txt#{tag}]\n{}", op.payload),
        &crate::gate::Open,
    )
    .unwrap_or_else(|error| panic!("{} {}: {error}", escaped(&bytes), op.words));
    let words = format!("{} {} {}", u8::from(bom), escaped(&body), op.words);
    (words, escaped(&std::fs::read(&path).unwrap()) + "\n")
}

/// A real read and hashline edit write the bytes the model persists on 60
/// scenarios of 1 to 5 files: lone `\r`, mixed `\n` and `\r\n` endings, a
/// BOM, no final newline, and replace, insert, cut, start and end edits.
#[test]
fn a_real_edit_writes_the_bytes_of_the_bend_model() {
    let mut rng = Rng(0x11e5_d0c5_ed17_0004);
    let dir = tempfile::tempdir().unwrap();
    let scenarios = (0..60).map(|at| {
        let mut events = Vec::new();
        let mut transcript = String::new();
        for index in 0..rng.range(1, 5) {
            let (words, printed) = case(&mut rng, &dir.path().join(format!("{at}-{index}")));
            events.push(words);
            transcript.push_str(&printed);
        }
        Scenario {
            name: format!("lines-{at}"),
            events: events.join("\n"),
            transcript,
        }
    });
    compare(MODEL, scenarios.collect::<Vec<_>>());
}
