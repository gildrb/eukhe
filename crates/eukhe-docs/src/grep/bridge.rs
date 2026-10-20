//! Two bridges from grep to the documents models.
//!
//! Rows (`bend/doc_lines.bend`, law `grep_line_is_read_line` of
//! `laws/documents.bend`): generated bodies of content bytes, `\r`, `\n`
//! and `\r\n` (not empty), with or without a BOM, are read with
//! [`Documents::read`] and searched with the pattern `^`, and
//! `bend/bridge_doc_rows.bend` must print the same rows. A scenario line is
//! `M BODY` (M: 1 for a BOM; BODY: `a`, `r`, `n` for each byte); it prints
//! `r N TEXT` for each row of read, then `g N TEXT` for each row of grep
//! (TEXT: `a` and `r` for each byte, `-` when empty).
//!
//! Tags (`bend/doc_tags.bend`, law `tag_names_shown_text`): a file holds
//! version 1 (N1 lines) when grep searches it and version 2 (N2 lines)
//! when grep records it ([`grep_with`]'s `between`). A scenario line is
//! `N1 N2`; it prints `t V` (the versions whose text has the tag of the
//! result) and `r V` (the versions whose lines are the rows).

use std::fmt::Write as _;
use std::path::Path;

use super::{grep_with, GrepLimits, GrepOutput, GrepRequest};
use crate::read::ReadContent;
use crate::store::EditStore;
use crate::testing::{compare, Rng, Scenario};
use crate::text::{normalize_to_lf, strip_bom};
use crate::Documents;

const ROWS_MODEL: &str = "bend/bridge_doc_rows.bend";
const TAGS_MODEL: &str = "bend/bridge_doc_tags.bend";
const BOM: &str = "\u{FEFF}";

/// A request for every line of `path`.
fn every_line(path: &str) -> GrepRequest {
    GrepRequest {
        pattern: "^".to_owned(),
        path: path.to_owned(),
        glob: None,
        ignore_case: false,
        gitignore: false,
        context_before: 0,
        context_after: 0,
        skip: 0,
        limit: None,
    }
}

/// The text of a row as the model writes it.
fn escaped(text: &str) -> String {
    if text.is_empty() {
        return "-".to_owned();
    }
    text.chars()
        .map(|char| match char {
            'a' => 'a',
            '\r' => 'r',
            '\n' => 'n',
            _ => '?',
        })
        .collect()
}

/// `(line, text)` of each row at its place in `rendered`: the text after
/// the row's `N:` (grep: `*N:`).
fn rows_of(rendered: &str, rows: &[crate::read::Row]) -> Vec<(u32, String)> {
    let lines: Vec<&str> = rendered.split('\n').collect();
    rows.iter()
        .map(|row| {
            let (_, text) = lines[row.at].split_once(':').unwrap();
            (row.line, text.to_owned())
        })
        .collect()
}

/// The rows read and grep show of a file holding `bytes`, as the model
/// prints them.
fn read_and_grep(dir: &Path, bytes: &str) -> String {
    let cwd = dir.join("w");
    std::fs::create_dir_all(&cwd).unwrap();
    std::fs::write(cwd.join("f.txt"), bytes).unwrap();
    let docs = Documents::new(dir.join("locks"), None);
    let view = docs.read(&cwd, "f.txt", &crate::gate::Open).unwrap();
    let ReadContent::File(file) = &view.content else {
        panic!("f.txt is a file");
    };
    let output = grep_with(
        docs.store(),
        &cwd,
        &every_line("f.txt"),
        &crate::gate::Open,
        GrepLimits::DEFAULT,
        &|| {},
    )
    .unwrap();
    let mut printed = String::new();
    for (line, text) in rows_of(&view.rendered, &file.rows) {
        let _ = writeln!(printed, "r {line} {}", escaped(&text));
    }
    let rendered = output.render();
    for grep_file in &output.files {
        for (line, text) in rows_of(&rendered, &grep_file.rows) {
            let _ = writeln!(printed, "g {line} {}", escaped(&text));
        }
    }
    printed
}

/// Read and grep show the same rows, as the model's two splitters do, on
/// 100 scenarios of 1 to 4 bodies: lone `\r` (also before `\r\n` and at
/// the end), mixed `\n` and `\r\n` endings, a final newline or not, a BOM.
#[test]
fn read_and_grep_rows_equal_the_bend_model() {
    let mut rng = Rng(0x6e9e_1a5e_7a95_0003);
    let dir = tempfile::tempdir().unwrap();
    let scenarios = (0..100).map(|at| {
        let mut events = Vec::new();
        let mut transcript = String::new();
        for index in 0..rng.range(1, 4) {
            let bom = rng.below(2) == 1;
            let mut body = String::new();
            for _ in 0..rng.range(1, 10) {
                body.push_str(match rng.below(4) {
                    0 => "a",
                    1 => "\r",
                    2 => "\n",
                    3.. => "\r\n",
                });
            }
            let bytes = if bom {
                format!("{BOM}{body}")
            } else {
                body.clone()
            };
            transcript.push_str(&read_and_grep(
                &dir.path().join(format!("{at}-{index}")),
                &bytes,
            ));
            events.push(format!("{} {}", u8::from(bom), escaped(&body)));
        }
        Scenario {
            name: format!("rows-{at}"),
            events: events.join("\n"),
            transcript,
        }
    });
    compare(ROWS_MODEL, scenarios.collect::<Vec<_>>());
}

/// Version `v` of the file: `lines` lines `vV lI`.
fn version(v: u64, lines: u64) -> String {
    let mut text = String::new();
    for line in 1..=lines {
        let _ = writeln!(text, "v{v} l{line}");
    }
    text
}

/// The versions (1, 2) for which `holds` is true, as ` 1 2`.
fn which(holds: impl Fn(u64) -> bool) -> String {
    let mut out = String::new();
    for v in [1, 2] {
        if holds(v) {
            let _ = write!(out, " {v}");
        }
    }
    out
}

/// What the tag and the rows of a grep name when the file changes from
/// version 1 to version 2 between the search and the record.
fn rewritten(dir: &Path, lines: [u64; 2]) -> String {
    let cwd = dir.join("w");
    std::fs::create_dir_all(&cwd).unwrap();
    let path = cwd.join("f.txt");
    let texts = [version(1, lines[0]), version(2, lines[1])];
    std::fs::write(&path, &texts[0]).unwrap();
    let store = EditStore::new();
    let output: GrepOutput = grep_with(
        &store,
        &cwd,
        &every_line("f.txt"),
        &crate::gate::Open,
        GrepLimits::DEFAULT,
        &|| std::fs::write(&path, &texts[1]).unwrap(),
    )
    .unwrap();
    let file = &output.files[0];
    let tags = EditStore::new();
    let tag_of = |v: u64| {
        let text = &texts[usize::try_from(v - 1).unwrap()];
        tags.record(&path, &normalize_to_lf(strip_bom(text).1), None)
    };
    let rows = rows_of(&output.render(), &file.rows);
    let rows_of_version = |v: u64| {
        let text = &texts[usize::try_from(v - 1).unwrap()];
        let source: Vec<&str> = text.lines().collect();
        rows.len() == source.len()
            && rows.iter().all(|(line, row)| {
                source.get(usize::try_from(*line).unwrap() - 1) == Some(&row.as_str())
            })
    };
    format!(
        "t{}\nr{}\n",
        which(|v| file.tag.as_deref() == Some(tag_of(v).as_str())),
        which(rows_of_version)
    )
}

/// The tag of a grep result names the version its rows come from, as the
/// model's result does, when the file is rewritten between the search and
/// the record, on 30 scenarios of 1 to 3 rewrites of 1 to 12 lines.
#[test]
fn a_grep_tag_names_the_searched_text_as_the_bend_model() {
    let mut rng = Rng(0x7a95_5ea2_c4ed_0002);
    let dir = tempfile::tempdir().unwrap();
    let scenarios = (0..30).map(|at| {
        let mut events = Vec::new();
        let mut transcript = String::new();
        for index in 0..rng.range(1, 3) {
            let lines = [rng.range(1, 12), rng.range(1, 12)];
            transcript.push_str(&rewritten(&dir.path().join(format!("{at}-{index}")), lines));
            events.push(format!("{} {}", lines[0], lines[1]));
        }
        Scenario {
            name: format!("tags-{at}"),
            events: events.join("\n"),
            transcript,
        }
    });
    compare(TAGS_MODEL, scenarios.collect::<Vec<_>>());
}
