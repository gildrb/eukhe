//! Grep's rows against read's, and grep's tags on a file rewritten during
//! the search.
//!
//! Rows: read's rows are the compiled core's decision over the scan of the
//! file (`bend/doc_rows.bend`, law `rows_lines_are_read_rows`); grep's
//! come from the search engine. Generated bodies of content bytes, `\r`,
//! `\n` and `\r\n` (not empty), with or without a BOM, read with
//! [`Documents::read`] and searched with the pattern `^`, show the same
//! rows (the model's law `grep_line_is_read_line`, here on the real code).
//!
//! Tags (`bend/doc_tags.bend`, laws `tag_names_shown_text` and
//! `grep_tag_fates_spec`; the choice runs as the compiled core,
//! `bend/ffi_doc_tags.bend`): a file holds version 1 when grep searches it
//! and version 2 when grep records it ([`grep_with`]'s `between`); the tag
//! and the rows name version 1, the searched text.

use std::fmt::Write as _;
use std::path::Path;

use super::{grep_with, GrepLimits, GrepOutput, GrepRequest};
use crate::read::ReadContent;
use crate::store::EditStore;
use crate::testing::Rng;
use crate::text::lf_text;
use crate::Documents;

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

/// The rows read and grep show of a file holding `bytes`.
fn read_and_grep(dir: &Path, bytes: &str) -> [Vec<(u32, String)>; 2] {
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
    let rendered = output.render();
    let grep = output
        .files
        .iter()
        .flat_map(|grep_file| rows_of(&rendered, &grep_file.rows))
        .collect();
    [rows_of(&view.rendered, &file.rows), grep]
}

/// Read and grep show the same rows on 100 bodies: lone `\r` (also before
/// `\r\n` and at the end), mixed `\n` and `\r\n` endings, a final newline or
/// not, a BOM.
#[test]
fn read_and_grep_show_the_same_rows() {
    let mut rng = Rng(0x6e9e_1a5e_7a95_0003);
    let dir = tempfile::tempdir().unwrap();
    for at in 0..100 {
        let bom = rng.below(2) == 1;
        let mut bytes = if bom { BOM.to_owned() } else { String::new() };
        for _ in 0..rng.range(1, 10) {
            bytes.push_str(match rng.below(4) {
                0 => "a",
                1 => "\r",
                2 => "\n",
                3.. => "\r\n",
            });
        }
        let [read, grep] = read_and_grep(&dir.path().join(at.to_string()), &bytes);
        assert_eq!(read, grep, "{bytes:?}");
    }
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
        tags.record(&path, &lf_text(text), None)
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

/// The tag of a grep result and its rows name the searched version when
/// the file is rewritten between the search and the record, on 30
/// rewrites of 1 to 12 lines.
#[test]
fn a_grep_tag_names_the_searched_text() {
    let mut rng = Rng(0x7a95_5ea2_c4ed_0002);
    let dir = tempfile::tempdir().unwrap();
    for at in 0..30 {
        let lines = [rng.range(1, 12), rng.range(1, 12)];
        assert_eq!(
            rewritten(&dir.path().join(at.to_string()), lines),
            "t 1\nr 1\n",
            "{lines:?}"
        );
    }
}
