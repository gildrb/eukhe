use std::{fs, num::NonZeroUsize, path::Path};

use tempfile::TempDir;

use super::*;
use crate::{file_hash, gate::Open};

fn request(pattern: &str, path: &str) -> GrepRequest {
    GrepRequest {
        pattern: pattern.to_owned(),
        path: path.to_owned(),
        glob: None,
        ignore_case: false,
        gitignore: true,
        context_before: 0,
        context_after: 0,
        skip: 0,
        limit: None,
    }
}

fn fixture(files: &[(&str, &str)]) -> TempDir {
    let directory = tempfile::tempdir().expect("temp directory");
    for (path, content) in files {
        let path = directory.path().join(path);
        fs::create_dir_all(path.parent().expect("fixture parent")).expect("fixture directory");
        fs::write(path, content).expect("fixture file");
    }
    directory
}

fn run(directory: &TempDir, request: &GrepRequest) -> GrepOutput {
    grep(&EditStore::new(), directory.path(), request, &Open).expect("grep succeeds")
}

#[test]
fn grouped_matches_have_folded_headers_tags_and_hashline_match_rows() {
    let alpha = "fn a() {}\nlet needle = 1;\n";
    let beta = "1\n2\n3\n4\n5\n6\n// needle\n";
    let directory = fixture(&[("dir/alpha.rs", alpha), ("dir/beta.rs", beta)]);
    let output = run(&directory, &request("needle", "dir"));
    assert_eq!(
        output.text,
        format!(
            "# dir/\n## alpha.rs#{}\n*2:let needle = 1;\n## beta.rs#{}\n*7:// needle",
            file_hash(alpha),
            file_hash(beta)
        )
    );
    assert!(output.multi_scope);
    assert!(output.notices.is_empty());
}

#[test]
fn single_file_match_has_hashline_header_and_no_group_heading() {
    let content = "a\nb\nc\nneedle();\n";
    let directory = fixture(&[("src/one.rs", content)]);
    let output = run(&directory, &request("needle", "src/one.rs"));
    assert_eq!(
        output.text,
        format!("[src/one.rs#{}]\n*4:needle();", file_hash(content))
    );
    assert!(!output.multi_scope);
}

#[test]
fn asymmetric_and_zero_context_preserve_source_order() {
    let content = "before 1\nbefore 2\nbefore 3\nneedle\nafter 1\nafter 2\nafter 3\nafter 4\n";
    let directory = fixture(&[("src/context.rs", content)]);
    let tag = file_hash(content);
    let asymmetric = run(
        &directory,
        &GrepRequest {
            context_before: 1,
            context_after: 3,
            ..request("needle", "src/context.rs")
        },
    );
    assert_eq!(
        asymmetric.text,
        format!(
            "[src/context.rs#{tag}]\n 3:before 3\n*4:needle\n 5:after 1\n 6:after 2\n 7:after 3"
        )
    );
    let zero = run(&directory, &request("needle", "src/context.rs"));
    assert_eq!(zero.text, format!("[src/context.rs#{tag}]\n*4:needle"));
}

#[test]
fn overlapping_context_shows_each_line_once_and_marks_gaps() {
    let content = "1\n2\n3\nneedle a\nneedle b\n6\n7\n8\n9\n10\n11\nneedle c\n";
    let directory = fixture(&[("f.rs", content)]);
    let output = run(
        &directory,
        &GrepRequest {
            context_before: 1,
            context_after: 2,
            ..request("needle", "f.rs")
        },
    );
    assert_eq!(
        output.text,
        format!(
            "[f.rs#{}]\n 3:3\n*4:needle a\n*5:needle b\n 6:6\n 7:7\n...\n 11:11\n*12:needle c",
            file_hash(content)
        )
    );
}

#[test]
fn line_ranged_target_restricts_matches_and_context_to_its_lines() {
    let content = "1\nneedle a\n3\n4\nneedle b\n6\n7\n8\nneedle c\n";
    let directory = fixture(&[("f.rs", content)]);
    let tag = file_hash(content);
    let ranged = |path: &str| {
        run(
            &directory,
            &GrepRequest {
                context_before: 1,
                context_after: 1,
                ..request("needle", path)
            },
        )
    };
    let output = ranged("f.rs:4-6");
    assert_eq!(
        output.text,
        format!("[f.rs#{tag}]\n 4:4\n*5:needle b\n 6:6")
    );
    assert!(!output.multi_scope);
    assert_eq!(
        ranged("f.rs:5-6").text,
        format!("[f.rs#{tag}]\n*5:needle b\n 6:6")
    );
    assert_eq!(
        ranged("f.rs:1-2,9").text,
        format!("[f.rs#{tag}]\n 1:1\n*2:needle a\n...\n*9:needle c")
    );
}

#[test]
fn line_ranged_target_reaches_matches_past_the_per_file_fetch() {
    let content: String = (1..=300)
        .map(|n| "needle ".to_owned() + &n.to_string() + "\n")
        .collect();
    let directory = fixture(&[("f.rs", &content)]);
    let output = run(&directory, &request("needle", "f.rs:250-251"));
    assert_eq!(
        output.text,
        format!(
            "[f.rs#{}]\n*250:needle 250\n*251:needle 251",
            file_hash(&content)
        )
    );
}

#[test]
fn line_ranges_apply_per_root() {
    let a = "needle 1\nneedle 2\nneedle 3\n";
    let b = "needle x\nneedle y\n";
    let directory = fixture(&[("a.rs", a), ("b.rs", b)]);
    let output = run(&directory, &request("needle", "a.rs:2-2;b.rs"));
    let lines: Vec<(&str, Vec<u32>)> = output
        .files
        .iter()
        .map(|file| {
            (
                file.path.as_str(),
                file.matches.iter().map(|m| m.line_number).collect(),
            )
        })
        .collect();
    assert_eq!(lines, [("a.rs", vec![2]), ("b.rs", vec![1, 2])]);
}

#[test]
fn bad_line_selectors_are_rejected() {
    let directory = fixture(&[("f.rs", "needle\n")]);
    let error = |path: &str| {
        grep(
            &EditStore::new(),
            directory.path(),
            &request("needle", path),
            &Open,
        )
        .unwrap_err()
        .to_string()
    };
    assert_eq!(
        error("f.rs:0"),
        "path entry \"f.rs:0\" has an invalid selector \":0\" — Line selector 0 is invalid; lines \
         are 1-indexed. Use :1."
    );
    assert_eq!(
        error("*.rs:1-2"),
        "Line-range selector requires a single file, not a glob: *.rs:1-2"
    );
}

#[test]
fn shown_rows_are_typed_and_the_snapshot_has_no_seen_lines() {
    let content = "1\nneedle\n3\n4\n5\n";
    let directory = fixture(&[("f.rs", content)]);
    let store = EditStore::new();
    let output = grep(
        &store,
        directory.path(),
        &GrepRequest {
            context_before: 1,
            context_after: 1,
            ..request("needle", "f.rs")
        },
        &Open,
    )
    .expect("grep succeeds");
    let absolute = &output.files[0].absolute;
    let head = store.head(absolute).expect("snapshot recorded");
    assert_eq!(
        (head.hash, head.seen_lines, &*head.text),
        (file_hash(content), None, content)
    );
    let rendered = output.render();
    let rendered: Vec<&str> = rendered.lines().collect();
    let rows: Vec<(u32, &str)> = output.files[0]
        .rows
        .iter()
        .map(|row| (row.line, rendered[row.at]))
        .collect();
    assert_eq!(rows, [(1, " 1:1"), (2, "*2:needle"), (3, " 3:3")]);
}

#[test]
fn twenty_file_window_emits_pagination_and_skip_returns_the_next_page() {
    let files: Vec<(String, &str)> = (1..=21)
        .map(|index| (format!("page/file-{index:02}.rs"), "needle\n"))
        .collect();
    let borrowed: Vec<(&str, &str)> = files
        .iter()
        .map(|(path, content)| (path.as_str(), *content))
        .collect();
    let directory = fixture(&borrowed);
    let tag = file_hash("needle\n");

    let first = run(&directory, &request("needle", "page"));
    let expected_files = (1..=20)
        .map(|index| format!("## file-{index:02}.rs#{tag}\n*1:needle"))
        .collect::<Vec<_>>()
        .join("\n");
    assert_eq!(first.text, format!("# page/\n{expected_files}"));
    assert_eq!(
        first.notices,
        [Notice {
            continuation: Some("skip=20".to_owned()),
            omitted: Some(Omitted {
                count: 1,
                unit: Unit::Files,
            }),
            ..Notice::info(NoticeKind::Pagination, "files 1-20 of 21".to_owned())
        }]
    );

    let second = run(
        &directory,
        &GrepRequest {
            skip: 20,
            ..request("needle", "page")
        },
    );
    assert_eq!(
        second.text,
        format!("# page/\n## file-21.rs#{tag}\n*1:needle")
    );
    assert!(second.notices.is_empty());
}

#[test]
fn skip_past_the_last_matching_file_has_empty_text_and_range_notice() {
    let directory = fixture(&[("page/one.rs", "needle\n"), ("page/two.rs", "needle\n")]);
    let output = run(
        &directory,
        &GrepRequest {
            skip: 2,
            ..request("needle", "page")
        },
    );
    assert_eq!(output.text, "");
    assert_eq!(
        output.notices,
        [Notice::warn(
            NoticeKind::RangeOutOfBounds,
            "skip=2 is past the end of 2 files".to_owned()
        )]
    );
}

#[test]
fn no_matches_renders_the_omp_message() {
    let directory = fixture(&[("src/lib.rs", "nothing\n")]);
    let output = run(&directory, &request("absent", "src"));
    assert_eq!(
        (output.text.as_str(), output.total_files),
        ("No matches found", 0)
    );
}

#[test]
fn faults_keep_the_omp_messages() {
    let directory = fixture(&[("live.txt", "needle\n")]);
    let store = EditStore::new();
    assert_eq!(
        grep(&store, directory.path(), &request("  ", "."), &Open),
        Err(GrepError::EmptyPattern)
    );
    let missing = grep(
        &store,
        directory.path(),
        &request("needle", "gone.txt; also/*.rs"),
        &Open,
    )
    .expect_err("all targets missing");
    assert_eq!(
        missing.to_string(),
        "Path not found: gone.txt, also/*.rs; list each target in the semicolon-delimited `path`"
    );
    assert_eq!(
        GrepError::TimedOut.to_string(),
        "Grep timed out after 30s; narrow paths or pattern, or scope with `glob` first"
    );
}

#[test]
fn missing_targets_fail_only_when_no_root_survives() {
    let directory = fixture(&[("live.txt", "needle\n")]);
    let output = run(&directory, &request("needle", "gone.txt; live.txt"));
    assert_eq!(output.files.len(), 1);
    assert_eq!(
        output.notices,
        [Notice::warn(
            NoticeKind::MissingPaths,
            "gone.txt".to_owned()
        )]
    );
    assert_eq!(
        output.render(),
        format!(
            "# live.txt#{}\n*1:needle\n<diag severity=\"warn\" kind=\"missing_paths\">gone.txt</diag>",
            file_hash("needle\n")
        )
    );
}

#[test]
fn an_existing_literal_semicolon_path_wins_over_root_splitting() {
    let directory = fixture(&[("semi;colon.txt", "needle\n")]);
    let output = run(&directory, &request("needle", "semi;colon.txt"));
    assert_eq!(
        (output.files[0].path.as_str(), output.multi_scope),
        ("semi;colon.txt", false)
    );
}

#[test]
fn overlapping_roots_show_each_line_once() {
    let directory = fixture(&[("a.txt", "needle a\n"), ("b.txt", "needle b\n")]);
    let output = run(&directory, &request("needle", "a.txt; a.txt; b.txt"));
    let paths: Vec<_> = output.files.iter().map(|file| file.path.as_str()).collect();
    assert_eq!(paths, ["a.txt", "b.txt"]);
    assert_eq!(output.files[0].matches.len(), 1);
}

#[test]
fn directory_results_follow_path_order() {
    let directory = fixture(&[
        ("b.txt", "needle\n"),
        ("a.txt", "needle\n"),
        ("sub/c.txt", "needle\n"),
    ]);
    let output = run(&directory, &request("needle", "."));
    let paths: Vec<_> = output.files.iter().map(|file| file.path.as_str()).collect();
    assert_eq!(paths, ["a.txt", "b.txt", "sub/c.txt"]);
}

#[test]
fn per_file_cap_keeps_twenty_matches_and_says_how_to_see_more() {
    let directory = fixture(&[
        ("hot.txt", &"needle\n".repeat(30)),
        ("cold.txt", "needle\n"),
    ]);
    let output = run(&directory, &request("needle", "."));
    let counts: Vec<_> = output
        .files
        .iter()
        .map(|file| (file.path.as_str(), file.matches.len()))
        .collect();
    assert_eq!(counts, [("cold.txt", 1), ("hot.txt", 20)]);
    assert!(output.per_file_limit_reached);
    assert_eq!(
        output.notices,
        [Notice {
            continuation: Some("path=hot.txt:21-".to_owned()),
            ..Notice::warn(
                NoticeKind::LimitReached,
                "hot.txt: 20 of 21+ matches shown; search hot.txt alone, or hot.txt:21-".to_owned()
            )
        }]
    );
    let next = run(&directory, &request("needle", "hot.txt:21-"));
    let lines: Vec<u32> = next.files[0]
        .matches
        .iter()
        .map(|matched| matched.line_number)
        .collect();
    assert_eq!(lines, (21..=30).collect::<Vec<_>>());
}

#[test]
fn gitignore_hides_ignored_files_unless_disabled_and_dotfiles_are_searched() {
    let directory = fixture(&[
        (".gitignore", "ignored.txt\n"),
        ("ignored.txt", "needle\n"),
        (".hidden.txt", "needle\n"),
        ("kept.txt", "needle\n"),
        (".git/config", "needle\n"),
    ]);
    let paths = |output: &GrepOutput| -> Vec<String> {
        output.files.iter().map(|file| file.path.clone()).collect()
    };
    assert_eq!(
        paths(&run(&directory, &request("needle", "."))),
        [".hidden.txt", "kept.txt"]
    );
    assert_eq!(
        paths(&run(
            &directory,
            &GrepRequest {
                gitignore: false,
                ..request("needle", ".")
            }
        )),
        [".hidden.txt", "ignored.txt", "kept.txt"]
    );
}

#[test]
fn glob_roots_and_glob_filters_select_files() {
    let directory = fixture(&[
        ("src/a.rs", "needle\n"),
        ("src/deep/b.rs", "needle\n"),
        ("src/c.ts", "needle\n"),
        ("node_modules/d.rs", "needle\n"),
    ]);
    let paths = |output: GrepOutput| -> Vec<String> {
        output.files.into_iter().map(|file| file.path).collect()
    };
    assert_eq!(
        paths(run(&directory, &request("needle", "src/*.rs"))),
        ["src/a.rs", "src/deep/b.rs"]
    );
    assert_eq!(
        paths(run(
            &directory,
            &GrepRequest {
                glob: Some("*.ts".to_owned()),
                ..request("needle", ".")
            }
        )),
        ["src/c.ts"]
    );
    assert_eq!(
        paths(run(&directory, &request("needle", "node_modules/*.rs"))),
        ["node_modules/d.rs"]
    );
}

#[test]
fn limit_takes_matches_round_robin_and_reports_the_cut() {
    let directory = fixture(&[("a.txt", "needle\nneedle\nneedle\n"), ("b.txt", "needle\n")]);
    let output = run(
        &directory,
        &GrepRequest {
            limit: NonZeroUsize::new(3),
            ..request("needle", ".")
        },
    );
    let counts: Vec<_> = output
        .files
        .iter()
        .map(|file| (file.path.as_str(), file.matches.len()))
        .collect();
    assert_eq!(counts, [("a.txt", 2), ("b.txt", 1)]);
    assert_eq!(
        output.notices,
        [Notice {
            continuation: Some("limit=6".to_owned()),
            ..Notice::info(
                NoticeKind::LimitReached,
                "3 result limit reached".to_owned()
            )
        }]
    );
}

#[test]
fn explicit_oversized_file_is_partially_scanned_and_untagged() {
    let mut large = b"needle in prefix\n".to_vec();
    large.resize(
        usize::try_from(MAX_SNAPSHOT_FILE_BYTES).expect("fits") + 1,
        b'x',
    );
    let directory = tempfile::tempdir().expect("temp directory");
    fs::write(directory.path().join("large.log"), large).expect("large file");
    let output = run(&directory, &request("needle", "large.log"));
    assert_eq!(output.text, "*1:needle in prefix");
    assert_eq!(output.files[0].tag, None);
    assert_eq!(
        output.notices,
        [
            Notice::warn(
                NoticeKind::PartialScan,
                "1 files over 4.0MB: only their first 4.0MB was searched: large.log".to_owned()
            ),
            Notice::warn(
                NoticeKind::NotEditable,
                "1 shown files have no tag, so `edit` cannot change them: large.log (over 4.0MB: `edit` cannot change it; read it in ranges, then change it with `write` (whole file) or `bash`)".to_owned()
            ),
        ]
    );
}

#[test]
fn binary_files_are_skipped_with_a_notice() {
    let directory = fixture(&[("bin.dat", "needle\0needle\n"), ("text.txt", "needle\n")]);
    let output = run(&directory, &request("needle", "."));
    let paths: Vec<_> = output.files.iter().map(|file| file.path.as_str()).collect();
    assert_eq!(paths, ["text.txt"]);
    let named = run(&directory, &request("needle", "bin.dat"));
    assert_eq!(
        (named.render(), named.account.binary),
        (
            "No matches found\n<diag severity=\"warn\" kind=\"skipped\">1 binary files (a NUL byte) not searched: bin.dat</diag>".to_owned(),
            1
        )
    );
}

#[test]
fn case_matching_is_explicit() {
    let directory = fixture(&[("f.txt", "Needle\n")]);
    assert_eq!(run(&directory, &request("needle", "f.txt")).total_files, 0);
    let insensitive = run(
        &directory,
        &GrepRequest {
            ignore_case: true,
            ..request("needle", "f.txt")
        },
    );
    assert_eq!(insensitive.total_files, 1);
}

#[test]
fn literal_backslash_n_matches_across_lines_and_shows_every_line() {
    let content = "zero\nalpha\nbeta\n";
    let directory = fixture(&[("f.txt", content)]);
    let output = run(&directory, &request(r"alpha\nbeta", "f.txt"));
    assert_eq!(
        output.text,
        format!("[f.txt#{}]\n*2:alpha\n*3:beta", file_hash(content))
    );
}

#[test]
fn long_lines_are_cut_after_512_bytes_with_a_marker() {
    let line = format!("needle {}", "x".repeat(600));
    let directory = fixture(&[("f.txt", &line)]);
    let output = run(&directory, &request("needle", "f.txt"));
    let matched = &output.files[0].matches[0];
    assert_eq!(
        (matched.line.as_str(), matched.truncated),
        (
            format!("needle {}…⟨+95 bytes⟩", "x".repeat(505)).as_str(),
            true
        )
    );
}

#[test]
fn invalid_regex_falls_back_to_literal() {
    for (pattern, hit, miss) in [
        ("foo[bar", &b"x foo[bar y"[..], &b"foobar"[..]),
        ("+++", &b"a+++b"[..], &b"ab"[..]),
        ("fail)", &b"(1 fail)"[..], &b"failure"[..]),
    ] {
        let matcher = engine::build_matcher(pattern, RegexOptions::default())
            .unwrap_or_else(|error| panic!("`{pattern}` should be literal: {error}"));
        assert!(grep_matcher_is_match(&matcher, hit), "{pattern} hit");
        assert!(!grep_matcher_is_match(&matcher, miss), "{pattern} miss");
    }
}

#[test]
fn stray_parenthesis_retry_preserves_surrounding_regex() {
    let matcher =
        engine::build_matcher("foo.*(bar", RegexOptions::default()).expect("parenthesis retry");
    assert!(grep_matcher_is_match(&matcher, b"fooXYZ(bar"));
    assert!(!grep_matcher_is_match(&matcher, b"foobar"));
}

#[test]
fn stray_braces_are_escaped_but_repetitions_and_escapes_stay() {
    let matcher = engine::build_matcher(r"fn main() {\s*x{2}\p{L}", RegexOptions::default())
        .expect("brace repair");
    assert!(grep_matcher_is_match(&matcher, b"fn main {  xxA"));
}

fn grep_matcher_is_match(matcher: &grep_regex::RegexMatcher, haystack: &[u8]) -> bool {
    let mut found = false;
    grep_searcher::Searcher::new()
        .search_slice(
            matcher,
            haystack,
            grep_searcher::sinks::Bytes(|_, _| {
                found = true;
                Ok(false)
            }),
        )
        .expect("search succeeds");
    found
}

#[test]
fn display_paths_outside_the_working_directory_stay_absolute() {
    let parent = fixture(&[("external.txt", "needle\n"), ("workspace/keep", "")]);
    let workspace = parent.path().join("workspace");
    let external = fs::canonicalize(parent.path().join("external.txt")).expect("canonical");
    let output = grep(
        &EditStore::new(),
        &workspace,
        &request("needle", external.to_str().expect("UTF-8 path")),
        &Open,
    )
    .expect("grep succeeds");
    assert_eq!(Path::new(&output.files[0].path), external.as_path());
}

/// The tag names the text the rows were cut from, even when the file
/// changes between the search and the record.
#[test]
fn tag_names_the_searched_text_when_the_file_changes_before_the_record() {
    let searched = "\u{FEFF}one\r\nneedle\r\n";
    let directory = fixture(&[("f.rs", searched)]);
    let path = directory.path().join("f.rs");
    let store = EditStore::new();
    let rewrite = || fs::write(&path, "changed\nneedle\nmore\n").expect("rewrite");
    let output = grep_with(
        &store,
        directory.path(),
        &request("needle", "f.rs"),
        &Open,
        GrepLimits::DEFAULT,
        &rewrite,
    )
    .expect("grep succeeds");
    let absolute = &output.files[0].absolute;
    assert_eq!(
        (
            output.files[0].tag.clone(),
            store.head(absolute).map(|head| head.text.to_string()),
            store.has_seen_bytes(absolute, searched.as_bytes()),
        ),
        (
            Some(file_hash("one\nneedle\n")),
            Some("one\nneedle\n".to_owned()),
            true
        )
    );
}

/// Rows strip only the line terminator: a trailing NBSP stays, `\r\n`
/// goes, and a BOM is not part of row 1.
#[test]
fn rows_keep_trailing_characters_other_than_the_terminator() {
    let directory = fixture(&[("f.txt", "\u{FEFF}needle\u{A0}\r\nneedle \nneedle\r")]);
    let output = run(&directory, &request("needle", "f.txt"));
    let lines: Vec<&str> = output.files[0]
        .matches
        .iter()
        .map(|matched| matched.line.as_str())
        .collect();
    assert_eq!(lines, ["needle\u{A0}", "needle ", "needle\r"]);
}

/// When the total match cap stops the search, the files after it are not
/// searched, a notice says so, and the file count is a lower bound.
#[test]
fn total_cap_marks_the_file_count_as_a_lower_bound() {
    let files: Vec<(String, &str)> = (1..=22)
        .map(|index| (format!("f{index:02}.txt"), "needle\n"))
        .collect();
    let borrowed: Vec<(&str, &str)> = files
        .iter()
        .map(|(path, content)| (path.as_str(), *content))
        .collect();
    let directory = fixture(&borrowed);
    let output = grep_with(
        &EditStore::new(),
        directory.path(),
        &request("needle", "."),
        &Open,
        GrepLimits {
            total_matches: 21,
            ..GrepLimits::DEFAULT
        },
        &|| {},
    )
    .expect("grep succeeds");
    assert_eq!(
        (
            output.total_files,
            output.total_files_lower_bound,
            output.account.not_searched
        ),
        (21, true, 1)
    );
    assert_eq!(
        output.notices,
        [
            Notice::warn(
                NoticeKind::LimitReached,
                "1 files not searched: the 21-match total was reached; narrow the path or the pattern"
                    .to_owned()
            ),
            Notice {
                continuation: Some("skip=20".to_owned()),
                omitted: Some(Omitted {
                    count: 1,
                    unit: Unit::Files,
                }),
                ..Notice::info(NoticeKind::Pagination, "files 1-20 of 21+".to_owned())
            },
        ]
    );
}

/// Excluded directories, symlinks, and eukhe temporary files: the first
/// two get notices and are counted; temporary files are hidden.
#[test]
fn walk_skips_are_counted_and_temporary_files_are_hidden() {
    let directory = fixture(&[
        ("a.txt", "needle\n"),
        ("node_modules/m.txt", "needle\n"),
        (".git/config", "needle\n"),
        (".eukhe-tmp-0123456789abcdef-1-0", "needle\n"),
    ]);
    std::os::unix::fs::symlink(
        directory.path().join("a.txt"),
        directory.path().join("link.txt"),
    )
    .expect("symlink");
    let output = run(
        &directory,
        &GrepRequest {
            gitignore: false,
            ..request("needle", ".")
        },
    );
    let paths: Vec<_> = output.files.iter().map(|file| file.path.as_str()).collect();
    assert_eq!(paths, ["a.txt"]);
    assert_eq!(
        output.notices,
        [
            Notice::warn(
                NoticeKind::Skipped,
                "2 excluded directories not searched (`.git` always; `node_modules` unless the path or glob names it): .git, node_modules".to_owned()
            ),
            Notice::warn(
                NoticeKind::Skipped,
                "1 symlinks not followed (name the target path to search it): link.txt".to_owned()
            ),
        ]
    );
    assert_eq!(
        output.account,
        GrepAccount {
            shown: 1,
            excluded: 2,
            symlink: 1,
            ..GrepAccount::default()
        }
    );
}

/// Whether this process can read a file that has no permissions (root
/// can, so the permission tests have nothing to check).
fn reads_without_permission(path: &Path) -> bool {
    fs::read_dir(path).is_ok() || fs::read(path).is_ok()
}

/// An unreadable file and an unreadable directory are counted with a
/// notice each, and the search goes on.
#[test]
fn unreadable_files_and_walk_errors_get_notices() {
    use std::os::unix::fs::PermissionsExt as _;
    let directory = fixture(&[
        ("a.txt", "needle\n"),
        ("locked.txt", "needle\n"),
        ("closed/b.txt", "needle\n"),
    ]);
    let locked = directory.path().join("locked.txt");
    let closed = directory.path().join("closed");
    fs::set_permissions(&locked, fs::Permissions::from_mode(0o000)).expect("chmod");
    fs::set_permissions(&closed, fs::Permissions::from_mode(0o000)).expect("chmod");
    if reads_without_permission(&locked) || reads_without_permission(&closed) {
        return;
    }
    let output = run(&directory, &request("needle", "."));
    fs::set_permissions(&closed, fs::Permissions::from_mode(0o755)).expect("chmod back");
    let kinds_and_starts: Vec<(NoticeKind, String)> = output
        .notices
        .iter()
        .map(|notice| {
            (
                notice.kind,
                notice.text.split(':').next().unwrap_or("").to_owned(),
            )
        })
        .collect();
    assert_eq!(
        kinds_and_starts,
        [
            (
                NoticeKind::Skipped,
                "1 unreadable files not searched".to_owned()
            ),
            (
                NoticeKind::Skipped,
                "1 walk errors (these entries were not searched)".to_owned()
            ),
        ]
    );
    assert_eq!(
        output.account,
        GrepAccount {
            shown: 1,
            unreadable: 1,
            walk_error: 1,
            ..GrepAccount::default()
        }
    );
}

/// A shown file that is not UTF-8 has no tag, and a notice says why.
#[test]
fn shown_non_utf8_file_says_it_is_not_editable() {
    let directory = tempfile::tempdir().expect("temp directory");
    fs::write(directory.path().join("latin.txt"), b"needle caf\xE9\n").expect("file");
    let output = run(&directory, &request("needle", "latin.txt"));
    assert_eq!(
        (output.files[0].tag.clone(), output.notices),
        (
            None,
            vec![Notice::warn(
                NoticeKind::NotEditable,
                "1 shown files have no tag, so `edit` cannot change them: latin.txt (not UTF-8: `edit` works on UTF-8 only; `write` replaces it as UTF-8)".to_owned()
            )]
        )
    );
}

/// Every walked entry lands in exactly one class of the account.
#[test]
fn account_partitions_the_walked_files() {
    let mut files: Vec<(String, String)> = (1..=23)
        .map(|index| (format!("m{index:02}.txt"), "needle\n".to_owned()))
        .collect();
    files.push(("none.txt".to_owned(), "other\n".to_owned()));
    files.push(("bin.dat".to_owned(), "needle\0\n".to_owned()));
    let borrowed: Vec<(&str, &str)> = files
        .iter()
        .map(|(path, content)| (path.as_str(), content.as_str()))
        .collect();
    let directory = fixture(&borrowed);
    let output = run(&directory, &request("needle", "."));
    assert_eq!(
        output.account,
        GrepAccount {
            no_match: 1,
            shown: 20,
            paged_out: 3,
            binary: 1,
            ..GrepAccount::default()
        }
    );
}
