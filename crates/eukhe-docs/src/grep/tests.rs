use std::{collections::BTreeSet, fs, num::NonZeroUsize, path::Path};

use tempfile::TempDir;

use super::*;
use crate::{file_hash, notice::Severity};

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
    grep(&EditStore::new(), directory.path(), request).expect("grep succeeds")
}

fn kinds(output: &GrepOutput) -> Vec<(Severity, NoticeKind)> {
    output
        .notices
        .iter()
        .map(|notice| (notice.severity, notice.kind))
        .collect()
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
fn shown_rows_are_recorded_as_seen_lines_of_the_tagged_snapshot() {
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
    )
    .expect("grep succeeds");
    let absolute = &output.files[0].absolute;
    let head = store.head(absolute).expect("snapshot recorded");
    assert_eq!(
        (head.hash, head.seen_lines, &*head.text),
        (file_hash(content), Some(BTreeSet::from([1, 2, 3])), content)
    );
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
        grep(&store, directory.path(), &request("  ", ".")),
        Err(GrepError::EmptyPattern)
    );
    let missing = grep(
        &store,
        directory.path(),
        &request("needle", "gone.txt; also/*.rs"),
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
fn per_file_cap_keeps_twenty_matches_in_multi_file_scope() {
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
    large.resize(usize::try_from(MAX_FILE_BYTES).expect("fits") + 1, b'x');
    let directory = tempfile::tempdir().expect("temp directory");
    fs::write(directory.path().join("large.log"), large).expect("large file");
    let output = run(&directory, &request("needle", "large.log"));
    assert_eq!(output.text, "*1:needle in prefix");
    assert_eq!(output.files[0].tag, None);
    assert_eq!(kinds(&output), [(Severity::Warn, NoticeKind::PartialScan)]);
}

#[test]
fn binary_files_are_skipped() {
    let directory = fixture(&[("bin.dat", "needle\0needle\n"), ("text.txt", "needle\n")]);
    let output = run(&directory, &request("needle", "."));
    let paths: Vec<_> = output.files.iter().map(|file| file.path.as_str()).collect();
    assert_eq!(paths, ["text.txt"]);
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
fn long_lines_are_cut_at_512_bytes() {
    let line = format!("needle {}", "x".repeat(600));
    let directory = fixture(&[("f.txt", &line)]);
    let output = run(&directory, &request("needle", "f.txt"));
    let matched = &output.files[0].matches[0];
    assert_eq!(
        (
            matched.line.len(),
            matched.truncated,
            matched.line.ends_with("...")
        ),
        (512, true, true)
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
    )
    .expect("grep succeeds");
    assert_eq!(Path::new(&output.files[0].path), external.as_path());
}
