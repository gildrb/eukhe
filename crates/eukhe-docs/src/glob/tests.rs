use std::{
    fs::{self, File},
    time::{Duration, SystemTime},
};

use tempfile::TempDir;

use super::*;
use crate::gate::Open;
use crate::notice::Severity;

fn request(path: &str) -> GlobRequest {
    GlobRequest {
        path: path.to_owned(),
        hidden: true,
        gitignore: true,
        limit: None,
    }
}

fn fixture(files: &[(&str, u64)]) -> TempDir {
    let directory = tempfile::tempdir().expect("temp directory");
    for (path, modified_secs) in files {
        let path = directory.path().join(path);
        fs::create_dir_all(path.parent().expect("fixture parent")).expect("fixture directory");
        let file = File::create(&path).expect("fixture file");
        file.set_modified(SystemTime::UNIX_EPOCH + Duration::from_secs(*modified_secs))
            .expect("fixture mtime");
    }
    directory
}

fn paths(output: &GlobOutput) -> Vec<&str> {
    output
        .matches
        .iter()
        .map(|entry| entry.path.as_str())
        .collect()
}

fn run(directory: &TempDir, request: &GlobRequest) -> GlobOutput {
    glob(directory.path(), request, &Open).expect("glob succeeds")
}

#[test]
fn matches_are_newest_first_grouped_and_hard_limited() {
    let directory = fixture(&[
        ("src/old.rs", 10),
        ("src/new.rs", 30),
        ("docs/generated/a.md", 5),
        ("src/mid.rs", 20),
    ]);
    let output = run(
        &directory,
        &GlobRequest {
            limit: NonZeroUsize::new(2),
            ..request("src/*.rs")
        },
    );
    assert_eq!(paths(&output), ["src/new.rs", "src/mid.rs"]);
    assert_eq!(output.text, "# src/\nnew.rs\nmid.rs");
    assert_eq!(
        output.notices,
        [Notice {
            continuation: Some("limit=4".to_owned()),
            ..Notice::info(
                NoticeKind::LimitReached,
                "2 result limit reached".to_owned()
            )
        }]
    );
    assert!(output.truncated);
}

#[test]
fn directories_end_in_a_slash_and_equal_times_sort_by_path() {
    let directory = fixture(&[("b.rs", 7), ("a.rs", 7)]);
    fs::create_dir(directory.path().join("sub")).expect("subdirectory");
    let sub = File::open(directory.path().join("sub")).expect("open subdirectory");
    sub.set_modified(SystemTime::UNIX_EPOCH + Duration::from_secs(9))
        .expect("subdirectory mtime");
    let output = run(&directory, &request("."));
    assert_eq!(paths(&output), ["sub/", "a.rs", "b.rs"]);
    assert_eq!(output.text, "a.rs\nb.rs\n# sub/");
}

#[test]
fn bare_globs_recurse_and_directory_globs_stay_shallow() {
    let directory = fixture(&[("top.rs", 1), ("src/a.rs", 2), ("src/deep/b.rs", 3)]);
    assert_eq!(
        paths(&run(&directory, &request("*.rs"))),
        ["src/deep/b.rs", "src/a.rs", "top.rs"]
    );
    assert_eq!(
        paths(&run(&directory, &request("src/*"))),
        ["src/deep/", "src/a.rs"]
    );
}

#[test]
fn semicolon_inputs_keep_literals_and_split_top_level_roots() {
    let directory = fixture(&[("literal;name.rs", 1), ("route[id].rs", 2)]);
    let root = directory.path();
    assert_eq!(
        split_inputs(root, "literal;name.rs").expect("literal"),
        ["literal;name.rs"]
    );
    assert_eq!(
        split_inputs(root, "src/{one;two}.rs; tests/**/*.rs").expect("top-level roots"),
        ["src/{one;two}.rs", "tests/**/*.rs"]
    );
    assert_eq!(
        split_inputs(root, "one.rs; two.rs;").expect("missing roots still split"),
        ["one.rs", "two.rs"]
    );
    assert_eq!(
        split_inputs(root, r"src/a\;b.rs").expect("escaped delimiter"),
        [r"src/a\;b.rs"]
    );
    assert_eq!(
        paths(&run(&directory, &request("route[id].rs"))),
        ["route[id].rs"]
    );
}

#[test]
fn hidden_and_gitignore_toggles_are_independent() {
    let directory = fixture(&[
        (".gitignore", 1),
        (".hidden.rs", 2),
        ("ignored.rs", 3),
        ("visible.rs", 4),
    ]);
    fs::write(directory.path().join(".gitignore"), "ignored.rs\n").expect("ignore file");
    let respected = run(&directory, &request("**/*.rs"));
    assert_eq!(paths(&respected), ["visible.rs", ".hidden.rs"]);
    let unfiltered = run(
        &directory,
        &GlobRequest {
            hidden: false,
            gitignore: false,
            ..request("**/*.rs")
        },
    );
    assert_eq!(paths(&unfiltered), ["visible.rs", "ignored.rs"]);
}

#[test]
fn multi_root_missing_targets_and_timeout_are_explicit() {
    let directory = fixture(&[("one/a.rs", 2), ("two/b.rs", 1)]);
    let output = run(
        &directory,
        &request("one/**/*.rs; missing/**/*.rs; two/**/*.rs"),
    );
    assert_eq!(paths(&output), ["one/a.rs", "two/b.rs"]);
    assert_eq!(
        output.notices,
        [Notice::warn(
            NoticeKind::MissingPaths,
            "missing/**/*.rs".to_owned()
        )]
    );

    let timed_out = glob_until(
        directory.path(),
        &request("one/**/*.rs"),
        &Open,
        Duration::ZERO,
    )
    .expect("partial");
    assert_eq!(
        (
            timed_out.matches.len(),
            timed_out.timed_out,
            timed_out.text.as_str()
        ),
        (0, true, "")
    );
    assert_eq!(
        timed_out
            .notices
            .iter()
            .map(|notice| (notice.severity, notice.kind, notice.text.as_str()))
            .collect::<Vec<_>>(),
        [(
            Severity::Warn,
            NoticeKind::Timeout,
            "Glob reached its 0s timeout after finding 0 partial matches"
        )]
    );
}

#[test]
fn faults_keep_the_omp_messages() {
    let directory = fixture(&[("file.rs", 1)]);
    let fault = |path: &str| {
        glob(directory.path(), &request(path), &Open)
            .expect_err("glob fails")
            .to_string()
    };
    assert_eq!(fault("  "), "`path` must contain non-empty globs or paths");
    assert_eq!(
        fault("/"),
        "Searching from root directory '/' is not allowed"
    );
    assert_eq!(fault("gone; also/*.rs"), "Path not found: gone, also/*.rs");
    assert_eq!(
        fault("file.rs/*.rs"),
        "Path is not a directory: file.rs/*.rs"
    );
    assert_eq!(
        fault("artifact://x"),
        "artifact:// targets are not supported yet"
    );
    assert!(fault("[.rs").starts_with("invalid glob pattern **/[.rs: "));
}

#[test]
fn no_match_renders_the_omp_message() {
    let directory = fixture(&[("a.rs", 1)]);
    let output = run(&directory, &request("*.md"));
    assert_eq!(output.text, "No files found matching pattern");
}

#[test]
fn external_absolute_directory_keeps_its_absolute_spelling() {
    let parent = fixture(&[("external/lib.rs", 1), ("workspace/keep", 1)]);
    let external = parent.path().join("external");
    let output = glob(
        &parent.path().join("workspace"),
        &request(&format!("{}/**/*.rs", external.display())),
        &Open,
    )
    .expect("glob succeeds");
    assert_eq!(
        paths(&output),
        [external.join("lib.rs").to_string_lossy().replace('\\', "/")]
    );
}

#[test]
fn ranked_retention_keeps_newest_then_lexical() {
    let mut matches = Vec::new();
    for (path, modified_ms) in [("b", 1), ("c", 2), ("a", 2)] {
        retain_ranked(
            &mut matches,
            GlobMatch {
                path: path.to_owned(),
                modified_ms,
                is_dir: false,
            },
            1,
        );
    }
    matches.sort_by(|left, right| compare_rank(right, left));
    assert_eq!(
        matches
            .iter()
            .map(|entry| entry.path.as_str())
            .collect::<Vec<_>>(),
        ["a", "c"]
    );
}

#[test]
fn find_patterns_split_at_the_first_glob_segment() {
    assert_eq!(
        [
            parse_find_pattern("src/*"),
            parse_find_pattern("*.rs"),
            parse_find_pattern("src"),
        ],
        [
            ("src".to_owned(), Some("*".to_owned())),
            (".".to_owned(), Some("**/*.rs".to_owned())),
            ("src".to_owned(), None),
        ]
    );
}
