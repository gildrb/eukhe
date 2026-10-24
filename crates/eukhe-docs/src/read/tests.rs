use std::path::Path;

use super::*;
use crate::gate::Open;

/// A read of these tests: the gate is not their subject.
fn read(
    store: &EditStore,
    cwd: &Path,
    home: Option<&Path>,
    authored: &str,
) -> Result<ReadView, ReadError> {
    super::read(store, cwd, home, authored, &Open)
}

/// A read of an internal URL of these tests: the gate is not their
/// subject.
fn read_under(
    store: &EditStore,
    cwd: &Path,
    home: Option<&Path>,
    url: Url<'_>,
    locate: impl Fn(&[&str]) -> Option<Located>,
) -> Result<ReadView, ReadError> {
    super::read_under(store, cwd, home, url, locate, &Open)
}

fn setup(text: &str) -> (tempfile::TempDir, EditStore) {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("a.rs"), text).unwrap();
    (dir, EditStore::new())
}

fn numbered_file(lines: usize) -> String {
    (1..=lines)
        .flat_map(|n| ["l".to_owned(), n.to_string(), "\n".to_owned()])
        .collect()
}

#[test]
fn whole_small_file_has_header_and_rows_and_records_no_seen_lines() {
    let raw = "\u{FEFF}one\r\ntwo\r\n";
    let (dir, store) = setup(raw);
    let view = read(&store, dir.path(), None, "a.rs").unwrap();
    let tag = crate::file_hash("one\ntwo\n");
    assert_eq!(view.rendered, format!("[a.rs#{tag}]\n1:one\n2:two"));
    let key = eukhe_types::path_policy::real_path(&dir.path().join("a.rs"));
    let snapshot = store.by_hash(&key, &tag).unwrap();
    assert_eq!(
        (
            snapshot.seen_lines,
            store.has_seen_bytes(&key, raw.as_bytes())
        ),
        (None, true)
    );
}

/// Each row's `at` is the index of its line in `rendered`: the header is
/// line 0, and the ellipsis between spans takes a line.
#[test]
fn rows_point_at_their_rendered_lines() {
    let (dir, store) = setup(&numbered_file(20));
    let view = read(&store, dir.path(), None, "a.rs:2-2,5-6").unwrap();
    let ReadContent::File(file) = &view.content else {
        panic!("a file view");
    };
    let rendered: Vec<&str> = view.rendered.lines().collect();
    let shown: Vec<(u32, &str)> = file
        .rows
        .iter()
        .map(|row| (row.line, rendered[row.at]))
        .collect();
    assert_eq!(shown, [(2, "2:l2"), (5, "5:l5"), (6, "6:l6")]);
    let raw = read(&store, dir.path(), None, "a.rs:raw").unwrap();
    let ReadContent::File(raw) = raw.content else {
        panic!("a file view");
    };
    assert_eq!(raw.rows, []);
}

/// A file over the size limit reads without a tag, and a notice says why
/// and how to change it; its bytes count as seen for `write`.
#[test]
fn file_over_the_size_limit_reads_with_a_not_editable_notice() {
    let mut text = "first\n".repeat(10);
    text.push_str(&"x".repeat(usize::try_from(MAX_SNAPSHOT_FILE_BYTES).unwrap()));
    let (dir, store) = setup(&text);
    let view = read(&store, dir.path(), None, "a.rs:1-2").unwrap();
    let ReadContent::File(file) = &view.content else {
        panic!("a file view");
    };
    assert_eq!(
        (&file.tag, &view.diags[1..]),
        (
            &None,
            &[Notice {
                continuation: Some(":1-2000".to_owned()),
                ..Notice::warn(
                    NoticeKind::NotEditable,
                    "a.rs is 4.0MB, over the 4.0MB limit: it has no tag, so `edit` cannot change it. Read it in ranges; change it with `write` (whole file) or `bash`.".to_owned()
                )
            }][..]
        )
    );
    assert!(view.rendered.starts_with("1:first\n"));
    let key = eukhe_types::path_policy::real_path(&dir.path().join("a.rs"));
    assert!(store.has_seen_bytes(&key, text.as_bytes()));
}

/// A NUL-free file that is not UTF-8 is named with its encoding, not
/// called binary; `:raw` shows it lossy, with no tag, and records its bytes.
#[test]
fn non_utf8_file_is_named_with_its_encoding() {
    let (dir, store) = setup("x");
    std::fs::write(dir.path().join("latin.txt"), b"caf\xE9\n").unwrap();
    std::fs::write(dir.path().join("wide.txt"), b"\xFF\xFEa\0b\0").unwrap();
    assert_eq!(
        [
            read(&store, dir.path(), None, "latin.txt").unwrap_err().to_string(),
            read(&store, dir.path(), None, "wide.txt").unwrap_err().to_string(),
        ],
        [
            "[latin.txt is not UTF-8: `edit` works on UTF-8 only. ':raw' shows it (characters that are not UTF-8 become U+FFFD); `write` replaces it as UTF-8.]",
            "[wide.txt is UTF-16 (little endian): `edit` works on UTF-8 only. ':raw' shows it (characters that are not UTF-8 become U+FFFD); `write` replaces it as UTF-8.]",
        ]
    );
    let raw = read(&store, dir.path(), None, "latin.txt:raw").unwrap();
    let ReadContent::File(file) = &raw.content else {
        panic!("a file view");
    };
    assert_eq!((raw.rendered.as_str(), &file.tag), ("caf\u{FFFD}\n", &None));
    let key = eukhe_types::path_policy::real_path(&dir.path().join("latin.txt"));
    assert!(store.has_seen_bytes(&key, b"caf\xE9\n"));
}

#[test]
fn range_selector_adds_context_lines() {
    let (dir, store) = setup(&numbered_file(20));
    let view = read(&store, dir.path(), None, "a.rs:5-6").unwrap();
    let tag = crate::file_hash(&numbered_file(20));
    assert_eq!(
        view.rendered,
        format!(
            "[a.rs#{tag}]\n4:l4\n5:l5\n6:l6\n7:l7\n8:l8\n9:l9\n<diag severity=\"info\" kind=\"pagination\" continuation=\":10\" omitted=\"11 lines\">11 lines remain in a.rs.</diag>"
        )
    );
}

#[test]
fn multiple_ranges_are_joined_by_an_ellipsis() {
    let (dir, store) = setup(&numbered_file(20));
    let view = read(&store, dir.path(), None, "a.rs:2-2,5-6,30-31").unwrap();
    let tag = crate::file_hash(&numbered_file(20));
    assert_eq!(
        view.rendered,
        format!(
            "[a.rs#{tag}]\n2:l2\n…\n5:l5\n6:l6\n<diag severity=\"warn\" kind=\"range_out_of_bounds\">Requested range 30-31 is beyond end of a.rs (20 lines total).</diag>"
        )
    );
}

#[test]
fn raw_has_no_numbers_or_header() {
    let (dir, store) = setup("one\ntwo\n");
    let view = read(&store, dir.path(), None, "a.rs:raw").unwrap();
    assert_eq!(view.rendered, "one\ntwo\n");
}

#[test]
fn errors_teach_the_fix() {
    let (dir, store) = setup("one\n");
    std::fs::write(dir.path().join("b.bin"), b"\0\x01").unwrap();
    assert_eq!(
        [
            read(&store, dir.path(), None, "missing.rs").unwrap_err().to_string(),
            read(&store, dir.path(), None, "b.bin").unwrap_err().to_string(),
            read(&store, dir.path(), None, "a.rs:0").unwrap_err().to_string(),
        ],
        [
            "Path 'missing.rs' not found",
            "[Cannot read binary file 'b.bin' (2B): it has a NUL byte. Use ':raw' to read bytes verbatim.]",
            "Line selector 0 is invalid; lines are 1-indexed. Use :1.",
        ]
    );
}

#[test]
fn directory_reads_as_a_depth_two_tree() {
    let (dir, store) = setup("x");
    std::fs::create_dir_all(dir.path().join("sub/deeper")).unwrap();
    std::fs::write(dir.path().join("sub/deeper/hidden.rs"), "y").unwrap();
    std::fs::write(dir.path().join("sub/b.rs"), "yy").unwrap();
    let view = read(&store, dir.path(), None, ".").unwrap();
    let labels: Vec<String> = view
        .rendered
        .lines()
        .map(|line| {
            let name = line.trim_start();
            let indent = &line[..line.len() - name.len()];
            format!("{indent}{}", name.split("  ").next().unwrap())
        })
        .collect();
    assert_eq!(
        labels,
        [".", "  - a.rs", "  - sub/", "    - b.rs", "    - deeper/"]
    );
    let ReadContent::Directory(entries) = &view.content else {
        panic!("a directory read carries entries");
    };
    assert_eq!(
        entries
            .iter()
            .map(|entry| entry.relative_path.as_str())
            .collect::<Vec<_>>(),
        ["a.rs", "sub", "sub/b.rs", "sub/deeper"]
    );
    assert_eq!(
        read(&store, dir.path(), None, ".:1-2,4")
            .unwrap_err()
            .to_string(),
        "Multi-range line selectors are not supported for directory listings."
    );
    let page = read(&store, dir.path(), None, ".:2-3").unwrap();
    assert!(page.rendered.starts_with("  - a.rs"), "{}", page.rendered);
    assert!(page.rendered.ends_with(
        "<diag severity=\"info\" kind=\"pagination\" continuation=\":4\" omitted=\"2 lines\">2 lines remain in listing.</diag>"
    ));
}

#[test]
fn display_path_prefers_cwd_then_home() {
    let home = Path::new("/home/u");
    assert_eq!(
        [
            display_path(
                Path::new("/home/u/p/a.rs"),
                Path::new("/home/u/p"),
                Some(home)
            ),
            display_path(
                Path::new("/home/u/q/a.rs"),
                Path::new("/home/u/p"),
                Some(home)
            ),
            display_path(Path::new("/etc/x"), Path::new("/home/u/p"), Some(home)),
        ],
        ["a.rs", "~/q/a.rs", "/etc/x"]
    );
}

fn repo_url(path: &str) -> Url<'_> {
    Url {
        scheme: crate::Scheme::Repo,
        path,
    }
}

/// The names joined under `root`; `missing` names none.
fn under(root: &Path) -> impl Fn(&[&str]) -> Option<crate::Located> + '_ {
    |names| {
        (names.first() != Some(&"missing")).then(|| crate::Located {
            root: root.to_path_buf(),
            path: names
                .iter()
                .fold(root.to_path_buf(), |path, name| path.join(name)),
        })
    }
}

#[test]
fn url_reads_a_file_under_its_root_with_a_selector() {
    let (dir, store) = setup("one\ntwo\nthree\n");
    let root = dir.path().join("root");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(root.join("src/b.rs"), "one\ntwo\nthree\n").unwrap();
    let view = read_under(
        &store,
        dir.path(),
        None,
        repo_url("src/./b.rs:2"),
        under(&root),
    )
    .unwrap();
    let tag = crate::file_hash("one\ntwo\nthree\n");
    assert_eq!(
        (view.path, view.absolute, view.rendered),
        (
            "root/src/b.rs".to_owned(),
            root.join("src/b.rs"),
            format!("[root/src/b.rs#{tag}]\n1:one\n2:two\n3:three")
        )
    );
}

#[test]
fn url_above_its_root_is_rejected_even_when_the_file_exists() {
    let (dir, store) = setup("one\n");
    let root = dir.path().join("root");
    std::fs::create_dir_all(&root).unwrap();
    let errors: Vec<String> = ["../a.rs", "x/../../a.rs:1", "/..", "missing/x"]
        .into_iter()
        .map(|path| {
            read_under(&store, dir.path(), None, repo_url(path), under(&root))
                .unwrap_err()
                .to_string()
        })
        .collect();
    assert_eq!(
        errors,
        [
            "repo://../a.rs goes above the root of repo://; `..` cannot leave it",
            "repo://x/../../a.rs goes above the root of repo://; `..` cannot leave it",
            "repo:///.. goes above the root of repo://; `..` cannot leave it",
            "Path 'repo://missing/x' not found",
        ]
    );
}

/// A symlink inside the root that points outside it is rejected: the real
/// path must stay under the root's real path. A symlink that stays inside
/// reads as usual.
#[test]
fn url_through_a_symlink_out_of_its_root_is_rejected() {
    let (dir, store) = setup("secret\n");
    let root = dir.path().join("root");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(root.join("src/b.rs"), "inside\n").unwrap();
    std::os::unix::fs::symlink(dir.path().join("a.rs"), root.join("out.rs")).unwrap();
    std::os::unix::fs::symlink(dir.path(), root.join("up")).unwrap();
    std::os::unix::fs::symlink(root.join("src"), root.join("in")).unwrap();
    let read = |path| {
        read_under(&store, dir.path(), None, repo_url(path), under(&root))
            .map(|view| view.rendered)
            .map_err(|error| error.to_string())
    };
    assert_eq!(
        [read("out.rs"), read("up/a.rs:1"), read("in/b.rs")],
        [
            Err("repo://out.rs resolves outside the root of repo:// through a symlink".to_owned()),
            Err("repo://up/a.rs resolves outside the root of repo:// through a symlink".to_owned()),
            Ok(format!(
                "[root/in/b.rs#{}]\n1:inside",
                crate::file_hash("inside\n")
            )),
        ]
    );
}

/// A root without a real path (here: gone) is an error, not a read that
/// skips the symlink check.
#[test]
fn url_under_a_root_without_a_real_path_is_an_error() {
    let (dir, store) = setup("outside\n");
    let got = read_under(&store, dir.path(), None, repo_url("a.rs"), |_| {
        Some(crate::Located {
            root: dir.path().join("gone"),
            path: dir.path().join("a.rs"),
        })
    })
    .map(|view| view.rendered)
    .map_err(|error| error.to_string());
    assert_eq!(
        got,
        Err("gone: No such file or directory (os error 2)".to_owned())
    );
}
