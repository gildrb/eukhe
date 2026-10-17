use std::path::Path;

use super::*;

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
fn whole_small_file_has_header_and_rows_and_records_seen_lines() {
    let (dir, store) = setup("\u{FEFF}one\r\ntwo\r\n");
    let view = read(&store, dir.path(), None, "a.rs").unwrap();
    let tag = crate::file_hash("one\ntwo\n");
    assert_eq!(view.rendered, format!("[a.rs#{tag}]\n1:one\n2:two"));
    let key = crate::canonical_key(&dir.path().join("a.rs"));
    let snapshot = store.by_hash(&key, &tag).unwrap();
    assert_eq!(
        snapshot.seen_lines.unwrap().into_iter().collect::<Vec<_>>(),
        [1, 2]
    );
}

#[test]
fn selectorless_read_shows_the_whole_file_without_pagination() {
    let lines = 405;
    let (dir, store) = setup(&numbered_file(lines));
    let view = read(&store, dir.path(), None, "a.rs").unwrap();
    assert_eq!(view.rendered.lines().last().unwrap(), "405:l405");
    assert!(view.diags.is_empty());
    assert_eq!(
        view.content,
        ReadContent::File(FileView {
            tag: Some(crate::file_hash(&numbered_file(lines))),
            text: numbered_file(lines),
            total_lines: lines,
            shown: vec![LineSpan {
                start_line: 1,
                end_line: lines
            }],
        })
    );
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
            "[Cannot read binary file 'b.bin' (2B); not valid UTF-8 text. Use ':raw' to read bytes verbatim.]",
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
