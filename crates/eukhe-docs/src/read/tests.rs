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
fn default_window_paginates() {
    let (dir, store) = setup(&numbered_file(DEFAULT_WINDOW_LINES + 5));
    let view = read(&store, dir.path(), None, "a.rs").unwrap();
    assert_eq!(
        view.rendered.lines().last().unwrap(),
        "<diag severity=\"info\" kind=\"pagination\" continuation=\":401\" omitted=\"5 lines\">5 lines remain in a.rs.</diag>"
    );
    assert_eq!(
        view.content,
        ReadContent::File(FileView {
            tag: Some(crate::file_hash(&numbered_file(DEFAULT_WINDOW_LINES + 5))),
            text: numbered_file(DEFAULT_WINDOW_LINES + 5),
            total_lines: DEFAULT_WINDOW_LINES + 5,
            shown: vec![LineSpan {
                start_line: 1,
                end_line: DEFAULT_WINDOW_LINES
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
fn directory_lists_directories_first() {
    let (dir, store) = setup("x");
    std::fs::create_dir(dir.path().join("sub")).unwrap();
    let view = read(&store, dir.path(), None, ".").unwrap();
    assert_eq!(view.rendered, "sub/\na.rs (1B)");
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
