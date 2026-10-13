//! Directory reads (port of omp `read/dirtree.rs` `render_directory` and the
//! envd directory walk): a tree two levels deep, `- name` rows indented by
//! depth with size and age columns, non-root directories capped at
//! [`CHILD_LIMIT`] children.

use std::collections::HashMap;
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::notice::{Notice, NoticeKind, Omitted, Unit};

/// Maximum directory depth rendered below the root.
const MAX_DEPTH: usize = 2;
/// Maximum retained children for each non-root directory.
const CHILD_LIMIT: usize = 12;
/// Directory names the walk never enters or lists (omp `skip_git`,
/// `skip_node_modules`).
const SKIPPED_NAMES: [&str; 2] = [".git", "node_modules"];

/// One entry under a listed directory.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DirEntry {
    /// Slash-separated path relative to the listed directory; one segment at
    /// depth 1, two at depth 2.
    pub relative_path: String,
    pub is_dir: bool,
    /// File size in bytes; `None` for directories.
    pub size: Option<u64>,
    /// Modification time in milliseconds since the Unix epoch, when known.
    pub modified_ms: Option<u64>,
}

/// Walk `directory` to [`MAX_DEPTH`] in path order: hidden entries
/// included, ignore files not consulted, symlinks not followed.
pub(super) fn list(directory: &Path) -> std::io::Result<Vec<DirEntry>> {
    let mut entries = Vec::new();
    walk(directory, "", 1, &mut entries)?;
    Ok(entries)
}

fn walk(
    directory: &Path,
    prefix: &str,
    depth: usize,
    out: &mut Vec<DirEntry>,
) -> std::io::Result<()> {
    let mut children = Vec::new();
    for entry in std::fs::read_dir(directory)? {
        let entry = entry?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if SKIPPED_NAMES.contains(&name.as_str()) {
            continue;
        }
        children.push((name, entry));
    }
    children.sort_by(|(a, _), (b, _)| a.cmp(b));
    for (name, entry) in children {
        let metadata = entry.metadata()?;
        let is_dir = metadata.is_dir();
        let relative_path = if prefix.is_empty() {
            name
        } else {
            format!("{prefix}/{name}")
        };
        let modified_ms = metadata
            .modified()
            .ok()
            .and_then(|time| time.duration_since(UNIX_EPOCH).ok())
            .and_then(|elapsed| u64::try_from(elapsed.as_millis()).ok());
        out.push(DirEntry {
            relative_path: relative_path.clone(),
            is_dir,
            size: (!is_dir).then_some(metadata.len()),
            modified_ms,
        });
        if is_dir && depth < MAX_DEPTH {
            walk(&entry.path(), &relative_path, depth + 1, out)?;
        }
    }
    Ok(())
}

/// Milliseconds since the Unix epoch now.
pub(super) fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .ok()
        .and_then(|elapsed| u64::try_from(elapsed.as_millis()).ok())
        .unwrap_or(0)
}

/// A rendered listing and its notices.
pub(super) struct Rendered {
    pub(super) text: String,
    pub(super) diags: Vec<Notice>,
}

#[derive(Clone, Copy)]
struct EntryRef<'a> {
    entry: &'a DirEntry,
    name: &'a str,
    depth: usize,
}

struct Row {
    label: String,
    size: Option<String>,
    age: Option<String>,
}

type Children<'a> = HashMap<&'a str, Vec<EntryRef<'a>>>;

/// Render `entries` as omp's tree. `now_ms` dates the age column; `offset`
/// (one-based) and `limit` slice the rendered rows.
pub(super) fn render(
    entries: &[DirEntry],
    now_ms: u64,
    offset: Option<usize>,
    limit: Option<usize>,
) -> Rendered {
    let mut by_parent: Children<'_> = HashMap::new();
    for entry in entries {
        let path = entry.relative_path.trim_matches('/');
        if path.is_empty() {
            continue;
        }
        let depth = path.bytes().filter(|byte| *byte == b'/').count() + 1;
        if depth > MAX_DEPTH {
            continue;
        }
        let (parent, name) = path.rsplit_once('/').unwrap_or(("", path));
        by_parent
            .entry(parent)
            .or_default()
            .push(EntryRef { entry, name, depth });
    }
    for children in by_parent.values_mut() {
        children.sort_unstable_by(|a, b| a.name.cmp(b.name));
    }
    let mut rows = vec![Row {
        label: ".".to_owned(),
        size: None,
        age: None,
    }];
    let mut diags = Vec::new();
    render_children("", 0, &by_parent, now_ms, &mut rows, &mut diags);
    let base = if rows.len() <= 1 {
        "(empty directory)".to_owned()
    } else {
        format_rows(&rows)
    };
    if offset.is_none() && limit.is_none() {
        return Rendered { text: base, diags };
    }
    let all_lines: Vec<&str> = base.split('\n').collect();
    let total_lines = all_lines.len();
    let start = offset.unwrap_or(1).saturating_sub(1);
    if start >= total_lines {
        diags.push(Notice {
            continuation: Some(":1".to_owned()),
            ..Notice::warn(
                NoticeKind::RangeOutOfBounds,
                format!(
                    "Line {} is beyond end of listing ({total_lines} lines total).",
                    start + 1
                ),
            )
        });
        return Rendered {
            text: String::new(),
            diags,
        };
    }
    let end = limit.map_or(total_lines, |count| {
        start.saturating_add(count).min(total_lines)
    });
    let text = all_lines[start..end].join("\n");
    if end < total_lines {
        let remaining = total_lines - end;
        diags.push(Notice {
            continuation: Some(format!(":{}", end + 1)),
            omitted: Some(Omitted {
                count: u64::try_from(remaining).unwrap_or(u64::MAX),
                unit: Unit::Lines,
            }),
            ..Notice::info(
                NoticeKind::Pagination,
                format!("{remaining} lines remain in listing."),
            )
        });
    }
    Rendered { text, diags }
}

fn render_children(
    parent: &str,
    parent_depth: usize,
    by_parent: &Children<'_>,
    now_ms: u64,
    rows: &mut Vec<Row>,
    diags: &mut Vec<Notice>,
) {
    let Some(all) = by_parent.get(parent) else {
        return;
    };
    let retained = if parent_depth > 0 {
        all.len().min(CHILD_LIMIT)
    } else {
        all.len()
    };
    for child in &all[..retained] {
        render_entry(*child, parent, by_parent, now_ms, rows, diags);
    }
    if retained == all.len() {
        return;
    }
    let omitted = all.len() - retained;
    diags.push(Notice {
        omitted: Some(Omitted {
            count: u64::try_from(omitted).unwrap_or(u64::MAX),
            unit: Unit::Entries,
        }),
        ..Notice::info(
            NoticeKind::LimitReached,
            format!("{omitted} directory entries omitted."),
        )
    });
}

fn render_entry(
    node: EntryRef<'_>,
    parent: &str,
    by_parent: &Children<'_>,
    now_ms: u64,
    rows: &mut Vec<Row>,
    diags: &mut Vec<Notice>,
) {
    let suffix = if node.entry.is_dir { "/" } else { "" };
    rows.push(Row {
        label: format!("{}- {}{suffix}", "  ".repeat(node.depth), node.name),
        size: if node.entry.is_dir {
            None
        } else {
            Some(super::format_bytes(node.entry.size.unwrap_or(0)))
        },
        age: format_age(now_ms.saturating_sub(node.entry.modified_ms.unwrap_or(0)) / 1_000),
    });
    if !node.entry.is_dir || node.depth >= MAX_DEPTH {
        return;
    }
    let child_path = if parent.is_empty() {
        node.name.to_owned()
    } else {
        format!("{parent}/{}", node.name)
    };
    render_children(&child_path, node.depth, by_parent, now_ms, rows, diags);
}

/// Align the size and age columns after the widest label. omp measures
/// display width; eukhe counts chars.
fn format_rows(rows: &[Row]) -> String {
    let width = |label: &str| label.chars().count();
    let max_label = rows.iter().map(|row| width(&row.label)).max().unwrap_or(0);
    let mut out = String::new();
    for (index, row) in rows.iter().enumerate() {
        if index > 0 {
            out.push('\n');
        }
        out.push_str(&row.label);
        let Some(age) = &row.age else {
            continue;
        };
        out.extend(std::iter::repeat_n(' ', max_label - width(&row.label) + 2));
        let size = row.size.as_deref().unwrap_or("");
        out.push_str(size);
        out.extend(std::iter::repeat_n(' ', 8_usize.saturating_sub(size.len())));
        out.push_str("  ");
        out.push_str(age);
    }
    out
}

fn format_age(seconds: u64) -> Option<String> {
    if seconds == 0 {
        return None;
    }
    let minutes = seconds / 60;
    let hours = minutes / 60;
    let days = hours / 24;
    let weeks = days / 7;
    let months = days / 30;
    Some(if months > 0 {
        format!("{months}mo ago")
    } else if weeks > 0 {
        format!("{weeks}w ago")
    } else if days > 0 {
        format!("{days}d ago")
    } else if hours > 0 {
        format!("{hours}h ago")
    } else if minutes > 0 {
        format!("{minutes}m ago")
    } else {
        "just now".to_owned()
    })
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;

    use super::*;

    fn file(path: &str, size: u64, modified_ms: u64) -> DirEntry {
        DirEntry {
            relative_path: path.to_owned(),
            is_dir: false,
            size: Some(size),
            modified_ms: Some(modified_ms),
        }
    }

    fn dir(path: &str, modified_ms: u64) -> DirEntry {
        DirEntry {
            relative_path: path.to_owned(),
            is_dir: true,
            size: None,
            modified_ms: Some(modified_ms),
        }
    }

    #[test]
    fn entries_are_alphabetical_and_directories_have_slashes() {
        let entries = [
            file("zeta.txt", 3, 9_000),
            dir("alpha", 1_000),
            file("alpha/b.txt", 2, 8_000),
            file("alpha/a.txt", 1, 7_000),
        ];
        let rendered = render(&entries, 10_000, None, None);
        let text = &rendered.text;
        let alpha = text.find("- alpha/").unwrap();
        let nested_a = text.find("- a.txt").unwrap();
        let nested_b = text.find("- b.txt").unwrap();
        let zeta = text.find("- zeta.txt").unwrap();
        assert!(alpha < nested_a && nested_a < nested_b && nested_b < zeta);
    }

    #[test]
    fn columns_align_after_the_widest_label() {
        let now = 3 * 3_600_000;
        let entries = [
            dir("src", now - 120_000),
            file("src/lib.rs", 2048, now - 7_200_000),
            file("README.md", 10, now - 30_000),
        ];
        assert_eq!(
            render(&entries, now, None, None).text,
            concat!(
                ".\n",
                "  - README.md  10B       just now\n",
                "  - src/                 2m ago\n",
                "    - lib.rs   2.0KB     2h ago",
            )
        );
    }

    #[test]
    fn depth_two_and_nested_children_are_capped() {
        let mut entries = vec![dir("dir", u64::MAX)];
        entries.extend(
            (0..14).map(|index| file(&format!("dir/child-{index:02}.txt"), index, u64::MAX)),
        );
        entries.push(file("dir/nested/too-deep.txt", 1, u64::MAX));
        let rendered = render(&entries, 10_000, None, None);
        let mut expected = ".\n  - dir/".to_owned();
        for index in 0..12 {
            let _infallible = write!(expected, "\n    - child-{index:02}.txt");
        }
        assert_eq!(rendered.text, expected);
        let [diag] = rendered.diags.as_slice() else {
            panic!("child cap emits one notice: {:?}", rendered.diags);
        };
        assert_eq!(
            diag.to_string(),
            "<diag severity=\"info\" kind=\"limit_reached\" omitted=\"2 entries\">2 directory entries omitted.</diag>"
        );
    }

    #[test]
    fn root_children_are_never_capped() {
        let entries: Vec<_> = (0..20)
            .map(|index| file(&format!("f{index:02}"), 1, u64::MAX))
            .collect();
        let rendered = render(&entries, 10_000, None, None);
        assert_eq!(rendered.text.lines().count(), 21);
        assert!(rendered.diags.is_empty());
    }

    #[test]
    fn empty_directory_and_listing_ranges() {
        assert_eq!(render(&[], 0, None, None).text, "(empty directory)");
        let entries = [file("a.txt", 1, 0)];
        let page = render(&entries, 10_000, Some(1), Some(1));
        assert_eq!(page.text, ".");
        assert_eq!(
            page.diags[0].to_string(),
            "<diag severity=\"info\" kind=\"pagination\" continuation=\":2\" omitted=\"1 lines\">1 lines remain in listing.</diag>"
        );
        let beyond = render(&entries, 10_000, Some(3), Some(1));
        assert!(beyond.text.is_empty());
        assert_eq!(
            beyond.diags[0].to_string(),
            "<diag severity=\"warn\" kind=\"range_out_of_bounds\" continuation=\":1\">Line 3 is beyond end of listing (2 lines total).</diag>"
        );
    }

    #[test]
    fn same_input_is_deterministic_across_input_order() {
        let mut entries = vec![file("b", 2, 2), file("a", 1, 1)];
        let first = render(&entries, 10_000, None, None).text;
        entries.reverse();
        assert_eq!(first, render(&entries, 10_000, None, None).text);
    }

    #[test]
    fn walk_is_depth_two_with_hidden_entries_and_without_vcs_dirs() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path();
        std::fs::create_dir_all(path.join("a/b/c")).unwrap();
        std::fs::create_dir_all(path.join(".git/objects")).unwrap();
        std::fs::create_dir_all(path.join("node_modules/x")).unwrap();
        std::fs::write(path.join(".env"), "k=v").unwrap();
        std::fs::write(path.join("a/b/c/deep.txt"), "x").unwrap();
        let entries = list(path).unwrap();
        let paths: Vec<_> = entries
            .iter()
            .map(|entry| (entry.relative_path.as_str(), entry.is_dir, entry.size))
            .collect();
        assert_eq!(
            paths,
            [
                (".env", false, Some(3)),
                ("a", true, None),
                ("a/b", true, None)
            ]
        );
    }
}
