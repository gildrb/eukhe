//! Prefix-folded path trees: the `# dir/` headings grep and glob render.
//!
//! Ported from omp `crates/tools/src/render/paths.rs`.

use std::collections::{HashMap, HashSet};

#[derive(Debug, Default)]
struct BuilderNode {
    files: Vec<FileLeaf>,
    file_names: HashSet<String>,
    subdirs: Vec<BuilderDirectory>,
    dir_index: HashMap<String, usize>,
}

impl BuilderNode {
    fn add_file(&mut self, name: &str, key: &str) {
        if !self.file_names.insert(name.to_owned()) {
            return;
        }
        self.files.push(FileLeaf {
            name: name.to_owned(),
            key: key.to_owned(),
        });
    }

    fn child_mut(&mut self, name: &str) -> &mut Self {
        let index = if let Some(index) = self.dir_index.get(name) {
            *index
        } else {
            let index = self.subdirs.len();
            self.dir_index.insert(name.to_owned(), index);
            self.subdirs.push(BuilderDirectory {
                name: name.to_owned(),
                node: Self::default(),
            });
            index
        };
        &mut self.subdirs[index].node
    }
}

#[derive(Debug)]
struct BuilderDirectory {
    name: String,
    node: BuilderNode,
}

#[derive(Debug)]
struct FileLeaf {
    name: String,
    key: String,
}

#[derive(Debug)]
struct Directory {
    name: String,
    node: PathTreeNode,
}

#[derive(Debug)]
struct PathTreeNode {
    files: Vec<FileLeaf>,
    subdirs: Vec<Directory>,
}

/// A directory tree built from flat paths in first-seen order.
#[derive(Debug)]
pub(crate) struct PathTree {
    root: PathTreeNode,
}

/// The kind of item emitted by [`walk_path_tree`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum GroupedTreeEventKind {
    /// A prefix-folded directory chain.
    Directory,
    /// A direct file leaf.
    File,
}

/// One prefix-folded directory or file emitted by [`walk_path_tree`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct GroupedTreeEvent<'a> {
    pub(crate) kind: GroupedTreeEventKind,
    /// Zero-based nesting depth; root children have depth zero.
    pub(crate) depth: usize,
    /// A folded chain without a trailing slash for directories, or a basename
    /// for files.
    pub(crate) name: &'a str,
    /// The original path of a file, or an empty string for directories.
    pub(crate) key: &'a str,
}

impl GroupedTreeEvent<'_> {
    /// Whether grouped file output starts a blank-line-delimited section here:
    /// every directory and every root-level file does.
    pub(crate) const fn starts_group(self) -> bool {
        matches!(self.kind, GroupedTreeEventKind::Directory) || self.depth == 0
    }

    /// The number of `#` characters in this event's grouped header.
    pub(crate) const fn heading_level(self) -> usize {
        self.depth + 1
    }
}

/// Builds a path tree while preserving first-seen directory and file order.
///
/// Backslashes are normalized to slashes. Absolute paths retain their leading
/// empty segment, so the common `/` prefix folds naturally. Duplicate file
/// basenames under the same node keep the first key. Directory-only inputs
/// remain visible as leaf headers.
pub(crate) fn build_path_tree<'a>(entries: impl IntoIterator<Item = (&'a str, bool)>) -> PathTree {
    let mut root = BuilderNode::default();
    for (path, is_dir) in entries {
        let normalized = path.replace('\\', "/");
        let trimmed = normalized.strip_suffix('/').unwrap_or(&normalized);
        if trimmed.is_empty() {
            continue;
        }
        let mut node = &mut root;
        let mut segments = trimmed.split('/').peekable();
        while let Some(segment) = segments.next() {
            if !is_dir && segments.peek().is_none() {
                node.add_file(segment, path);
                break;
            }
            node = node.child_mut(segment);
        }
    }
    PathTree {
        root: finish_node(root),
    }
}

fn finish_node(node: BuilderNode) -> PathTreeNode {
    PathTreeNode {
        files: node.files,
        subdirs: node.subdirs.into_iter().map(finish_directory).collect(),
    }
}

fn finish_directory(mut directory: BuilderDirectory) -> Directory {
    while directory.node.files.is_empty() && directory.node.subdirs.len() == 1 {
        let Some(only) = directory.node.subdirs.pop() else {
            break;
        };
        directory.name.push('/');
        directory.name.push_str(&only.name);
        directory.node = only.node;
    }
    Directory {
        name: directory.name,
        node: finish_node(directory.node),
    }
}

#[derive(Debug)]
struct WalkFrame<'a> {
    node: &'a PathTreeNode,
    depth: usize,
    next_file: usize,
    next_dir: usize,
}

/// Depth-first iterator returned by [`walk_path_tree`]. A node's direct files
/// are emitted before its child directories.
#[derive(Debug)]
pub(crate) struct PathTreeIter<'a> {
    stack: Vec<WalkFrame<'a>>,
}

impl<'a> Iterator for PathTreeIter<'a> {
    type Item = GroupedTreeEvent<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let frame = self.stack.last_mut()?;
            if let Some(file) = frame.node.files.get(frame.next_file) {
                frame.next_file += 1;
                return Some(GroupedTreeEvent {
                    kind: GroupedTreeEventKind::File,
                    depth: frame.depth,
                    name: &file.name,
                    key: &file.key,
                });
            }
            if let Some(directory) = frame.node.subdirs.get(frame.next_dir) {
                frame.next_dir += 1;
                let depth = frame.depth;
                self.stack.push(WalkFrame {
                    node: &directory.node,
                    depth: depth + 1,
                    next_file: 0,
                    next_dir: 0,
                });
                return Some(GroupedTreeEvent {
                    kind: GroupedTreeEventKind::Directory,
                    depth,
                    name: &directory.name,
                    key: "",
                });
            }
            self.stack.pop();
        }
    }
}

/// Walks `tree` depth-first with single-child directory chains already folded.
pub(crate) fn walk_path_tree(tree: &PathTree) -> PathTreeIter<'_> {
    PathTreeIter {
        stack: vec![WalkFrame {
            node: &tree.root,
            depth: 0,
            next_file: 0,
            next_dir: 0,
        }],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn traversal_marks_group_boundaries_for_grouped_file_projection() {
        let tree = build_path_tree([
            ("root.rs", false),
            ("src/a.rs", false),
            ("src/deep/b.rs", false),
        ]);
        let events: Vec<_> = walk_path_tree(&tree)
            .map(|event| {
                (
                    event.kind,
                    event.depth,
                    event.name,
                    event.key,
                    event.starts_group(),
                )
            })
            .collect();
        assert_eq!(
            events,
            [
                (GroupedTreeEventKind::File, 0, "root.rs", "root.rs", true),
                (GroupedTreeEventKind::Directory, 0, "src", "", true),
                (GroupedTreeEventKind::File, 1, "a.rs", "src/a.rs", false),
                (GroupedTreeEventKind::Directory, 1, "deep", "", true),
                (
                    GroupedTreeEventKind::File,
                    2,
                    "b.rs",
                    "src/deep/b.rs",
                    false
                ),
            ]
        );
    }
}
