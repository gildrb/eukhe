use std::os::unix::fs::symlink;

use super::*;

/// A tree of one home (agent dir, ssh keys, a child workspace) and one
/// workspace with links into the home, a dangling link, a loop and
/// project config dirs.
struct Tree {
    _dir: tempfile::TempDir,
    top: PathBuf,
}

impl Tree {
    fn new() -> Self {
        let dir = tempfile::tempdir().expect("temp dir");
        let top = dir.path().canonicalize().expect("real temp dir");
        for path in [
            "home/.eukhe/agents",
            "home/.eukhe/workspaces/s/c",
            "home/.ssh",
            "ws/src",
            "ws/.eukhe",
            "ws/sub/.eukhe",
        ] {
            std::fs::create_dir_all(top.join(path)).expect("dir");
        }
        for path in [
            "home/.eukhe/settings.json",
            "home/.ssh/id",
            "ws/src/a.rs",
            "ws/.eukhe/settings.json",
        ] {
            std::fs::write(top.join(path), "x").expect("file");
        }
        symlink("../home/.eukhe/settings.json", top.join("ws/cfg")).expect("link");
        symlink(top.join("home/.ssh"), top.join("ws/keys")).expect("link");
        symlink(top.join("home/.eukhe/new.json"), top.join("ws/gone")).expect("link");
        symlink("loop2", top.join("ws/loop1")).expect("link");
        symlink("loop1", top.join("ws/loop2")).expect("link");
        Self { _dir: dir, top }
    }

    fn at(&self, path: &str) -> PathBuf {
        self.top.join(path)
    }
}

#[test]
fn real_paths_follow_links_on_the_existing_part() {
    let tree = Tree::new();
    let real = |path: &str| real_path(&tree.at(path));
    assert_eq!(
        [
            real("ws/./src/a.rs"),
            real("ws/cfg"),
            real("ws/keys/id"),
            real("ws/keys/../x"),
            real("ws/gone"),
            real("ws/new/../deep/file"),
            real("ws/src/../../../../../.."),
        ],
        [
            tree.at("ws/src/a.rs"),
            tree.at("home/.eukhe/settings.json"),
            tree.at("home/.ssh/id"),
            tree.at("home/x"),
            tree.at("home/.eukhe/new.json"),
            tree.at("ws/deep/file"),
            PathBuf::from("/"),
        ]
    );
}
