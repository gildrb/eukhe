use std::ffi::OsString;
use std::os::unix::fs::symlink;
use std::path::PathBuf;

use eukhe_types::path_policy::{PathClass, PathPolicy, PathRule};

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

    fn policy(&self) -> PathPolicy {
        PathPolicy::new(
            vec![self.at("ws"), self.at("home/.eukhe/workspaces/s/c")],
            vec![
                PathRule::Dir(self.at("home/.eukhe")),
                PathRule::Tree(self.at("home/.eukhe/agents")),
                PathRule::Tree(self.at("ws/.eukhe")),
                PathRule::Named(OsString::from(".eukhe")),
            ],
            vec![self.at("home/.ssh")],
        )
    }
}

#[test]
fn a_path_is_judged_by_its_real_path() {
    let tree = Tree::new();
    let policy = tree.policy();
    let classes: Vec<(&str, PathClass)> = [
        "ws/src/a.rs",
        "ws/new/deep/file",
        "ws/cfg",
        "ws/keys/id",
        "ws/gone",
        "ws/loop1",
        "ws/.eukhe/settings.json",
        "ws/sub/.eukhe/x",
        "ws",
        "home",
        "",
        "home/.eukhe/workspaces/s/c/file",
        "home/other.txt",
        "ws/src/../../home/.ssh/id",
        "ws/keys/../x",
        "home/.eukhe/agents/main.cfg",
        "home/.eukhe/settings.json",
    ]
    .into_iter()
    .map(|path| (path, judge_path(&policy, &tree.at(path)).class))
    .collect();
    assert_eq!(
        classes,
        [
            ("ws/src/a.rs", PathClass::Inside),
            ("ws/new/deep/file", PathClass::Inside),
            ("ws/cfg", PathClass::Protected),
            ("ws/keys/id", PathClass::Secret),
            ("ws/gone", PathClass::Protected),
            ("ws/loop1", PathClass::Outside),
            ("ws/.eukhe/settings.json", PathClass::Protected),
            ("ws/sub/.eukhe/x", PathClass::Protected),
            ("ws", PathClass::Protected),
            ("home", PathClass::Protected),
            ("", PathClass::Protected),
            ("home/.eukhe/workspaces/s/c/file", PathClass::Inside),
            ("home/other.txt", PathClass::Outside),
            ("ws/src/../../home/.ssh/id", PathClass::Secret),
            ("ws/keys/../x", PathClass::Outside),
            ("home/.eukhe/agents/main.cfg", PathClass::Protected),
            ("home/.eukhe/settings.json", PathClass::Protected),
        ]
    );
}

#[test]
fn a_dir_that_holds_a_secret_is_known() {
    let tree = Tree::new();
    let policy = tree.policy();
    assert_eq!(
        ["home", "ws", "ws/keys", "home/.ssh/id", "home/.eukhe"].map(|path| judge_path(
            &policy,
            &tree.at(path)
        )
        .holds_secret),
        [true, false, true, true, false]
    );
}
