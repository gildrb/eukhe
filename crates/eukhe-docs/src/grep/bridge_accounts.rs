//! The bridge from what [`grep_with`] searched, its notices and its pages to
//! their Bend model (`bend/doc_search.bend`, laws
//! `grep_accounts_every_file`, `grep_notes_every_gap`,
//! `grep_notes_every_cut` and the continuation laws of
//! `laws/doc_search.bend`): generated trees run through the Rust code and
//! `bend/bridge_doc_search.bend` must print the same transcript, byte for
//! byte.
//!
//! A tree holds entries `e00`, `e01`, ... in walk order: text files with
//! up to 40 matching lines (some over a small size limit), binary files,
//! files that do not open, directories that hold only `node_modules` or
//! `.git`, symlinks, and directories that do not open. The search keeps 20
//! matches of a file and a small total. A scenario's events are
//! `g 20 S 20 R` (skip S, R matches in all), then `t I H B` for a text file
//! with H matches, over the size limit when B is 1, or `s I W` for a skipped
//! entry (W: 0 binary, 1 does not open, 2 excluded, 3 symlink, 4 walk
//! error). The transcript is the account (`c`), the notices of each class
//! (`n`), the files with a cut notice (`x`), the files of the page (`f`),
//! the continuation (`r`) and the files of its page.
//!
//! A file or a directory with no permissions is still open to root: then
//! the scenario has the file as a text file and no entry for the directory,
//! as the Rust code sees them.

use std::{
    fmt::Write as _,
    fs,
    os::unix::fs::{symlink, PermissionsExt as _},
    path::{Path, PathBuf},
};

use super::{
    grep_with, GrepLimits, GrepOutput, GrepRequest, DEFAULT_FILE_LIMIT, MULTI_FILE_PER_FILE_MATCHES,
};
use crate::{
    notice::NoticeKind,
    store::EditStore,
    testing::{compare, Rng, Scenario},
};

const MODEL: &str = "bend/bridge_doc_search.bend";
/// The size limit of the generated searches: a text file has at most 40
/// matching lines of 2 bytes, so all its matches are inside it.
const MAX_FILE_BYTES: u64 = 128;

/// The number of a generated entry `eNN`.
fn number(path: &str) -> u64 {
    path.strip_prefix('e')
        .and_then(|digits| digits.get(..2))
        .and_then(|digits| digits.parse().ok())
        .expect("a generated entry name")
}

/// The `f` line of one page.
fn page(output: &GrepOutput) -> String {
    let mut line = "f".to_owned();
    for file in &output.files {
        let _ = write!(line, " {}", number(&file.path));
    }
    line.push('\n');
    line
}

/// Grep `root` for `x` with `skip`.
fn search(root: &Path, skip: u64, total_matches: u64) -> GrepOutput {
    grep_with(
        &EditStore::new(),
        root,
        &GrepRequest {
            pattern: "x".to_owned(),
            path: ".".to_owned(),
            glob: None,
            ignore_case: false,
            gitignore: false,
            context_before: 0,
            context_after: 0,
            skip,
            limit: None,
        },
        &crate::gate::Open,
        GrepLimits {
            max_file_bytes: MAX_FILE_BYTES,
            total_matches,
        },
        &|| {},
    )
    .expect("grep succeeds")
}

/// What the Rust code does with the tree, as the model prints it.
fn transcript(root: &Path, skip: u64, total_matches: u64) -> String {
    let output = search(root, skip, total_matches);
    let account = output.account;
    let mut text = format!(
        "c {} {} {} {} {} {} {} {} {} {}\n",
        account.no_match,
        account.shown,
        account.paged_out,
        account.not_searched,
        account.binary,
        account.unreadable,
        account.excluded,
        account.symlink,
        account.walk_error,
        account.partial
    );
    let skipped = |what: &str| {
        output.notices.iter().any(|notice| {
            notice.kind == NoticeKind::Skipped
                && notice
                    .text
                    .split_once(' ')
                    .is_some_and(|(_, rest)| rest.starts_with(what))
        })
    };
    let partial = output
        .notices
        .iter()
        .any(|notice| notice.kind == NoticeKind::PartialScan);
    let not_searched = output.notices.iter().any(|notice| {
        notice.kind == NoticeKind::LimitReached && notice.text.contains(" files not searched: ")
    });
    let noted = [
        skipped("binary files"),
        skipped("unreadable files"),
        skipped("excluded directories"),
        skipped("symlinks"),
        skipped("walk errors"),
        partial,
        not_searched,
    ];
    text.push('n');
    for present in noted {
        let _ = write!(text, " {}", u8::from(present));
    }
    text.push_str("\nx");
    for notice in &output.notices {
        let cut = notice.kind == NoticeKind::LimitReached
            && notice
                .continuation
                .as_deref()
                .is_some_and(|next| next.starts_with("path="));
        if cut {
            let _ = write!(text, " {}", number(&notice.text));
        }
    }
    text.push('\n');
    text.push_str(&page(&output));
    let next = output
        .notices
        .iter()
        .filter(|notice| notice.kind == NoticeKind::Pagination)
        .find_map(|notice| notice.continuation.as_deref()?.strip_prefix("skip="))
        .map(|next| next.parse::<u64>().expect("a numeric skip"));
    match next {
        Some(next) => {
            let _ = writeln!(text, "r {next}");
            text.push_str(&page(&search(root, next, total_matches)));
        }
        None => text.push_str("r -\n"),
    }
    text
}

/// Makes the generated entry `eNN` (NN: `index`) in `root` and returns
/// its event, or `None` when the walk does not see it. A path made with no
/// permissions goes into `closed`, to give them back before the cleanup.
fn entry(rng: &mut Rng, root: &Path, index: u64, closed: &mut Vec<PathBuf>) -> Option<String> {
    let path = root.join(format!("e{index:02}"));
    let no_access = fs::Permissions::from_mode(0o000);
    match rng.below(14) {
        0..=7 => {
            let hits = match rng.below(4) {
                0 => 0,
                1 => rng.range(21, 40),
                2.. => rng.range(1, 20),
            };
            let big = rng.below(5) == 0;
            let mut content = "x\n".repeat(usize::try_from(hits).expect("few matches"));
            if big {
                content.push_str(&"y".repeat(200));
            }
            content.push_str("y\n");
            fs::write(&path, content).expect("text file");
            Some(format!("t {index} {hits} {}", u8::from(big)))
        }
        8 => {
            fs::write(&path, "x\0\n").expect("binary file");
            Some(format!("s {index} 0"))
        }
        9 => {
            fs::write(&path, "x\n").expect("closed file");
            fs::set_permissions(&path, no_access).expect("chmod file");
            closed.push(path.clone());
            match fs::read(&path) {
                Ok(_) => Some(format!("t {index} 1 0")),
                Err(_) => Some(format!("s {index} 1")),
            }
        }
        10 => {
            let excluded = if rng.below(2) == 0 {
                "node_modules"
            } else {
                ".git"
            };
            let inner = path.join(excluded);
            fs::create_dir_all(&inner).expect("excluded directory");
            fs::write(inner.join("a.txt"), "x\n").expect("excluded file");
            Some(format!("s {index} 2"))
        }
        11 | 12 => {
            let target = if rng.below(2) == 0 { "e00" } else { "missing" };
            symlink(target, &path).expect("symlink");
            Some(format!("s {index} 3"))
        }
        13.. => {
            fs::create_dir(&path).expect("closed directory");
            fs::set_permissions(&path, no_access).expect("chmod directory");
            closed.push(path.clone());
            match fs::read_dir(&path) {
                Ok(_) => None,
                Err(_) => Some(format!("s {index} 4")),
            }
        }
    }
}

/// `grep_with` accounts for every walked entry, gives the notices and
/// pages, and follows its continuation as the model does on 150 generated
/// trees of up to 70 entries, with totals that often stop the search.
#[test]
fn the_grep_accounts_equal_the_bend_model() {
    let mut rng = Rng(0x93e9_acc0_5eed_0006);
    let scenarios = (0..150).map(|at| {
        let directory = tempfile::tempdir().expect("temp directory");
        let total_matches = match rng.below(2) {
            0 => GrepLimits::DEFAULT.total_matches,
            1.. => rng.range(1, 300),
        };
        let skip = match rng.below(4) {
            0 | 1 => 0,
            2 => 20,
            3.. => rng.below(50),
        };
        let mut events = vec![format!(
            "g {MULTI_FILE_PER_FILE_MATCHES} {skip} {DEFAULT_FILE_LIMIT} {total_matches}"
        )];
        let mut closed = Vec::new();
        for index in 0..rng.range(1, 70) {
            events.extend(entry(&mut rng, directory.path(), index, &mut closed));
        }
        let transcript = transcript(directory.path(), skip, total_matches);
        for path in closed {
            fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).expect("chmod back");
        }
        Scenario {
            name: format!("grep-accounts-{at}"),
            events: events.join("\n"),
            transcript,
        }
    });
    compare(MODEL, scenarios.collect::<Vec<_>>());
}
