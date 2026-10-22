//! The bridge from the pages of [`glob`] to their Bend model
//! (`bend/doc_search.bend`, laws `continuation_progresses`,
//! `continuation_contiguous` and `continuation_disjoint` of
//! `LAWS.bend` section `documents`): generated files with times that are often equal
//! run through the Rust code, which follows each continuation the result
//! gives, and `bend/bridge_doc_search.bend` must print the same
//! transcript, byte for byte.
//!
//! A scenario's events are `o S K` (a glob that skips S paths, with limit
//! K) and one `p I M` for each file `eI`, changed M seconds after the
//! epoch. Each page prints `f I I ...` (its files, by number) and `r C`
//! (the skip of its continuation; `r -`: none); the next page is the one
//! at C.

use std::{
    fmt::Write as _,
    fs::File,
    num::NonZeroUsize,
    time::{Duration, SystemTime},
};

use super::{glob, GlobOutput, GlobRequest};
use crate::{
    notice::NoticeKind,
    testing::{compare, Rng, Scenario},
};

const MODEL: &str = "bend/bridge_doc_search.bend";

/// The `f` line of one page: the number of each file `eNN`.
fn page(output: &GlobOutput) -> String {
    let mut line = "f".to_owned();
    for entry in &output.matches {
        let number: u64 = entry
            .path
            .strip_prefix('e')
            .and_then(|digits| digits.parse().ok())
            .expect("a generated file name");
        let _ = write!(line, " {number}");
    }
    line.push('\n');
    line
}

/// The skip of the continuation the result gives, from its notice.
fn continuation(output: &GlobOutput) -> Option<u64> {
    output
        .notices
        .iter()
        .filter(|notice| notice.kind == NoticeKind::Pagination)
        .find_map(|notice| notice.continuation.as_deref()?.strip_prefix("skip="))
        .map(|skip| skip.parse().expect("a numeric skip"))
}

/// `glob` pages the paths of the tree as the model does on 200 scenarios
/// of up to 24 files, with times that are often equal, and each
/// continuation it gives returns the next page.
#[test]
fn the_glob_pages_equal_the_bend_model() {
    let mut rng = Rng(0x6c0b_5eed_d0c5_0007);
    let scenarios = (0..200).map(|at| {
        let directory = tempfile::tempdir().expect("temp directory");
        let count = rng.below(25);
        let skip = match rng.below(4) {
            0 => 0,
            1.. => rng.below(count + 3),
        };
        let limit = rng.range(1, 7);
        let mut events = vec![format!("o {skip} {limit}")];
        for index in 0..count {
            let modified = rng.below(5);
            let file =
                File::create(directory.path().join(format!("e{index:02}"))).expect("fixture file");
            file.set_modified(SystemTime::UNIX_EPOCH + Duration::from_secs(1_000 + modified))
                .expect("fixture time");
            events.push(format!("p {index} {modified}"));
        }
        let mut transcript = String::new();
        let mut next = Some(skip);
        while let Some(skip) = next {
            let output = glob(
                directory.path(),
                &GlobRequest {
                    path: ".".to_owned(),
                    hidden: false,
                    gitignore: false,
                    limit: NonZeroUsize::new(usize::try_from(limit).expect("a small limit")),
                    skip,
                },
                &crate::gate::Open,
            )
            .expect("glob succeeds");
            transcript.push_str(&page(&output));
            next = continuation(&output);
            match next {
                Some(skip) => {
                    let _ = writeln!(transcript, "r {skip}");
                }
                None => transcript.push_str("r -\n"),
            }
        }
        Scenario {
            name: format!("glob-pages-{at}"),
            events: events.join("\n"),
            transcript,
        }
    });
    compare(MODEL, scenarios.collect::<Vec<_>>());
}
