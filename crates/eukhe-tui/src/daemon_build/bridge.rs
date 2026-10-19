//! The bridge from the launcher's replacement verdict
//! ([`replacement_verdict`]) to its Bend model (`bend/replace.bend`,
//! docs/daemon.md D1): client starts of any builds by any callers run in
//! both, and `bend/bridge_replace.bend` must print the same transcript,
//! byte for byte. That file documents the events and the output.

use std::fmt::Write as _;

use super::{rank, replacement_verdict, Build, Caller, Relation, Replacement, Tier};
use crate::testing::{compare, Rng, Scenario};

const MODEL: &str = "bend/bridge_replace.bend";

/// Versions that are no release of the usual shape.
const ODD_VERSIONS: [&str; 7] = [
    "0.9.9-main.46",
    "garbage",
    "01.2.3",
    "1.2",
    "1.2.3.4",
    "1..3",
    "1.2.3-",
];

/// The suffixes of generated prerelease versions.
const SUFFIXES: [&str; 3] = ["-dev", "-main.46", "-rc.1"];

fn random_version(rng: &mut Rng) -> String {
    if rng.below(5) == 0 {
        let index = usize::try_from(rng.below(ODD_VERSIONS.len() as u64)).unwrap();
        return ODD_VERSIONS[index].to_string();
    }
    let mut version = format!("{}.{}.{}", rng.below(2), rng.below(12), rng.below(45));
    if rng.below(3) == 0 {
        let index = usize::try_from(rng.below(SUFFIXES.len() as u64)).unwrap();
        version.push_str(SUFFIXES[index]);
    }
    version
}

/// The rank as the model prints it: `-` for none, else its numbers.
fn shown_rank(version: &str) -> String {
    rank(version).map_or_else(
        || "-".to_string(),
        |rank| {
            let tier = match rank.tier {
                Tier::Prerelease => 0,
                Tier::Release => 1,
            };
            format!("{}.{}.{tier}.{}", rank.major, rank.minor, rank.patch)
        },
    )
}

fn scenario(rng: &mut Rng) -> Scenario {
    // The builds: a version and an id number each. Ids repeat sometimes,
    // and versions repeat with other ids.
    let count = rng.range(1, 5);
    let mut builds: Vec<(String, u64)> = Vec::new();
    for index in 0..count {
        let version = match builds.first() {
            Some((first, _)) if rng.below(4) == 0 => first.clone(),
            Some(_) | None => random_version(rng),
        };
        let id = if rng.below(8) == 0 { 0 } else { index };
        builds.push((version, id));
    }
    let ids: Vec<String> = builds.iter().map(|(_, id)| format!("build-{id}")).collect();
    let mut events = String::new();
    let mut transcript = String::new();
    let mut daemon: Option<usize> = None;
    let mut replaced = 0u64;
    for _ in 0..rng.range(1, 12) {
        let client = usize::try_from(rng.below(count)).unwrap();
        let caller = if rng.below(2) == 0 {
            Caller::Interactive
        } else {
            Caller::Background
        };
        let (version, id) = &builds[client];
        let letter = match caller {
            Caller::Interactive => 'i',
            Caller::Background => 'b',
        };
        writeln!(events, "s {version} {id} {letter}").unwrap();
        let word = match daemon {
            None => {
                daemon = Some(client);
                "start"
            }
            Some(running) => {
                let verdict = replacement_verdict(
                    Build {
                        version,
                        id: &ids[client],
                    },
                    Build {
                        version: &builds[running].0,
                        id: &ids[running],
                    },
                    caller,
                );
                match verdict {
                    Replacement::Replace => {
                        daemon = Some(client);
                        replaced += 1;
                        "replace"
                    }
                    Replacement::Keep(Relation::Same) => "same",
                    Replacement::Keep(Relation::Older) => "older",
                    Replacement::Keep(Relation::Newer) => "newer",
                    Replacement::Keep(Relation::Other) => "other",
                }
            }
        };
        let running = daemon.unwrap();
        let (version, id) = &builds[running];
        writeln!(transcript, "{word} {} {id}", shown_rank(version)).unwrap();
    }
    writeln!(transcript, "r {replaced}").unwrap();
    Scenario {
        name: format!("{count} builds"),
        events,
        transcript,
    }
}

/// Client starts of a few builds (releases, dev and older-scheme builds,
/// text that is no version, repeated ids and versions) by interactive and
/// background callers.
#[test]
fn the_replacement_verdict_runs_as_its_model() {
    let mut rng = Rng(0x0e1d_ba11);
    let scenarios: Vec<Scenario> = (0..80).map(|_| scenario(&mut rng)).collect();
    compare(MODEL, scenarios);
}
