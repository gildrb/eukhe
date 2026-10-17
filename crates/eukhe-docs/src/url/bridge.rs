//! The bridge from the internal URL paths ([`Url::names`]) to their Bend
//! model (`bend/tools.bend` §3, docs/tools.md S7): generated paths of
//! names, `..`, `.` and empty segments run through the Rust code, and
//! `bend/bridge_paths.bend` must print the same transcript, byte for byte.
//!
//! A scenario file (no trailing newline) has one path a line, its segments
//! separated by spaces: `nN` (the name `sN`), `u` (`..`), `h` (`.` or an
//! empty segment). Each prints `B NAMES`: B is 1 when the path is accepted
//! and 0 when it is rejected; NAMES is ` -` when rejected, else ` N` for
//! each name it reaches, deepest first.

use super::{Scheme, Url};
use crate::testing::{compare, Rng, Scenario};

const MODEL: &str = "bend/bridge_paths.bend";

/// One generated path: the model's tokens and the URL path the Rust code
/// reads.
fn path(rng: &mut Rng) -> (String, String) {
    let mut tokens = Vec::new();
    let mut segments = Vec::new();
    for _ in 0..rng.below(9) {
        match rng.below(7) {
            0..=2 => {
                let name = rng.below(4);
                tokens.push(format!("n{name}"));
                segments.push(format!("s{name}"));
            }
            3 | 4 => {
                tokens.push("u".to_owned());
                segments.push("..".to_owned());
            }
            5 => {
                tokens.push("h".to_owned());
                segments.push(".".to_owned());
            }
            6.. => {
                tokens.push("h".to_owned());
                segments.push(String::new());
            }
        }
    }
    (tokens.join(" "), segments.join("/"))
}

/// What the Rust code does with `path`, as the model prints it.
fn resolved(path: &str) -> String {
    let url = Url {
        scheme: Scheme::Repo,
        path,
    };
    match url.names() {
        Ok(names) => {
            let mut line = "1".to_owned();
            for name in names.iter().rev() {
                line.push(' ');
                line.push_str(name.trim_start_matches('s'));
            }
            line.push('\n');
            line
        }
        Err(_) => "0 -\n".to_owned(),
    }
}

/// [`Url::names`] accepts and resolves the paths the model does on 200
/// scenarios of 1 to 12 paths: names, `..` at and above the root, `.` and
/// empty segments, and empty paths.
#[test]
fn the_rust_paths_equal_the_bend_model() {
    let mut rng = Rng(0x7a1b_c0de_5eed_0007);
    let scenarios = (0..200).map(|at| {
        let mut events = Vec::new();
        let mut transcript = String::new();
        for _ in 0..rng.range(1, 12) {
            let (tokens, path) = path(&mut rng);
            transcript.push_str(&resolved(&path));
            events.push(tokens);
        }
        Scenario {
            name: format!("paths-{at}"),
            events: events.join("\n"),
            transcript,
        }
    });
    compare(MODEL, scenarios.collect::<Vec<_>>());
}
