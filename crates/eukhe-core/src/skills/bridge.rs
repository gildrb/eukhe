//! The bridge between the skill and template loaders
//! ([`load_skills_from_dir`], [`load_prompt_templates`]) and their Bend
//! model (`bend/skill_load.bend`, whose laws `PROOF.bend` proves): the
//! Rust test writes each scenario's candidate files into a temp dir, runs
//! the real loaders over it, and prints what became of each file; the
//! model prints the same from the scenario. `bend/bridge_skill_load.bend`
//! documents the scenario format.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::{load_prompt_templates, load_skills_from_dir, LoadPromptTemplatesOptions};
use super::{ResourceDiagnostic, Skill};

/// Write candidate `i` (`kind` 0: a skill, 1: a template) with `outcome`
/// (0: good, 1: unreadable, 2: malformed frontmatter, 3: no description)
/// and return its path.
fn write_candidate(rng: &mut Rng, root: &Path, i: usize, kind: u64, outcome: u64) -> PathBuf {
    let path = if kind == 0 {
        let dir = root.join("skills").join(format!("s{i}"));
        std::fs::create_dir_all(&dir).unwrap();
        dir.join("SKILL.md")
    } else {
        root.join("prompts").join(format!("p{i}.md"))
    };
    match outcome {
        0 => std::fs::write(
            &path,
            format!("---\nname: s{i}\ndescription: Candidate {i}\n---\nbody"),
        )
        .unwrap(),
        1 if rng.chance(50) => std::fs::write(&path, [0xff, 0xfe, 0x00]).unwrap(),
        1 => std::os::unix::fs::symlink(root.join(format!("gone{i}.md")), &path).unwrap(),
        2 => std::fs::write(
            &path,
            format!("---\nname: s{i}\ndescription: [x\n---\nbody"),
        )
        .unwrap(),
        _ => std::fs::write(&path, format!("---\nname: s{i}\n---\nbody")).unwrap(),
    }
    path
}

/// One scenario: its candidates, for the model, and what the Rust loaders
/// did with each.
fn scenario(seed: u64, files: usize) -> (String, String) {
    let mut rng = Rng(seed);
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path();
    std::fs::create_dir_all(root.join("skills")).unwrap();
    std::fs::create_dir_all(root.join("prompts")).unwrap();
    let mut events = String::new();
    let mut candidates = Vec::new();
    for i in 0..files {
        let kind = rng.below(2);
        // A template has no required description: outcome 3 is a skill's.
        let outcome = rng.below(if kind == 0 { 4 } else { 3 });
        writeln!(events, "{kind} {outcome}").unwrap();
        candidates.push(write_candidate(&mut rng, root, i, kind, outcome));
    }
    let skills = load_skills_from_dir(&root.join("skills"), "user");
    let templates = load_prompt_templates(&LoadPromptTemplatesOptions {
        cwd: root.to_path_buf(),
        agent_dir: root.join("agent"),
        prompt_paths: vec![root.join("prompts").display().to_string()],
        include_defaults: false,
    });
    let loaded: Vec<String> = skills
        .skills
        .iter()
        .map(|skill: &Skill| skill.file_path.display().to_string())
        .chain(templates.templates.iter().map(|t| t.file_path.clone()))
        .collect();
    let diagnostics: Vec<(String, &str)> = skills
        .diagnostics
        .iter()
        .chain(&templates.diagnostics)
        .filter_map(|diagnostic| match diagnostic {
            ResourceDiagnostic::Warning { message, path }
            | ResourceDiagnostic::Error { message, path } => {
                path.clone().map(|path| (path, message.as_str()))
            }
            ResourceDiagnostic::Collision { message, path, .. } => {
                Some((path.clone(), message.as_str()))
            }
        })
        .collect();
    let mut transcript = String::new();
    for path in candidates {
        let path = path.display().to_string();
        let kind = diagnostics
            .iter()
            .find(|(named, _)| *named == path)
            .map(|(_, message)| {
                if message.starts_with("invalid frontmatter") {
                    1
                } else if *message == "description is required" {
                    2
                } else {
                    0
                }
            });
        let line = match (loaded.contains(&path), kind) {
            (true, None) => "L".to_owned(),
            (true, Some(_)) => "LD".to_owned(),
            (false, None) => "S".to_owned(),
            (false, Some(kind)) => format!("R {kind}"),
        };
        writeln!(transcript, "{line}").unwrap();
    }
    (events, transcript)
}

#[test]
fn the_rust_skill_loaders_equal_the_bend_model() {
    let scenarios = (1..=30).map(|seed| {
        let (events, transcript) = scenario(seed, 12);
        Scenario {
            name: seed.to_string(),
            events,
            transcript,
        }
    });
    compare("bend/bridge_skill_load.bend", scenarios);
}
