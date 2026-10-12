//! omp's TypeScript parity fixtures for the hashline parser and applier
//! (`tests/fixtures/hashline/parity_*.json`), run against the private API.

use std::{collections::HashMap, path::Path};

use serde_json::{json, Value};

use super::super::{apply::apply_edits, parser::parse_patch, types::FileOp};
use crate::store::Clipboard;

const FIXTURES: &[&str] = &[
    "parity_boundary_repair.json",
    "parity_block.json",
    "parity_clipboard.json",
    "parity_core_contracts.json",
    "parity_file_ops.json",
    "parity_format_v2.json",
    "parity_landing_shift.json",
    "parity_leniency.json",
    "parity_patcher.json",
    "parity_recovery_session_chain.json",
];

/// Cases whose expected result comes from omp's tree-sitter parse probe
/// (boundary repair, annotation echoes, opener escapes, broken-parse
/// warnings). Every one targets a `.ts`/`.tsx`/`.rs` path; without grammars
/// eukhe behaves as omp does for a path without one. They need tree-sitter
/// (Phase 5).
const NEEDS_TREE_SITTER: &[(&str, &str)] = &[
    (
        "parity_boundary_repair.json",
        "counts a separately inserted closer immediately below the range",
    ),
    (
        "parity_boundary_repair.json",
        "counts earlier kept closers in later projected prefixes",
    ),
    (
        "parity_boundary_repair.json",
        "counts head insertions before replacement payloads in original coordinates",
    ),
    (
        "parity_boundary_repair.json",
        "does not let an earlier kept closer cover a later orphan closer",
    ),
    (
        "parity_boundary_repair.json",
        "does not let an unterminated template in one hunk mask a missing closer in another",
    ),
    (
        "parity_boundary_repair.json",
        "does not resurrect a swallowed signature when body indentation matches",
    ),
    (
        "parity_boundary_repair.json",
        "drops a JSX closer echo after a self-closing tag with a greater-than prop expression",
    ),
    (
        "parity_boundary_repair.json",
        "drops a duplicated multi-line closing block (the Root.tsx incident)",
    ),
    (
        "parity_boundary_repair.json",
        "drops a leading attribute echo in a single-line replacement",
    ),
    (
        "parity_boundary_repair.json",
        "drops a one-sided JSX closer echo in a single-line expansion",
    ),
    (
        "parity_boundary_repair.json",
        "drops a trailing attribute echo in a single-line replacement",
    ),
    (
        "parity_boundary_repair.json",
        "drops a trailing decorator echo in a single-line replacement",
    ),
    (
        "parity_boundary_repair.json",
        "drops the echo when the body carries several new doc rows",
    ),
    (
        "parity_boundary_repair.json",
        "flags a range that swallows a lifetime-carrying signature line",
    ),
    (
        "parity_boundary_repair.json",
        "ignores non-contiguously deleted openers when choosing which closer to keep",
    ),
    (
        "parity_boundary_repair.json",
        "keeps an omitted inner closer when the outer closer survives below",
    ),
    (
        "parity_boundary_repair.json",
        "keeps an omitted outer closer even when the payload restates an inner closer",
    ),
    (
        "parity_boundary_repair.json",
        "keeps only the non-restated outer closer for a nested deleted suffix",
    ),
    (
        "parity_boundary_repair.json",
        "keeps the closer when the matching opener is replaced rather than removed",
    ),
    (
        "parity_boundary_repair.json",
        "preserves a duplicated opener when it does not account for the imbalance",
    ),
    (
        "parity_boundary_repair.json",
        "rejects a single-line annotation echo whose body cannot fill the range",
    ),
    (
        "parity_boundary_repair.json",
        "rejects a swallowed leading closer when the payload claims the block interior",
    ),
    (
        "parity_boundary_repair.json",
        "rejects sparing a deleted closer when the payload claims no position inside the block",
    ),
    (
        "parity_boundary_repair.json",
        "retains a swallowed opening comment fence when syntax and indentation prove the boundary",
    ),
    (
        "parity_boundary_repair.json",
        "spares a leading closer the range swallowed when the payload claims sibling depth",
    ),
    (
        "parity_boundary_repair.json",
        "spares the deleted closing line when the payload omits it",
    ),
    (
        "parity_boundary_repair.json",
        "spares the swallowed leading closer when the authored edit does not parse",
    ),
    (
        "parity_boundary_repair.json",
        "spends the missing-closer residual on the genuine hunk, not an earlier wrapper removal",
    ),
    (
        "parity_boundary_repair.json",
        "still keeps a missing closer when another hunk's dupSuffix repair masks the raw delta",
    ),
    (
        "parity_boundary_repair.json",
        "still spares a closer when the payload indentation claims the block interior",
    ),
    (
        "parity_boundary_repair.json",
        "warns when a balance-neutral edit stops the file parsing",
    ),
    (
        "parity_boundary_repair.json",
        "warns when a balanced payload's range ends mid-block",
    ),
    (
        "parity_landing_shift.json",
        "abandons the escape when the relocated result does not parse",
    ),
    (
        "parity_landing_shift.json",
        "escapes a shallower function body past a class in TypeScript",
    ),
    (
        "parity_landing_shift.json",
        "lands a tab-indented construct body after the block, not inside the opener",
    ),
];

fn fixture(name: &str) -> Value {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/hashline")
        .join(name);
    serde_json::from_str(
        &std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display())),
    )
    .unwrap_or_else(|error| panic!("parse {}: {error}", path.display()))
}

fn legacy_error(message: &str) -> &str {
    message
        .strip_prefix("InvalidAbsoluteRangeError: ")
        .or_else(|| message.strip_prefix("Error: "))
        .unwrap_or(message)
}

fn file_op_value(op: Option<&FileOp>) -> Value {
    match op {
        None => Value::Null,
        Some(FileOp::Rem) => json!({ "kind": "rem" }),
        Some(FileOp::Move { dest }) => json!({ "kind": "move", "dest": dest }),
    }
}

fn check_parse(call: &Value) -> Result<(), String> {
    let input = call["input"].as_str().expect("parse input");
    match (parse_patch(input), call["error"].as_str()) {
        (Ok(parsed), None) => {
            let expected = &call["expect"];
            let actual = json!({
                "editCount": parsed.edits.len(),
                "fileOp": file_op_value(parsed.file_op.as_ref()),
                "warnings": parsed.warnings,
            });
            let wanted = json!({
                "editCount": expected["editCount"],
                "fileOp": expected["fileOp"],
                "warnings": expected["warnings"],
            });
            if actual == wanted {
                Ok(())
            } else {
                Err(format!(
                    "parse {input:?}\n  expected {wanted}\n  actual   {actual}"
                ))
            }
        }
        (Err(error), Some(expected)) if error == legacy_error(expected) => Ok(()),
        (Err(error), expected) => Err(format!(
            "parse {input:?}\n  expected error {expected:?}\n  actual error   {error:?}"
        )),
        (Ok(parsed), Some(expected)) => Err(format!(
            "parse {input:?}\n  expected error {expected:?}, got {} edits",
            parsed.edits.len()
        )),
    }
}

fn clipboard_from(value: &Value) -> Clipboard {
    let strings = |value: &Value| -> Vec<String> {
        value
            .as_array()
            .expect("string array")
            .iter()
            .map(|line| line.as_str().expect("string").to_owned())
            .collect()
    };
    Clipboard {
        lines: value.get("lines").filter(|v| !v.is_null()).map(strings),
        named: value["named"].as_object().map(|registers| {
            registers
                .iter()
                .map(|(name, lines)| (name.clone(), strings(lines)))
                .collect::<HashMap<_, _>>()
        }),
        pending_anon_cuts: value
            .get("pendingAnonCuts")
            .filter(|v| !v.is_null())
            .map(strings),
    }
}

fn check_apply(call: &Value) -> Result<(), String> {
    let input = call["input"].as_str().expect("apply input");
    let parsed = parse_patch(input).map_err(|error| format!("apply input {input:?}: {error}"))?;
    let mut clipboard = call
        .get("clipboard")
        .map_or_else(Clipboard::default, clipboard_from);
    let text = call["text"].as_str().expect("apply source text");
    match (
        apply_edits(text, &parsed.edits, &mut clipboard),
        call["error"].as_str(),
    ) {
        (Ok(actual), None) => {
            let expected = &call["expect"];
            let actual = json!({
                "text": actual.text,
                "firstChangedLine": actual.first_changed_line,
                "warnings": actual.warnings,
            });
            let wanted = json!({
                "text": expected["text"],
                "firstChangedLine": expected["firstChangedLine"],
                "warnings": expected.get("warnings").cloned().unwrap_or_else(|| json!([])),
            });
            if actual == wanted {
                Ok(())
            } else {
                Err(format!(
                    "apply {input:?} to {text:?}\n  expected {wanted}\n  actual   {actual}"
                ))
            }
        }
        (Err(error), Some(expected)) if error.to_string() == legacy_error(expected) => Ok(()),
        (Err(error), expected) => Err(format!(
            "apply {input:?} to {text:?}\n  expected error {expected:?}\n  actual error   {:?}",
            error.to_string()
        )),
        (Ok(actual), Some(expected)) => Err(format!(
            "apply {input:?} to {text:?}\n  expected error {expected:?}, got {:?}",
            actual.text
        )),
    }
}

#[test]
fn parser_and_applier_match_omp_parity_fixtures() {
    let mut failures = Vec::new();
    let mut calls = 0_usize;
    let mut skipped = 0_usize;
    for fixture_name in FIXTURES {
        let root = fixture(fixture_name);
        for case in root["cases"].as_array().expect("fixture cases") {
            let case_name = case["name"].as_str().expect("case name");
            if NEEDS_TREE_SITTER.contains(&(*fixture_name, case_name)) {
                skipped += 1;
                continue;
            }
            let parses = case["parse"]
                .as_array()
                .into_iter()
                .flatten()
                .map(check_parse);
            let applies = case["apply"].as_array().into_iter().flatten().map(|call| {
                if call["onEmptyPaste"].as_str() == Some("drop") {
                    return Ok(());
                }
                check_apply(call)
            });
            for result in parses.chain(applies) {
                calls += 1;
                if let Err(message) = result {
                    failures.push(format!("{fixture_name}: {case_name}: {message}"));
                }
            }
        }
    }
    assert_eq!(
        skipped,
        NEEDS_TREE_SITTER.len(),
        "every skipped case exists"
    );
    assert!(calls > 0);
    assert!(
        failures.is_empty(),
        "{} call(s) failed:\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}
