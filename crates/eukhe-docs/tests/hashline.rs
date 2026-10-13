//! Session-level hashline coverage: omp's patcher fixture and the
//! coding-agent, loop-guard, seen-line, and block parity cases that do not
//! need tree-sitter.

mod common;

use common::{DiskWriter, Workspace};
use eukhe_docs::{file_hash, FileChange, FileOutcome, HashlineOutcome};

#[test]
fn patcher_fixture_cases() {
    common::run_fixture("patcher.json");
}

#[test]
fn result_text_has_new_tag_and_compact_preview() {
    let ws = Workspace::new();
    let path = ws.write("a.txt", "one\ntwo\nthree\n");
    let tag = ws.snapshot("a.txt", "one\ntwo\nthree\n", None);
    let outcome = ws
        .apply(
            &format!("[a.txt#{tag}]\nPUT 2.=2:\n+TWO"),
            &DiskWriter::default(),
        )
        .expect("apply");
    let new_tag = file_hash("one\nTWO\nthree\n");
    assert_eq!(
        outcome,
        HashlineOutcome {
            text: format!("[a.txt#{new_tag}]\n1:one\n2:TWO\n3:three"),
            files: vec![FileOutcome {
                display: "a.txt".into(),
                absolute: path,
                change: FileChange::Updated,
                diff: " 1|one\n-2|two\n+2|TWO\n 3|three".into(),
                first_changed_line: Some(2),
                warnings: Vec::new(),
                tag: Some(new_tag.clone()),
                text: format!("[a.txt#{new_tag}]\n1:one\n2:TWO\n3:three"),
            }],
        }
    );
    // The written text is the new snapshot: its tag anchors the next edit.
    ws.apply(
        &format!("[a.txt#{new_tag}]\nPUT 3.=3:\n+THREE"),
        &DiskWriter::default(),
    )
    .expect("chained edit");
    assert_eq!(ws.read("a.txt").as_deref(), Some("one\nTWO\nTHREE\n"));
}

#[test]
fn identical_noop_escalates_on_third_attempt() {
    let ws = Workspace::new();
    ws.write("a.txt", "same\n");
    let tag = ws.snapshot("a.txt", "same\n", None);
    let input = format!("[a.txt#{tag}]\nPUT 1.=1:\n+same");
    for _ in 0..2 {
        let outcome = ws
            .apply(&input, &DiskWriter::default())
            .expect("soft no-op");
        assert_eq!(
            outcome.text,
            "Edits to a.txt parsed and applied cleanly, but produced no change: your body row(s) \
             are byte-identical to the file at the targeted lines. The bug is somewhere else — \
             re-read the file before issuing another edit. Do NOT widen the payload or add lines; \
             verify the anchor first."
        );
    }
    let error = ws
        .apply(&input, &DiskWriter::default())
        .expect_err("third no-op must fail");
    assert!(error
        .to_string()
        .starts_with("STOP. Edits to a.txt have been a byte-identical no-op 3 times in a row"));
}

#[test]
fn noop_counter_is_per_path_and_resets_after_a_commit() {
    let paths = Workspace::new();
    for name in ["a.txt", "b.txt"] {
        paths.write(name, "same\n");
        let tag = paths.snapshot(name, "same\n", None);
        let input = format!("[{name}#{tag}]\nPUT 1.=1:\n+same");
        for _ in 0..2 {
            assert!(paths.apply(&input, &DiskWriter::default()).is_ok());
        }
    }

    let reset = Workspace::new();
    reset.write("a.txt", "same\n");
    let old_tag = reset.snapshot("a.txt", "same\n", None);
    let noop = format!("[a.txt#{old_tag}]\nPUT 1.=1:\n+same");
    assert!(reset.apply(&noop, &DiskWriter::default()).is_ok());
    reset
        .apply(
            &format!("[a.txt#{old_tag}]\nPUT 1.=1:\n+changed"),
            &DiskWriter::default(),
        )
        .expect("a real edit resets the counter");
    let changed_tag = reset.snapshot("a.txt", "changed\n", None);
    let changed_noop = format!("[a.txt#{changed_tag}]\nPUT 1.=1:\n+changed");
    for _ in 0..2 {
        assert!(reset.apply(&changed_noop, &DiskWriter::default()).is_ok());
    }
}

#[test]
fn coding_agent_executor_cases() {
    let create = Workspace::new();
    let error = create
        .apply(
            "[new.ts]\nPUT <1:\n+export const x = 1;\n",
            &DiskWriter::default(),
        )
        .expect_err("rejects file creation and directs to the write tool");
    assert!(error.to_string().contains("write tool"));
    assert!(create.read("new.ts").is_none());

    let inserts = Workspace::new();
    inserts.write("a.ts", "aaa\nbbb\nccc");
    let tag = inserts.snapshot("a.ts", "aaa\nbbb\nccc", None);
    let outcome = inserts
        .apply(
            &format!("[a.ts#{tag}]\nPUT >$:\n+bbb\n+ccc\n+NEW\n"),
            &DiskWriter::default(),
        )
        .expect("applies duplicate pure-insert payload literally");
    assert_eq!(
        inserts.read("a.ts").as_deref(),
        Some("aaa\nbbb\nccc\nbbb\nccc\nNEW")
    );
    assert!(!outcome.text.contains("Auto-dropped"));
    assert!(!outcome.text.contains("Auto-absorbed"));

    let bom = Workspace::new();
    bom.write("Program.cs", "\u{feff}using A;\n");
    let tag = bom.snapshot("Program.cs", "using A;\n", None);
    bom.apply(
        &format!("[Program.cs#{tag}]\nPUT 1.=1:\n+using B;\n"),
        &DiskWriter::default(),
    )
    .expect("preserves UTF-8 BOM bytes");
    assert_eq!(
        bom.read("Program.cs").as_deref(),
        Some("\u{feff}using B;\n")
    );

    let crlf = Workspace::new();
    crlf.write("a.txt", "one\r\ntwo\r\n");
    let tag = crlf.snapshot("a.txt", "one\r\ntwo\r\n", None);
    crlf.apply(
        &format!("[a.txt#{tag}]\nPUT 2.=2:\n+TWO"),
        &DiskWriter::default(),
    )
    .expect("preserves CRLF line endings");
    assert_eq!(crlf.read("a.txt").as_deref(), Some("one\r\nTWO\r\n"));

    let atomic = Workspace::new();
    atomic.write("a.ts", "aaa\n");
    atomic.write("b.ts", "bbb\n");
    let a_tag = atomic.snapshot("a.ts", "aaa\n", None);
    let writer = DiskWriter::default();
    assert!(
        atomic
            .apply(
                &format!("[a.ts#{a_tag}]\nPUT 1.=1:\n+AAA\n[b.ts#FFFF]\nPUT 1.=1:\n+BBB"),
                &writer,
            )
            .is_err(),
        "preflights every section before writing multi-file edits"
    );
    assert_eq!(writer.writes(), 0);
    assert_eq!(atomic.read("a.ts").as_deref(), Some("aaa\n"));

    let original = (1..=10)
        .map(|line| format!("L{line}"))
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    let sections = Workspace::new();
    sections.write("a.ts", &original);
    let tag = sections.snapshot("a.ts", &original, None);
    sections
        .apply(
            &format!(
                "[a.ts#{tag}]\nPUT 2.=2:\n+L2a\n+L2b\n+L2c\n+L2d\n+L2e\n+L2f\n+L2g\n+L2h\n+L2i\n\
                 [a.ts#{tag}]\nPUT >8:\n+INSERTED"
            ),
            &DiskWriter::default(),
        )
        .expect("applies same-file sections against the original snapshot");
    assert_eq!(
        sections.read("a.ts").as_deref(),
        Some(
            "L1\nL2a\nL2b\nL2c\nL2d\nL2e\nL2f\nL2g\nL2h\nL2i\nL3\nL4\nL5\nL6\nL7\nL8\nINSERTED\nL9\n\
             L10\n"
        )
    );
}

#[test]
fn seen_line_guard_rejects_hidden_anchors_and_accepts_seen_ones() {
    let source = "one\ntwo\nthree\n";
    let mut hidden = Workspace::new();
    hidden.enforce_seen_lines = true;
    hidden.write("a.txt", source);
    let tag = hidden.snapshot("a.txt", source, Some(&[2]));
    let error = hidden
        .apply(
            &format!("[a.txt#{tag}]\nPUT 3.=3:\n+THREE"),
            &DiskWriter::default(),
        )
        .expect_err("rejects an edit on a line the partial read never displayed");
    assert_eq!(
        error.to_string(),
        format!(
            "This edit anchors to lines 3 of a.txt that [a.txt#{tag}] never displayed (it showed \
             a partial range, a search hit, or a folded summary). Actual file content at those \
             lines:\n  3:three\nVerify the content matches what you intend to touch, then \
             re-issue the edit with the same [path#tag] header — a straight retry now succeeds \
             without a re-read. If the content does NOT match, fix your line numbers."
        )
    );
    assert_eq!(hidden.read("a.txt").as_deref(), Some(source));
    hidden
        .apply(
            &format!("[a.txt#{tag}]\nPUT 3.=3:\n+THREE"),
            &DiskWriter::default(),
        )
        .expect("the revealed line is now seen; a straight retry succeeds");
    assert_eq!(hidden.read("a.txt").as_deref(), Some("one\ntwo\nTHREE\n"));
}

const BLOCK_RESOLVER_UNAVAILABLE: &str = "line 1: Block locators (`N*` in `PUT N*:`, `PUT >N*`, \
                                           `CUT N*`) are not available here (no block resolver \
                                           configured). Use a concrete line range.";

#[test]
fn insert_after_block_on_an_opener_is_rejected_and_the_file_unchanged() {
    let source = "function x() {\n  if (y) {\n  }\n}\n";
    let ws = Workspace::new();
    ws.write("x.ts", source);
    let tag = ws.snapshot("x.ts", source, None);
    let writer = DiskWriter::default();
    let error = ws
        .apply(&format!("[x.ts#{tag}]\nPUT >1*:\n+  z();"), &writer)
        .expect_err("`PUT >N*:` must not land inside the block");
    assert_eq!(error.to_string(), BLOCK_RESOLVER_UNAVAILABLE);
    assert_eq!(ws.read("x.ts").as_deref(), Some(source));
    assert_eq!(writer.writes(), 0);
}

#[test]
fn every_block_locator_form_is_rejected() {
    let source = "function x() {\n  if (y) {\n  }\n}\n";
    for op in [
        "PUT 1*:\n+function w() {}",
        "PUT 1*:",
        "PUT <2*:\n+  z();",
        "PUT >2*:\n+  z();",
        "CUT 2*",
        "CUT 2* @hold",
        "PUT 2* @hold",
        "PUT >3* @hold",
        "PUT >3*",
    ] {
        let ws = Workspace::new();
        ws.write("x.ts", source);
        let tag = ws.snapshot("x.ts", source, None);
        let error = ws
            .apply(&format!("[x.ts#{tag}]\n{op}"), &DiskWriter::default())
            .expect_err(op);
        assert_eq!(error.to_string(), BLOCK_RESOLVER_UNAVAILABLE, "{op}");
        assert_eq!(ws.read("x.ts").as_deref(), Some(source), "{op}");
    }
}

/// Same drift as `stale_edit_rebases_when_anchor_remap_cannot_prove_one_offset`
/// (only the byte rebase can apply it), but line 6 was never displayed.
#[test]
fn byte_rebase_runs_the_seen_line_guard_on_the_snapshot() {
    let live = "a\nb\nc\nd\nX\ne\nf\n";
    let mut ws = Workspace::new();
    ws.enforce_seen_lines = true;
    ws.write("a.txt", live);
    let tag = ws.snapshot("a.txt", "a\nb\nc\nd\ne\nf\n", Some(&[1, 2, 3]));
    let error = ws
        .apply(
            &format!("[a.txt#{tag}]\nPUT 2.=2:\n+B\nPUT 6.=6:\n+F"),
            &DiskWriter::default(),
        )
        .expect_err("line 6 was never displayed by the tagged read");
    assert_eq!(
        error.to_string(),
        format!(
            "This edit anchors to lines 6 of a.txt that [a.txt#{tag}] never displayed (it showed \
             a partial range, a search hit, or a folded summary). Actual file content at those \
             lines:\n  6:f\nVerify the content matches what you intend to touch, then re-issue \
             the edit with the same [path#tag] header — a straight retry now succeeds without a \
             re-read. If the content does NOT match, fix your line numbers."
        )
    );
    assert_eq!(ws.read("a.txt").as_deref(), Some(live));
}

/// Two texts with the same 16-bit tag (from omp's snapshot contract).
const COLLIDE_READ: &str = "line one 263\nline two 4471\n";
const COLLIDE_LIVE: &str = "line one 410\nline two 6970\n";

#[test]
fn colliding_tag_with_different_live_text_is_stale() {
    assert_eq!(file_hash(COLLIDE_READ), file_hash(COLLIDE_LIVE));
    let ws = Workspace::new();
    ws.write("a.txt", COLLIDE_LIVE);
    let tag = ws.snapshot("a.txt", COLLIDE_READ, None);
    let writer = DiskWriter::default();
    let error = ws
        .apply(&format!("[a.txt#{tag}]\nPUT 1.=1:\n+changed"), &writer)
        .expect_err("the tag names the read text, not the live one");
    assert!(error
        .to_string()
        .starts_with("Edit rejected for a.txt: file changed between read and edit."));
    assert_eq!(writer.writes(), 0);
    assert_eq!(ws.read("a.txt").as_deref(), Some(COLLIDE_LIVE));
}

#[test]
fn colliding_tag_matches_when_the_live_text_was_read() {
    let ws = Workspace::new();
    ws.write("a.txt", COLLIDE_LIVE);
    ws.snapshot("a.txt", COLLIDE_READ, None);
    let tag = ws.snapshot("a.txt", COLLIDE_LIVE, None);
    ws.apply(
        &format!("[a.txt#{tag}]\nPUT 1.=1:\n+changed"),
        &DiskWriter::default(),
    )
    .expect("the live text was read under this tag");
    assert_eq!(
        ws.read("a.txt").as_deref(),
        Some("changed\nline two 6970\n")
    );
}

#[test]
fn stale_tag_remaps_anchors_onto_shifted_lines() {
    let ws = Workspace::new();
    ws.write("a.txt", "inserted\none\ntwo\nthree\n");
    let tag = ws.snapshot("a.txt", "one\ntwo\nthree\n", None);
    let outcome = ws
        .apply(
            &format!("[a.txt#{tag}]\nPUT 2.=2:\n+TWO"),
            &DiskWriter::default(),
        )
        .expect("anchor remap recovers the shift");
    assert_eq!(
        ws.read("a.txt").as_deref(),
        Some("inserted\none\nTWO\nthree\n")
    );
    assert!(outcome.text.ends_with(
        "Warnings:\nRecovered by remapping stale line anchors to unchanged current lines (file \
         changed since the tagged read). Verify the diff matches your intent."
    ));
}

#[test]
fn stale_edit_rebases_when_anchor_remap_cannot_prove_one_offset() {
    let ws = Workspace::new();
    ws.write("a.txt", "a\nb\nc\nd\nX\ne\nf\n");
    let tag = ws.snapshot("a.txt", "a\nb\nc\nd\ne\nf\n", None);
    let outcome = ws
        .apply(
            &format!("[a.txt#{tag}]\nPUT 2.=2:\n+B\nPUT 6.=6:\n+F"),
            &DiskWriter::default(),
        )
        .expect("the rebase carries both edits past the inserted line");
    assert_eq!(ws.read("a.txt").as_deref(), Some("a\nB\nc\nd\nX\ne\nF\n"));
    assert_eq!(
        outcome.files[0].warnings,
        [
            "Recovered by rebasing your edit onto the current file (it changed since the tagged \
          read; your edit touched only regions that are unchanged since then). Verify the diff \
          matches your intent."
        ]
    );
}

#[test]
fn stale_edit_overlapping_the_other_writer_is_rejected() {
    let ws = Workspace::new();
    ws.write("a.txt", "a\nOTHER\nc\nd\nX\ne\nf\n");
    let tag = ws.snapshot("a.txt", "a\nb\nc\nd\ne\nf\n", None);
    let error = ws
        .apply(
            &format!("[a.txt#{tag}]\nPUT 2.=2:\n+B\nPUT 6.=6:\n+F"),
            &DiskWriter::default(),
        )
        .expect_err("both sides changed line 2");
    assert!(
        error
            .to_string()
            .starts_with("Edit rejected for a.txt: file changed between read and edit."),
        "{error}"
    );
    assert_eq!(
        ws.read("a.txt").as_deref(),
        Some("a\nOTHER\nc\nd\nX\ne\nf\n")
    );
}

#[test]
fn write_drift_is_recorded_and_warned() {
    let ws = Workspace::new();
    ws.write("a.txt", "one\n");
    let tag = ws.snapshot("a.txt", "one\n", None);
    let writer = DiskWriter {
        rewrite: Some("ONE  \n".into()),
        ..DiskWriter::default()
    };
    let outcome = ws
        .apply(&format!("[a.txt#{tag}]\nPUT 1.=1:\n+ONE"), &writer)
        .expect("apply");
    let landed = file_hash("ONE  \n");
    assert_eq!(outcome.files[0].tag.as_deref(), Some(landed.as_str()));
    assert_eq!(
        outcome.files[0].warnings,
        [
            "a.txt: the file on disk after this write differs from what was sent — the client \
          (editor/IDE) likely reformatted it on save (e.g. format-on-save, tab/space settings). \
          The returned snapshot reflects the actual file; re-read before further edits if the \
          extra changes were unexpected."
        ]
    );
}

#[test]
fn writer_receives_the_read_bytes_for_compare_and_swap() {
    let ws = Workspace::new();
    let path = ws.write("a.txt", "\u{feff}one\r\n");
    let tag = ws.snapshot("a.txt", "one\n", None);
    let writer = DiskWriter::default();
    ws.apply(
        &format!("[a.txt#{tag}]\nPUT 1.=1:\n+ONE\nMV b.txt"),
        &writer,
    )
    .expect("edit and move");
    assert_eq!(
        *writer.requests.lock().expect("lock"),
        [common::RecordedWrite {
            absolute: path,
            op: "move",
            before_raw: Some("\u{feff}one\r\n".into()),
        }]
    );
    assert_eq!(ws.read("b.txt").as_deref(), Some("\u{feff}ONE\r\n"));
}
