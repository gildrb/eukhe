//! Parser, tokenizer, and section-splitting cases ported from omp
//! `tests/hashline_parse.rs`.

use std::path::Path;

use super::super::{
    input::split_sections,
    mismatch::{mismatch_error, MismatchDetails},
    parser::parse_patch,
    tokenizer::{tokenize, BlockTarget, Token},
    types::{Cursor, Edit, FileOp, PasteTarget},
};

fn cwd() -> &'static Path {
    Path::new("/work")
}

#[test]
fn parses_literal_replace_in_textual_order() {
    let parsed = parse_patch("PUT 2.=3:\n+B\n+C").unwrap();
    assert_eq!(parsed.edits.len(), 4);
    assert!(
        matches!(&parsed.edits[0], Edit::Insert { cursor: Cursor::BeforeAnchor(a), text, replacement: true, .. } if a.line == 2 && text == "B")
    );
    assert!(matches!(&parsed.edits[1], Edit::Insert { text, .. } if text == "C"));
    assert!(matches!(&parsed.edits[2], Edit::Delete { anchor, .. } if anchor.line == 2));
    assert!(matches!(&parsed.edits[3], Edit::Delete { anchor, .. } if anchor.line == 3));
}

#[test]
fn accepts_lenient_range_separators_and_dangling_ranges() {
    for header in ["PUT 2-3:", "PUT 2=3:", "PUT 2..3:", "PUT 2…3:", "PUT 2 3:"] {
        let parsed = parse_patch(&format!("{header}\n+X")).unwrap();
        assert_eq!(
            parsed
                .edits
                .iter()
                .filter(|edit| matches!(edit, Edit::Delete { .. }))
                .count(),
            2,
            "{header}"
        );
    }
    for header in ["PUT 2.=:", "PUT 2-:"] {
        assert_eq!(
            parse_patch(&format!("{header}\n+X")).unwrap().edits.len(),
            2
        );
    }
    assert!(parse_patch("PUT 2.= junk:\n+X").is_err());
}

#[test]
fn parses_all_gap_and_block_targets() {
    let parsed = parse_patch(
        "PUT <2:\n+a\nPUT >3:\n+b\nPUT <1:\n+c\nPUT >$:\n+d\nPUT 4*:\n+e\nPUT >5*:\n+f\nPUT <6*:\n+g\nCUT 7*\nPUT 8* @r",
    )
    .unwrap();
    assert!(
        matches!(&parsed.edits[0], Edit::Insert { cursor: Cursor::BeforeAnchor(a), .. } if a.line == 2)
    );
    assert!(parsed.edits.iter().any(
        |edit| matches!(edit, Edit::Insert { cursor: Cursor::AfterAnchor(a), .. } if a.line == 3)
    ));
    assert!(parsed.edits.iter().any(|edit| matches!(
        edit,
        Edit::Insert {
            cursor: Cursor::Bof,
            ..
        }
    )));
    assert!(parsed.edits.iter().any(|edit| matches!(
        edit,
        Edit::Insert {
            cursor: Cursor::Eof,
            ..
        }
    )));
    for line in [4, 5, 6, 7, 8] {
        assert!(
            parsed
                .edits
                .iter()
                .any(|edit| matches!(edit, Edit::Block { anchor, .. } if anchor.line == line)),
            "block locator on line {line}"
        );
    }
}

#[test]
fn parses_cut_clipboard_and_register_pastes() {
    let parsed = parse_patch("CUT 2.=3 @hold\nPUT <1 @hold\nPUT >$\nPUT 4.=5 @hold").unwrap();
    assert!(matches!(&parsed.edits[0], Edit::Cut { register: Some(name), .. } if name == "hold"));
    assert_eq!(
        parsed
            .edits
            .iter()
            .filter(|edit| matches!(edit, Edit::Delete { .. }))
            .count(),
        2
    );
    assert!(parsed.edits.iter().any(|edit| matches!(edit, Edit::Paste { at: PasteTarget::Gap { cursor: Cursor::Bof }, register: Some(name), .. } if name == "hold")));
    assert!(parsed.edits.iter().any(|edit| matches!(
        edit,
        Edit::Paste {
            at: PasteTarget::Gap {
                cursor: Cursor::Eof
            },
            register: None,
            ..
        }
    )));
    assert!(parsed.edits.iter().any(|edit| matches!(edit, Edit::Paste { at: PasteTarget::Span { range }, .. } if range.start.line == 4 && range.end.line == 5)));
}

#[test]
fn rejects_body_rows_for_bodyless_ops() {
    assert!(parse_patch("CUT 2\n+replacement")
        .unwrap_err()
        .contains("takes no body rows"));
    assert!(parse_patch("PUT >2 @name:")
        .unwrap_err()
        .contains("never takes `:`"));
    assert!(parse_patch("PUT <2\n+X")
        .unwrap_err()
        .contains("without `:` is clipboard-backed"));
}

#[test]
fn empty_put_deletes_but_empty_insert_is_rejected() {
    let parsed = parse_patch("PUT 2.=3:").unwrap();
    assert_eq!(parsed.edits.len(), 2);
    assert!(parsed
        .warnings
        .iter()
        .any(|warning| warning.contains("empty `PUT` body as deletion")));
    assert!(parse_patch("PUT >$:")
        .unwrap_err()
        .contains("promises body rows"));
}

#[test]
fn recovers_bare_snapshot_rows_and_rejects_duplicates() {
    let parsed = parse_patch("2:B\n4|D").unwrap();
    assert_eq!(parsed.edits.len(), 4);
    assert!(parsed
        .warnings
        .iter()
        .any(|warning| warning.contains("snapshot row")));
    let error = parse_patch("2:B\n4:first\n4:second").unwrap_err();
    assert!(error.contains("name line 4") && error.contains("keep only the last row"));
}

#[test]
fn bare_body_prefix_stripping_is_uniform_and_single_pass() {
    let parsed = parse_patch("PUT 2.=3:\n2:foo\n3:bar").unwrap();
    let text: Vec<_> = parsed
        .edits
        .iter()
        .filter_map(|edit| {
            if let Edit::Insert { text, .. } = edit {
                Some(text.as_str())
            } else {
                None
            }
        })
        .collect();
    assert_eq!(text, ["foo", "bar"]);
    let parsed = parse_patch("PUT 2.=3:\n3:keep\nplain").unwrap();
    let text: Vec<_> = parsed
        .edits
        .iter()
        .filter_map(|edit| {
            if let Edit::Insert { text, .. } = edit {
                Some(text.as_str())
            } else {
                None
            }
        })
        .collect();
    assert_eq!(text, ["3:keep", "plain"]);
    let parsed = parse_patch("PUT 2:\n2:42:hello").unwrap();
    assert!(matches!(&parsed.edits[0], Edit::Insert { text, .. } if text == "42:hello"));
}

#[test]
fn preserves_numeric_keyed_bodies() {
    let parsed = parse_patch("PUT 2.=3:\n1: \"one\",\n2: \"two\",").unwrap();
    assert!(matches!(&parsed.edits[0], Edit::Insert { text, .. } if text == "1: \"one\","));
    assert!(matches!(&parsed.edits[1], Edit::Insert { text, .. } if text == "2: \"two\","));
}

#[test]
fn handles_minus_rows_and_markdown_bullets() {
    assert!(parse_patch("PUT 2:\n-old")
        .unwrap_err()
        .contains("`-` rows are not valid"));
    let parsed = parse_patch("PUT 2:\n- item\n  - nested").unwrap();
    assert!(parsed
        .warnings
        .iter()
        .any(|warning| warning.contains("bullet row")));
    let parsed = parse_patch("PUT 2:\n-old\n+new").unwrap();
    assert!(parsed
        .warnings
        .iter()
        .any(|warning| warning.contains("Ignored unified-diff `-old`")));
    assert!(matches!(&parsed.edits[0], Edit::Insert { text, .. } if text == "new"));
}

#[test]
fn warns_when_literal_payload_is_an_op() {
    let parsed = parse_patch("PUT >1:\n+inserted();\n+CUT 2.=3").unwrap();
    assert!(parsed
        .warnings
        .iter()
        .any(|warning| warning.contains("itself a valid hunk header")));
}

#[test]
fn rejects_contaminated_patch_syntax() {
    assert!(parse_patch("*** Update File: a.ts\nPUT 2:\n+X")
        .unwrap_err()
        .contains("apply_patch sentinel"));
    assert!(parse_patch("@@ -1,3 +1,3 @@\nPUT 2:\n+X")
        .unwrap_err()
        .contains("unified-diff hunk header"));
    assert!(parse_patch("2\n+B")
        .unwrap_err()
        .contains("hunk headers need a verb"));
    assert!(parse_patch("2 3\n+X")
        .unwrap_err()
        .contains("Hunk headers need a verb"));
}

#[test]
fn recovers_bare_range_header_as_implicit_put() {
    let parsed = parse_patch("2.=3:\n+X").unwrap();
    assert_eq!(
        parsed
            .edits
            .iter()
            .filter(|edit| matches!(edit, Edit::Delete { .. }))
            .count(),
        2
    );
    assert!(parsed
        .warnings
        .iter()
        .any(|warning| warning.contains("bare `N.=M:` header")));
}

#[test]
fn ignores_copied_read_elisions() {
    let parsed = parse_patch("1:a\n2-3: omitted() { … }\n4:d").unwrap();
    assert_eq!(
        parsed
            .edits
            .iter()
            .filter(|edit| matches!(edit, Edit::Insert { .. }))
            .count(),
        2
    );
    assert!(parsed
        .warnings
        .iter()
        .any(|warning| warning.contains("Ignored copied read-output elision")));
}

#[test]
fn accepts_harmless_cut_colon_with_warning() {
    let parsed = parse_patch("CUT 2.=3:").unwrap();
    assert!(parsed
        .warnings
        .iter()
        .any(|warning| warning.contains("Ignored a trailing `:`")));
}

#[test]
fn cut_supersedes_placeholder_put_on_exact_range() {
    let parsed = parse_patch("PUT 2.=3:\n+// moved block removed\nCUT 2.=3 @block").unwrap();
    assert!(parsed.edits.iter().all(|edit| edit.line_num() != 1));
    assert!(parsed
        .edits
        .iter()
        .any(|edit| matches!(edit, Edit::Cut { register: Some(name), .. } if name == "block")));
}

#[test]
fn preserves_explicit_and_interior_blank_payload_rows() {
    let parsed = parse_patch("PUT 2:\n+\n+\nPUT 4:\n+D").unwrap();
    let payloads: Vec<_> = parsed
        .edits
        .iter()
        .filter_map(|edit| {
            if let Edit::Insert { text, .. } = edit {
                Some(text.as_str())
            } else {
                None
            }
        })
        .collect();
    assert_eq!(payloads, ["", "", "D"]);
    let parsed = parse_patch("PUT 2:\nfirst\n\nsecond").unwrap();
    let payloads: Vec<_> = parsed
        .edits
        .iter()
        .filter_map(|edit| {
            if let Edit::Insert { text, .. } = edit {
                Some(text.as_str())
            } else {
                None
            }
        })
        .collect();
    assert_eq!(payloads, ["first", "", "second"]);
}

#[test]
fn drops_trailing_bare_blank_before_next_hunk() {
    let parsed = parse_patch("PUT 2:\nfoo\n\nPUT 4:\nbaz").unwrap();
    let payloads: Vec<_> = parsed
        .edits
        .iter()
        .filter_map(|edit| {
            if let Edit::Insert { text, .. } = edit {
                Some(text.as_str())
            } else {
                None
            }
        })
        .collect();
    assert_eq!(payloads, ["foo", "baz"]);
}

#[test]
fn abort_terminates_parser_without_warning() {
    let parsed = parse_patch("PUT >1:\n+HELLO\n*** Abort\nPUT >99:\n+never").unwrap();
    assert_eq!(parsed.edits.len(), 1);
    assert!(matches!(&parsed.edits[0], Edit::Insert { text, .. } if text == "HELLO"));
    assert!(parsed.warnings.is_empty());
}

#[test]
fn abort_stops_input_before_later_sections() {
    let patch = split_sections(
        "[a.ts]\nPUT >1:\n+a\n*** Abort\n[b.ts]\nPUT >1:\n+never",
        cwd(),
    )
    .unwrap();
    assert_eq!(patch.len(), 1);
    assert_eq!(patch[0].path, "a.ts");
    assert!(!patch[0].diff.contains("never"));
}

#[test]
fn removed_del_and_copy_headers_are_orphan_rows() {
    for header in ["DEL 2", "DEL.BLK 2", "COPY 2", "COPY.BLK 2"] {
        assert!(parse_patch(header)
            .unwrap_err()
            .contains("payload line has no preceding hunk header"));
    }
}

#[test]
fn detects_and_coalesces_overlapping_hunks() {
    let error = parse_patch("PUT 2.=4:\n+A\nPUT 3.=5:\n+B").unwrap_err();
    assert!(error.contains("anchor line 3 is already targeted by another hunk on line 1"));
    let parsed = parse_patch("2:b\nPUT 2:\n+B").unwrap();
    assert!(parsed.edits.iter().all(|edit| edit.line_num() != 1));
    assert!(parsed
        .warnings
        .iter()
        .any(|warning| warning.contains("kept only the last")));
}

#[test]
fn parses_file_ops_and_rejects_invalid_combinations() {
    assert_eq!(parse_patch("REM").unwrap().file_op, Some(FileOp::Rem));
    assert_eq!(
        parse_patch("MV next.ts").unwrap().file_op,
        Some(FileOp::Move {
            dest: "next.ts".into()
        })
    );
    assert!(parse_patch("PUT 1:\n+x\nREM").unwrap_err().contains("REM"));
    assert!(parse_patch("REM\nMV b.ts")
        .unwrap_err()
        .contains("only one file-level op"));
}

#[test]
fn input_splits_sections_and_normalizes_tags() {
    let patch = split_sections(
        "\n*** Begin Patch\n[a.ts#1a2b]\nPUT 2:\n+B\n[b.ts]\nCUT 3\n*** End Patch\n[c.ts]\nCUT 1",
        cwd(),
    )
    .unwrap();
    assert_eq!(patch.len(), 2);
    assert_eq!(patch[0].path, "a.ts");
    assert_eq!(patch[0].file_hash.as_deref(), Some("1A2B"));
    assert_eq!(patch[0].diff, "PUT 2:\n+B");
    assert_eq!(patch[1].path, "b.ts");
}

#[test]
fn input_recovers_apply_patch_header_noise_and_spaces() {
    let patch = split_sections(
        "[*** Update File: dir with spaces/a.ts#1A2B]\nPUT 1:\n+x",
        cwd(),
    )
    .unwrap();
    assert_eq!(patch[0].path, "dir with spaces/a.ts");
    assert_eq!(patch[0].file_hash.as_deref(), Some("1A2B"));
}

#[test]
fn input_recovers_headers_nested_in_apply_patch_envelope_markers() {
    // Observed in an edit-benchmark trace: the model wrapped the section
    // header in apply_patch framing. The bracketed sentinel must be consumed
    // like a bare `*** Begin Patch` row, not salvaged as the file name.
    let patch =
        split_sections("[*** Begin Patch] [migrations.ts#5275]\nCUT 33.=38", cwd()).unwrap();
    assert_eq!(patch.len(), 1);
    assert_eq!(patch[0].path, "migrations.ts");
    assert_eq!(patch[0].file_hash.as_deref(), Some("5275"));
    assert_eq!(patch[0].diff, "CUT 33.=38");

    // Bracketed markers on their own rows: begin is skipped, end terminates.
    let patch = split_sections(
        "[*** Begin Patch]\n[a.ts#1a2b]\nPUT 2.=2:\n+B\n[*** End Patch]\n[b.ts#3c4d]\nCUT 1",
        cwd(),
    )
    .unwrap();
    assert_eq!(patch.len(), 1);
    assert_eq!(patch[0].path, "a.ts");
    assert_eq!(patch[0].diff, "PUT 2.=2:\n+B");
}

#[test]
fn input_rejects_multi_group_headers_instead_of_inventing_a_path() {
    // Recovery must decline any bracket residue it cannot explain, so the
    // caller sees the malformed header rather than an edit aimed at a file
    // named after the noise.
    for header in ["[Foo] [bar.ts#1A2B]", "[a.ts] [b.ts#1A2B]", "[x] [y]"] {
        let error = split_sections(&format!("{header}\nCUT 1"), cwd())
            .unwrap_err()
            .to_string();
        assert!(error.contains("Input header must be"), "{header}: {error}");
    }

    // Brackets inside a path stay addressable — dynamic-route files are real.
    let patch = split_sections("[app/[slug]/page.tsx#1A2B]\nCUT 1", cwd()).unwrap();
    assert_eq!(patch[0].path, "app/[slug]/page.tsx");
    assert_eq!(patch[0].file_hash.as_deref(), Some("1A2B"));
    let patch = split_sections("[app/[slug]/page.tsx]\nCUT 1", cwd()).unwrap();
    assert_eq!(patch[0].path, "app/[slug]/page.tsx");
}

#[test]
fn input_rejects_malformed_tags_and_missing_headers() {
    for header in [
        "[a.ts#1A2]",
        "[a.ts#1A2G]",
        "[a.ts#1A2B5]",
        "[a.ts#1A2B copied]",
    ] {
        assert!(
            split_sections(&format!("{header}\nPUT 1:\n+x"), cwd())
                .unwrap_err()
                .to_string()
                .contains("Input header must be"),
            "{header}"
        );
    }
    let error = split_sections("CUT 38.=40", cwd()).unwrap_err().to_string();
    assert!(
        error.contains("input must begin with \"[PATH#HASH]\"")
            && error.contains("[src/foo.ts#1A2B]")
    );
}

#[test]
fn input_merges_same_path_sections_and_conflicting_tags_fail() {
    let patch = split_sections(
        "[a.ts#1A2B]\nCUT 1\n[b.ts]\nCUT 2\n[a.ts#1A2B]\nCUT 3",
        cwd(),
    )
    .unwrap();
    assert_eq!(patch.len(), 2);
    assert_eq!(patch[0].diff, "CUT 1\nCUT 3");
    let error = patch[0].parse().unwrap_err().to_string();
    assert!(error.contains("cannot be used in a file whose sections are interleaved"));
    assert!(
        split_sections("[a.ts#1A2B]\nCUT 1\n[a.ts#3C4D]\nCUT 2", cwd())
            .unwrap_err()
            .to_string()
            .contains("Conflicting hashline snapshot tags")
    );
}

#[test]
fn tokenizer_recognizes_headers_ops_payloads_and_envelope() {
    let tokens =
        tokenize("*** Begin Patch\n[a b.ts#1a2b]\nPUT 2.=3:\r\n+x\nCUT 5*\n*** End Patch\n");
    assert!(matches!(&tokens[0], Token::EnvelopeBegin { line_num: 1 }));
    assert!(
        matches!(&tokens[1], Token::Header { path, file_hash: Some(hash), .. } if path == "a b.ts" && hash == "1A2B")
    );
    assert!(matches!(
        &tokens[2],
        Token::OpBlock {
            line_num: 3,
            target: BlockTarget::Replace { .. },
            had_colon: true,
        }
    ));
    assert!(matches!(&tokens[3], Token::PayloadLiteral { text, .. } if text == "x"));
    assert!(matches!(
        &tokens[4],
        Token::OpBlock {
            target: BlockTarget::CutBlock { .. },
            ..
        }
    ));
    assert!(matches!(&tokens[5], Token::EnvelopeEnd { line_num: 6 }));
    assert_eq!(tokens.len(), 6);
}

#[test]
fn reports_invalid_absolute_ranges_and_limits() {
    let error = parse_patch("CUT 5.=2").unwrap_err();
    assert!(error.contains("For one line use `CUT 5`"));
    assert!(error.contains("For 2 lines starting at 5, use `CUT 5.=6`"));
    assert!(parse_patch("PUT 1.=100001:\n+x")
        .unwrap_err()
        .contains("maximum is 100000"));
}

#[test]
fn input_shortens_absolute_paths_in_cwd() {
    let patch =
        split_sections("[/tmp/work/src/a.ts]\nPUT <1:\n+x", Path::new("/tmp/work")).unwrap();
    assert_eq!(patch[0].path, "src/a.ts");
}

#[test]
fn mismatch_messages_distinguish_stale_and_unrecognized_hashes() {
    let stale = MismatchDetails {
        path: "a.ts".into(),
        expected_file_hash: "1A2B".into(),
        actual_file_hash: "3C4D".into(),
        file_lines: vec!["one".into(), "two".into(), "three".into()],
        anchor_lines: vec![2],
        hash_recognized: true,
    };
    let message = mismatch_error(&stale).to_string();
    assert!(message.contains("Edit rejected for a.ts: file changed between read and edit."));
    assert!(message.contains("*2:two"));
    let unknown = MismatchDetails {
        hash_recognized: false,
        ..stale
    };
    assert_eq!(
        mismatch_error(&unknown).to_string(),
        "Edit rejected for a.ts: tag #1A2B is not among the versions of this file that this \
         worker holds (an older read, or one from before a restart).\nThe current file hashes to \
         #3C4D. Re-read the file with `read` and use the [path#tag] header it gives. Do not \
         invent a tag.\n\n 1:one\n*2:two\n 3:three"
    );
}
