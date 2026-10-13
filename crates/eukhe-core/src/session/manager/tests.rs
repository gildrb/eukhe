//! The manager unit battery (moved with its concern): the id mint, the
//! compaction row shape, the ISO round-trip, and the read-only legacy load.

use super::*;

#[test]
fn generated_entry_ids_are_unique_and_link_to_previous_entry() {
    let mut manager = SessionManager::in_memory(Path::new("/tmp"));
    let mut previous = None;
    for _ in 0..1_000 {
        let id = manager.append_custom_entry(
            eukhe_types::custom_type::CustomType::Other("test".to_owned()),
            None,
        );
        let entry = manager.get_all_entries().last().unwrap();
        assert_eq!(entry.id(), Some(id.as_str()));
        assert_eq!(entry.parent_id(), previous.as_deref());
        assert_eq!(id.len(), 8);
        assert!(id.bytes().all(|byte| byte.is_ascii_hexdigit()));
        previous = Some(id);
    }
    assert_eq!(manager.by_id.len(), 1_000);
    assert_eq!(manager.get_leaf_id(), previous.as_deref());
}

/// The compaction row is the full TS `CompactionEntry` record:
/// `fromHook: false` is present (never a missing key), and the details
/// and usage ride along.
#[test]
fn append_compaction_serializes_the_full_ts_record() {
    let tmp = tempfile::tempdir().unwrap();
    let mut manager = SessionManager::in_memory(tmp.path());
    manager.append_compaction(eukhe_types::session::CompactionEntry {
        summary: "the overflow summary".to_string(),
        first_kept_entry_id: "e4".to_string(),
        tokens_before: 214,
        details: Some(serde_json::json!({
            "readFiles": [],
            "modifiedFiles": [],
        })),
        from_hook: Some(false),
        custom_instructions: None,
        usage: Some(eukhe_types::ai::Usage {
            input: 20,
            output: 10,
            cache_read: 80,
            cache_write: 0,
            total_tokens: 110,
            cost: eukhe_types::ai::UsageCost::default(),
        }),
        harness_digest: None,
        harness_state_fingerprint: None,
    });
    let line = serde_json::to_string(
        manager
            .get_entries()
            .iter()
            .rev()
            .find(|entry| matches!(entry, FileEntry::Compaction { .. }))
            .expect("compaction entry appended"),
    )
    .unwrap();
    assert!(line.contains("\"fromHook\":false"));
    assert!(line.contains("\"tokensBefore\":214"));
    assert!(line.contains("\"usage\":"));
}

#[test]
fn iso_format_round_trips() {
    let stamp = format_iso(1_704_067_200_012);
    assert_eq!(stamp, "2024-01-01T00:00:00.012Z");
    assert_eq!(super::super::timestamp_to_millis(&stamp), 1_704_067_200_012);
}

/// Loading a legacy session file is read-only: a torn tail row is skipped
/// in memory, a pre-v3 header migrates in memory, and appends after the
/// load stay in memory — the file keeps its exact bytes throughout (the
/// legacy writer used to repair, migrate, and append by rewriting it).
#[test]
fn loading_a_legacy_file_never_writes_it() {
    let tmp = tempfile::tempdir().unwrap();
    let file = tmp.path().join("legacy.jsonl");
    let header = serde_json::json!({
        "type": "session", "version": 2, "id": "legacy",
        "timestamp": "2026-01-01T00:00:00.000Z", "cwd": "/w"
    });
    let message = serde_json::json!({
        "type": "message", "id": "m1", "parentId": null,
        "timestamp": "2026-01-01T00:00:01.000Z",
        "message": {"role": "user", "content": "hi", "timestamp": 1}
    });
    let content = format!("{header}\n{message}\n{{\"type\":\"message\",\"id\":\"torn");
    std::fs::write(&file, &content).unwrap();

    let mut manager = SessionManager::in_memory(tmp.path());
    manager.set_session_file(file.clone(), None);
    manager.append_session_info("renamed");

    let ids: Vec<Option<&str>> = manager
        .get_all_entries()
        .iter()
        .map(FileEntry::id)
        .collect();
    assert_eq!(
        (
            manager.get_session_id(),
            manager.get_session_file(),
            ids.len(),
            ids[1],
            std::fs::read_to_string(&file).unwrap(),
        ),
        ("legacy", Some(file.as_path()), 3, Some("m1"), content),
    );
}
