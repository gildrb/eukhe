//! omp's snapshot-store contract (`parity_snapshots.json`): tags, version
//! history, retention limits, relocation, and 16-bit tag collisions.

use std::path::PathBuf;

use eukhe_docs::{file_hash, EditStore};

#[test]
#[allow(
    clippy::too_many_lines,
    reason = "omp's single snapshot contract test, kept whole so each assertion maps to its fixture case"
)]
fn snapshot_store_matches_snapshot_contract_cases() {
    let path = PathBuf::from("/tmp/__hashline-snapshots__.ts");
    let other = PathBuf::from("/tmp/__hashline-other__.ts");

    let store = EditStore::new();
    let text = "L1\nL2\nL3\n";
    let tag = store.record(&path, text, None);
    assert_eq!(
        tag,
        file_hash(text),
        "derives the tag from whole-file content (matches computeFileHash)"
    );
    assert_eq!(tag.len(), 4);

    let first = store.record(&path, text, None);
    let second = store.record(&path, text, None);
    assert_eq!(
        second, first,
        "fuses repeated reads of identical content onto one tag"
    );
    assert_eq!(&*store.by_hash(&path, &first).expect("snapshot").text, text);

    let v1 = "one\ntwo\n";
    let v2 = "one\ntwo\nthree\n";
    let tag1 = store.record(&path, v1, None);
    let tag2 = store.record(&path, v2, None);
    assert_ne!(
        tag1, tag2,
        "mints a new tag when content changes and retains the prior version"
    );
    assert_eq!(&*store.by_hash(&path, &tag1).expect("prior").text, v1);
    assert_eq!(
        store.record(&path, v1, None),
        tag1,
        "promotes a re-observed older version back to head"
    );
    assert_eq!(store.head(&path).expect("head").hash, tag1);

    let bounded = EditStore::with_limits(8, 2, usize::MAX);
    let tag_a = bounded.record(&path, "A\n", None);
    let tag_b = bounded.record(&path, "B\n", None);
    let tag_c = bounded.record(&path, "C\n", None);
    assert!(
        bounded.by_hash(&path, &tag_a).is_none(),
        "bounds per-path history to maxVersionsPerPath (oldest dropped)"
    );
    assert!(bounded.by_hash(&path, &tag_b).is_some());
    assert!(bounded.by_hash(&path, &tag_c).is_some());

    let bounded = EditStore::with_limits(1, 4, usize::MAX);
    let cold = bounded.record(&path, "first\n", None);
    bounded.record(&other, "second\n", None);
    assert!(
        bounded.by_hash(&path, &cold).is_none(),
        "bounds tracked paths to maxPaths (cold path evicted)"
    );

    let wide = EditStore::new();
    let early = wide.record(&path, "first\n", None);
    for index in 0..100 {
        wide.record(
            &PathBuf::from(format!("/w/other-{index}.ts")),
            &format!("content {index}\n"),
            None,
        );
    }
    assert_eq!(
        &*wide.by_hash(&path, &early).expect("early tag").text,
        "first\n",
        "keeps an early tag resolvable across a wide session at default capacity"
    );
    assert!(
        wide.by_hash(&other, &early).is_none(),
        "rejects cross-path lookups"
    );

    let mutating = EditStore::new();
    let old = mutating.record(&path, "A\n", Some(&[1]));
    let keep = mutating.record(&other, "B\n", None);
    mutating.invalidate(&path);
    assert!(
        mutating.by_hash(&path, &old).is_none(),
        "invalidate drops one path; clear drops everything"
    );
    assert!(mutating.by_hash(&other, &keep).is_some());
    mutating.clear();
    assert!(mutating.by_hash(&other, &keep).is_none());

    let relocating = EditStore::new();
    let destination = PathBuf::from("/tmp/__hashline-dest__.ts");
    let moved = relocating.record(&path, "A\n", Some(&[1]));
    relocating.relocate(&path, &destination);
    assert!(
        relocating.by_hash(&path, &moved).is_none(),
        "relocate moves version history and read provenance to a new path"
    );
    let snapshot = relocating.by_hash(&destination, &moved).expect("relocated");
    assert_eq!(&*snapshot.text, "A\n");
    assert_eq!(
        snapshot
            .seen_lines
            .expect("seen")
            .into_iter()
            .collect::<Vec<_>>(),
        vec![1]
    );

    let shared = EditStore::new();
    let shared_text = "shared\n";
    let shared_tag = shared.record(&path, shared_text, None);
    shared.record(&other, shared_text, None);
    let mut matches = shared
        .find_by_hash(&shared_tag)
        .into_iter()
        .map(|snapshot| snapshot.path)
        .collect::<Vec<_>>();
    matches.sort();
    assert_eq!(
        matches,
        vec![other, path.clone()],
        "findByHash returns every retained version with that tag across paths"
    );

    let collide_a = "line one 263\nline two 4471\n";
    let collide_b = "line one 410\nline two 6970\n";
    assert_eq!(file_hash(collide_a), file_hash(collide_b));
    let collisions = EditStore::new();
    let collision_tag = collisions.record(&path, collide_a, Some(&[1]));
    assert_eq!(
        collisions.record(&path, collide_b, Some(&[2])),
        collision_tag
    );
    assert_eq!(
        &*collisions
            .by_content(&path, collide_a)
            .expect("collision A")
            .text,
        collide_a,
        "keeps two colliding texts as separate versions with separate seenLines"
    );
    assert_eq!(
        &*collisions
            .by_content(&path, collide_b)
            .expect("collision B")
            .text,
        collide_b
    );
    collisions.record(&path, collide_a, Some(&[2]));
    let seen = collisions
        .by_content(&path, collide_a)
        .expect("repeated collision")
        .seen_lines
        .expect("seen lines");
    assert_eq!(
        seen.into_iter().collect::<Vec<_>>(),
        vec![1, 2],
        "still fuses identical repeated reads of one colliding text onto one snapshot"
    );
}
