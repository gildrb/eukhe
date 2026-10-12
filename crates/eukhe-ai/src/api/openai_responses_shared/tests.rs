use super::normalize_id_part;

#[test]
fn normalize_id_part_sanitizes_truncates_and_trims() {
    assert_eq!(normalize_id_part("call/1+x"), "call_1_x");
    assert_eq!(normalize_id_part("abc___"), "abc");
    let long = "a".repeat(70);
    assert_eq!(normalize_id_part(&long).len(), 64);
}
