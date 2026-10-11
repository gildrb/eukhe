use super::{normalize_id_part, supports_explicit_cache_breakpoints};

#[test]
fn normalize_id_part_sanitizes_truncates_and_trims() {
    assert_eq!(normalize_id_part("call/1+x"), "call_1_x");
    assert_eq!(normalize_id_part("abc___"), "abc");
    let long = "a".repeat(70);
    assert_eq!(normalize_id_part(&long).len(), 64);
}

#[test]
fn explicit_cache_breakpoint_models() {
    for id in [
        "gpt-5.6",
        "gpt-5.6-sol",
        "gpt-5.10",
        "gpt-6",
        "gpt-6-astra",
        "gpt-6.1-sol",
    ] {
        assert!(supports_explicit_cache_breakpoints(id), "{id}");
    }
    for id in ["gpt-5.5", "gpt-5", "gpt-5.6sol", "gpt-60", "gpt-4o"] {
        assert!(!supports_explicit_cache_breakpoints(id), "{id}");
    }
}
