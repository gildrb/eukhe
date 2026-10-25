//! Port of pi-codemode `identifier.ts`: the identifier a script uses for a
//! tool, and whether a text is one. The rule runs as the compiled Bend core
//! (`eukhe_bend::rules::codemode_id`; `bend/codemode_id.bend`,
//! `laws/codemode_id.bend`).

use eukhe_bend::rules::codemode_id;
use eukhe_bend::{expect_core, Entry};

/// The identifier a script uses for a tool: characters that are not valid
/// in a JavaScript identifier become `_`. `mcp__docs__search` stays as is,
/// `my-tool` becomes `my_tool`. Iterates code points, like JS `for...of`.
///
/// # Panics
///
/// On a name past the core's wire bound (8 Mi chars) or an inconsistent
/// build ([`expect_core`]).
#[must_use]
pub fn to_codemode_identifier(name: &str) -> String {
    expect_core(Entry::CodemodeId, codemode_id::identifier(name))
}

/// Whether `text` is an identifier scripts can write bare: not empty, an
/// ASCII letter, `_` or `$` first, then also ASCII digits.
///
/// # Panics
///
/// As [`to_codemode_identifier`].
pub(crate) fn is_codemode_identifier(text: &str) -> bool {
    expect_core(Entry::CodemodeId, codemode_id::is_identifier(text))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reaches_the_core() {
        assert_eq!(to_codemode_identifier("my-tool"), "my_tool");
        assert!(is_codemode_identifier("tools"));
    }
}
