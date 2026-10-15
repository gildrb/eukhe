//! Port of pi-codemode `identifier.ts`: the identifier a script uses for a
//! tool.

/// The identifier a script uses for a tool: characters that are not valid
/// in a JavaScript identifier become `_`. `mcp__docs__search` stays as is,
/// `my-tool` becomes `my_tool`. Iterates code points, like JS `for...of`.
#[must_use]
pub fn to_codemode_identifier(name: &str) -> String {
    let mut identifier = String::with_capacity(name.len());
    for c in name.chars() {
        let valid = if identifier.is_empty() {
            c.is_ascii_alphabetic() || c == '_' || c == '$'
        } else {
            c.is_ascii_alphanumeric() || c == '_' || c == '$'
        };
        identifier.push(if valid { c } else { '_' });
    }
    if identifier.is_empty() {
        identifier.push('_');
    }
    identifier
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keeps_valid_identifiers() {
        assert_eq!(
            to_codemode_identifier("mcp__docs__search"),
            "mcp__docs__search"
        );
        assert_eq!(to_codemode_identifier("$x_1"), "$x_1");
    }

    #[test]
    fn replaces_invalid_characters() {
        assert_eq!(to_codemode_identifier("my-tool"), "my_tool");
        assert_eq!(to_codemode_identifier("1st.tool"), "_st_tool");
        assert_eq!(to_codemode_identifier("a😀b"), "a_b");
        assert_eq!(to_codemode_identifier("é"), "_");
    }

    #[test]
    fn empty_name_is_underscore() {
        assert_eq!(to_codemode_identifier(""), "_");
    }
}
