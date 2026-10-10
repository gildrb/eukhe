//! The client-side path argument of `/export` and `/import` (TS
//! `getPathCommandArgument`). The exported file itself is the daemon-side
//! exporter (the `export_html`/`export_jsonl` commands).

/// Parse the path argument of `/export` or `/import` (TS
/// `getPathCommandArgument`): `None` for no argument; a quoted argument runs
/// to its closing quote; an unquoted one ends at the first whitespace.
pub fn path_command_argument(text: &str, command: &str) -> Option<String> {
    if text == command {
        return None;
    }
    let rest = text.strip_prefix(&format!("{command} "))?;
    let rest = rest.trim_start();
    let first = rest.chars().next()?;
    if first == '"' || first == '\'' {
        let quoted = rest.chars().skip(1).collect::<String>();
        let close = quoted.find(first)?;
        return Some(quoted[..close].to_string());
    }
    match rest.find(char::is_whitespace) {
        Some(index) => Some(rest[..index].to_string()),
        None => Some(rest.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The `/export` path argument parses exactly like the TS helper:
    /// missing, bare, quoted, and whitespace-terminated arguments.
    #[test]
    fn path_arguments_parse() {
        assert_eq!(path_command_argument("/export", "/export"), None);
        assert_eq!(
            path_command_argument("/export out.html", "/export"),
            Some("out.html".to_string())
        );
        assert_eq!(
            path_command_argument("/export   out.html  ", "/export"),
            Some("out.html".to_string())
        );
        assert_eq!(
            path_command_argument("/export \"my file.html\"", "/export"),
            Some("my file.html".to_string())
        );
        assert_eq!(
            path_command_argument("/export 'my file.jsonl' extra", "/export"),
            Some("my file.jsonl".to_string())
        );
        assert_eq!(
            path_command_argument("/export a b c", "/export"),
            Some("a".to_string())
        );
        // An unclosed quote is no argument at all (TS returns undefined).
        assert_eq!(path_command_argument("/export \"unclosed", "/export"), None);
    }
}
