//! YAML frontmatter parsing. Port of utils/frontmatter.ts.

use serde_json::Value;

fn normalize_newlines(value: &str) -> String {
    value
        .trim_start_matches('\u{feff}')
        .replace("\r\n", "\n")
        .replace('\r', "\n")
}

fn extract_frontmatter(content: &str) -> (Option<String>, String) {
    let normalized = normalize_newlines(content);
    if !normalized.starts_with("---") {
        return (None, normalized);
    }
    let Some(end_index) = normalized[3..].find("\n---") else {
        return (None, normalized);
    };
    // end_index is relative to offset 3; the yaml block runs from offset 4 to
    // the absolute close, the body starts after "\n---" (4 chars from the
    // find position). An EMPTY block (the close follows the open, e.g.
    // `---\n---`) is NO frontmatter on the TS side (`!yamlString`), and its
    // slice bounds are inverted (4 > 3) — fall back to the whole document
    // instead of slicing.
    let Some(yaml) = normalized.get(4..end_index + 3) else {
        return (None, normalized);
    };
    if yaml.is_empty() {
        return (None, normalized);
    }
    let body = normalized[end_index + 3 + 4..].trim().to_string();
    (Some(yaml.to_string()), body)
}

/// Parse `---` YAML frontmatter into a JSON object plus the body.
#[must_use]
pub fn parse_frontmatter(content: &str) -> (Value, String) {
    let (yaml_string, body) = extract_frontmatter(content);
    let Some(yaml_string) = yaml_string else {
        return (serde_json::Map::new().into(), body);
    };
    // YAML 1.2 booleans only, as the TS `yaml` package: `off`/`yes` stay
    // strings.
    let options = serde_saphyr::options! { strict_booleans: true };
    let converted: Value = match serde_saphyr::from_str_with_options(&yaml_string, options) {
        Ok(parsed) => parsed,
        Err(_) => return (serde_json::Map::new().into(), body),
    };
    let frontmatter = if converted.is_null() {
        serde_json::Map::new().into()
    } else {
        converted
    };
    (frontmatter, body)
}

/// The body with frontmatter stripped.
#[must_use]
pub fn strip_frontmatter(content: &str) -> String {
    parse_frontmatter(content).1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_simple_frontmatter() {
        let (frontmatter, body) =
            parse_frontmatter("---\nname: my-skill\ndescription: A skill\n---\nUse it well.");
        assert_eq!(frontmatter["name"], "my-skill");
        assert_eq!(frontmatter["description"], "A skill");
        assert_eq!(body, "Use it well.");
    }

    #[test]
    fn no_frontmatter_returns_body() {
        let (frontmatter, body) = parse_frontmatter("Just text");
        assert!(frontmatter.as_object().unwrap().is_empty());
        assert_eq!(body, "Just text");
    }

    #[test]
    fn unterminated_frontmatter_returns_body() {
        let (frontmatter, body) = parse_frontmatter("---\nname: x\nno end");
        assert!(frontmatter.as_object().unwrap().is_empty());
        assert_eq!(body, "---\nname: x\nno end");
    }

    #[test]
    fn an_empty_frontmatter_block_is_no_frontmatter() {
        // TS `!yamlString`: the close follows the open, so the whole
        // document is the body (the slice bounds are inverted, which
        // previously panicked).
        for text in ["---\n---\nbody", "---\n---", "---\n----\nbody"] {
            let (frontmatter, body) = parse_frontmatter(text);
            assert!(frontmatter.as_object().unwrap().is_empty(), "{text}");
            assert_eq!(body, text, "{text} is the body verbatim");
        }
    }

    #[test]
    fn an_empty_first_line_between_delimiters_is_no_frontmatter() {
        // `---x\n---\nbody`: TS slice(4, 4) = "" -> falsy -> no frontmatter.
        let (frontmatter, body) = parse_frontmatter("---x\n---\nbody");
        assert!(frontmatter.as_object().unwrap().is_empty());
        assert_eq!(body, "---x\n---\nbody");
    }

    #[test]
    fn crlf_and_bom_normalized() {
        let (frontmatter, _) = parse_frontmatter("\u{feff}---\r\nname: x\r\n---\r\nbody");
        assert_eq!(frontmatter["name"], "x");
    }

    #[test]
    fn yaml_scalars_resolve_as_the_ts_yaml_package() {
        // TS `yaml.parse`: YAML 1.1 words stay strings, and a clipped block
        // scalar keeps its final line break at the close.
        let (frontmatter, _) = parse_frontmatter(
            "---\nname: x\nsignals: [off, yes, n, true]\ndescription: |\n  a\n  b\n---\nbody",
        );
        assert_eq!(
            frontmatter,
            serde_json::json!({
                "name": "x",
                "signals": ["off", "yes", "n", true],
                "description": "a\nb\n",
            })
        );
    }
}
