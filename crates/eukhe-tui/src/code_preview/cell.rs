//! Port of `packages/coding-agent/src/core/tools/ipython-cell-code.ts`.

use super::shapes::PreviewShape;
use crate::text_shapes::TextShape;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedIpythonBashCell {
    pub body: String,
}

/// Detect an `%%bash` cell magic (after blank lines) and return the cell
/// body that follows its line.
#[must_use]
pub fn parse_ipython_bash_cell(code: &str) -> Option<ParsedIpythonBashCell> {
    let magic = PreviewShape::BashMagic.find(code)?;
    Some(ParsedIpythonBashCell {
        body: code[magic.end()..].to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_bash_cell() {
        let p = parse_ipython_bash_cell("%%bash\necho hi").unwrap();
        assert_eq!(p.body, "echo hi");
    }

    #[test]
    fn ignores_leading_blank_lines() {
        let p = parse_ipython_bash_cell("\n\t\n  %%bash -l\nls").unwrap();
        assert_eq!(p.body, "ls");
    }

    #[test]
    fn no_magic() {
        assert!(parse_ipython_bash_cell("print(1)").is_none());
        assert!(parse_ipython_bash_cell("x = '%%bash'").is_none());
        assert!(parse_ipython_bash_cell("  %%bashish\n").is_none());
    }
}
