//! ANSI styling of plain command output (chalk's rules): colors only on a
//! terminal stdout without `NO_COLOR`. The decision is a value the caller
//! makes once, so rendered text never depends on where stdout points.

use std::io::IsTerminal as _;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum Styling {
    #[default]
    Plain,
    Ansi,
}

impl Styling {
    /// chalk's enable rule for stdout.
    pub(crate) fn for_stdout() -> Self {
        if std::env::var_os("NO_COLOR").is_none() && std::io::stdout().is_terminal() {
            Styling::Ansi
        } else {
            Styling::Plain
        }
    }

    /// Wrap `text` in SGR `code` with chalk's reset (dim closes with 22,
    /// colors with 39).
    pub(crate) fn paint(self, code: Sgr, text: &str) -> String {
        match self {
            Styling::Ansi => {
                let (open, close) = match code {
                    Sgr::Dim => ("2", "22"),
                    Sgr::Red => ("31", "39"),
                    Sgr::Green => ("32", "39"),
                    Sgr::Yellow => ("33", "39"),
                };
                format!("\x1b[{open}m{text}\x1b[{close}m")
            }
            Styling::Plain => text.to_string(),
        }
    }
}

/// The SGR styles the command output uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Sgr {
    Dim,
    Red,
    Green,
    Yellow,
}
