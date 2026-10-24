//! The dashboard's token tables (`bend/tokens.bend`, entry
//! `bend/ffi_tokens.bend`; `laws/tokens.bend`) as the lines of
//! `crates/eukhe-dashboard/ui/src/tokens.stylex.ts` that hold them. The web
//! app's `StyleX` build needs the values as literals in that file, so the
//! compiled core writes them: [`blocks`] answers the generated blocks, a
//! test checks the file holds them, and its ignored twin writes them
//! (`make dashboard-tokens`).

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// A generated block of `tokens.stylex.ts`: the object it fills, and its
/// lines in order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub name: String,
    pub lines: Vec<String>,
}

/// The generated blocks, in file order.
#[must_use]
pub fn blocks() -> Vec<Block> {
    expect_core(Entry::Tokens, blocks_call())
}

fn blocks_call() -> Result<Vec<Block>, Error> {
    let mut request = Writer::new();
    request.tag(0);
    let reply = call(Entry::Tokens, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let mut blocks = Vec::new();
    for _ in 0..reader.count()? {
        let name = reader.str()?.to_owned();
        let mut lines = Vec::new();
        for _ in 0..reader.count()? {
            lines.push(reader.str()?.to_owned());
        }
        blocks.push(Block { name, lines });
    }
    reader.end()?;
    Ok(blocks)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    fn file() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../eukhe-dashboard/ui/src/tokens.stylex.ts")
    }

    /// `source` with each generated block's lines (between its marker
    /// lines) replaced by the core's.
    fn generated(source: &str) -> String {
        let mut lines: Vec<String> = source.lines().map(str::to_owned).collect();
        for block in blocks() {
            let start = lines
                .iter()
                .position(|line| line.starts_with(&format!("  // block {}: ", block.name)))
                .unwrap_or_else(|| panic!("tokens.stylex.ts has no block {}", block.name));
            let end = lines[start..]
                .iter()
                .position(|line| *line == format!("  // end of block {}", block.name))
                .unwrap_or_else(|| panic!("block {} of tokens.stylex.ts has no end", block.name))
                + start;
            lines.splice(start + 1..end, block.lines);
        }
        let mut text = lines.join("\n");
        text.push('\n');
        text
    }

    /// The token values of the web app are the compiled core's tables,
    /// line for line.
    #[test]
    fn the_dashboard_token_file_holds_the_cores_tables() {
        let source = std::fs::read_to_string(file()).expect("tokens.stylex.ts");
        assert!(
            generated(&source) == source,
            "tokens.stylex.ts differs from bend/tokens.bend: run `make dashboard-tokens`"
        );
    }

    #[test]
    #[ignore = "writes the generated blocks of tokens.stylex.ts (`make dashboard-tokens`)"]
    fn regenerate_dashboard_tokens() {
        let source = std::fs::read_to_string(file()).expect("tokens.stylex.ts");
        std::fs::write(file(), generated(&source)).expect("write tokens.stylex.ts");
    }
}
