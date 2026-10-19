use eukhe_tui::width::str_width;

use super::{render, StyledText};
use crate::testing::{compare, Rng, Scenario};

/// A wide (CJK) cell pads to its display width, not its character count:
/// `漢字` is 2 characters but 4 columns wide.
#[test]
fn a_cjk_row_aligns_by_display_width() {
    let text = "a    | b\n-----|--\n漢字 | x\nabcd | y".to_string();
    let units = text.encode_utf16().count();
    assert_eq!(
        render("| a | b |\n|---|---|\n| 漢字 | x |\n| abcd | y |"),
        vec![StyledText {
            text,
            styles: vec![format!("0:{units}:MONOSPACE")],
        }]
    );
}

/// The glyphs of the generated cells: ASCII, CJK, emoji (one with a
/// zero-width joiner), and a letter with a combining mark.
const GLYPHS: [&str; 6] = ["a", "Z", "漢", "😀", "👨\u{200d}👩\u{200d}👧", "e\u{301}"];

/// A table of random rows (ragged, with empty cells), the scenario of
/// the model (each cell as the display widths of its glyphs) and what the
/// Rust formatter printed (the display width of each column of each row).
fn table(rng: &mut Rng, at: usize) -> Scenario {
    let columns = rng.range(1, 4);
    // Text before and after the table: the chunk's trim never reaches
    // the table, even when its first or last cell is empty.
    let mut markdown = "start\n".to_string();
    let mut events = String::new();
    let rows = rng.range(1, 5);
    for row in 0..=rows {
        let cells = if row == 0 {
            columns
        } else {
            rng.range(1, columns)
        };
        markdown.push('|');
        events.push('r');
        for _ in 0..cells {
            markdown.push(' ');
            events.push('\t');
            for _ in 0..rng.below(4) {
                let glyph = GLYPHS[usize::try_from(rng.below(GLYPHS.len() as u64)).unwrap()];
                markdown.push_str(glyph);
                events.push_str(&str_width(glyph).to_string());
            }
            markdown.push_str(" |");
        }
        markdown.push('\n');
        events.push('\n');
        if row == 0 {
            markdown.push_str(&"|---".repeat(usize::try_from(columns).unwrap()));
            markdown.push_str("|\n");
        }
    }
    markdown.push_str("\nend");
    let rendered: String = render(&markdown)
        .into_iter()
        .map(|chunk| chunk.text)
        .collect();
    let mut transcript = String::new();
    for (line, text) in rendered
        .lines()
        .skip(1)
        .take(usize::try_from(rows).unwrap() + 2)
        .enumerate()
    {
        if line == 1 {
            continue;
        }
        let widths: Vec<String> = text
            .split(" | ")
            .map(|column| str_width(column).to_string())
            .collect();
        transcript.push_str(&widths.join(" "));
        transcript.push('\n');
    }
    Scenario {
        name: format!("table {at}"),
        events,
        transcript,
    }
}

#[test]
fn the_rust_table_equals_the_bend_model() {
    let mut rng = Rng(0x6a7e_3a1d_71d7_4b5e);
    let scenarios: Vec<Scenario> = (0..200).map(|at| table(&mut rng, at)).collect();
    compare("bend/bridge_gateway_width.bend", scenarios);
}
