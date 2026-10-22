use super::{render, StyledText};

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
