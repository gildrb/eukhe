//! The row cells: the name column clip/pad.

use super::*;

/// The exact expected idle-row text: name cell (icon + title, clipped or
/// padded to `name_width`), the model cell padded to its column, then
/// the cost/age details.
fn expected_row(title_cell: &str, layout: &RowLayout) -> String {
    let bullet = crate::glyphs::BULLET;
    format!(
        "{bullet} {title_cell}  {}  $0.00   1s",
        cell("mock-1", layout.model_width),
    )
}

#[test]
fn long_session_names_clip_to_the_name_column() {
    let (mode, index) = mode_with_row(&"a".repeat(100), "mock-1");
    let layout = build_layout(&mode.rows, 120);
    // TS `buildCompactAgentsViewLayout` at width 120 with these rows.
    assert_eq!(layout.name_width, 28);
    assert_eq!(layout.model_width, 12);
    let line = mode.render_row(&mode.rows[index], &layout, 120);
    let text = flat(&line);
    // TS `formatTableCell` clips with an empty ellipsis marker: the
    // name cell keeps the icon and space plus 26 name characters.
    assert_eq!(text, expected_row(&"a".repeat(26), &layout));
    // Every column still renders after the clipped name.
    let model_at = text.find("mock-1").expect("model column present");
    assert_eq!(str_width(&text[..model_at]), 28 + 2);
    assert!(text.ends_with("$0.00   1s"));
}

#[test]
fn short_session_names_pad_to_the_name_column() {
    let (mode, index) = mode_with_row("short name", "mock-1");
    let layout = build_layout(&mode.rows, 120);
    assert_eq!(layout.name_width, 28);
    let line = mode.render_row(&mode.rows[index], &layout, 120);
    let text = flat(&line);
    let name_cell = format!("short name{}", " ".repeat(28 - 2 - 10));
    assert_eq!(text, expected_row(&name_cell, &layout));
}
