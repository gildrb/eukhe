use super::*;
use crate::command_paths::PathMenu;

/// `command_rows` skips the menu call where `menu_lists_none` holds: the
/// menu lists no children there, for every path of the table.
#[test]
fn the_skipped_menu_lists_no_children() {
    let provider = CombinedAutocompleteProvider::from_registry(std::path::PathBuf::from("/tmp"));
    let table = &provider.table;
    let tails = [
        " ",
        " x",
        " s",
        " m",
        " a",
        " x y",
        " x ",
        "  x  y",
        " on off",
        " set cost=2 t",
        " 7 --until a",
        " ran a b",
        " model x",
    ];
    let mut skipped = 0;
    for place in 0.. {
        let Some(row) = table.row(place) else {
            break;
        };
        for tail in tails {
            let line = format!("{}{tail}", row.path.join(" "));
            let Some((path, text)) = provider.argument_text(&line) else {
                continue;
            };
            if provider.menu_lists_none(&path, text) {
                skipped += 1;
                let menu = table.menu(&line);
                assert!(
                    !matches!(&menu, PathMenu::Kids { rows, .. } if !rows.is_empty()),
                    "the menu of {line:?} lists children: {menu:?}"
                );
            }
        }
    }
    assert!(skipped > 100, "only {skipped} lines skip the menu");
}
