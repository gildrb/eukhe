//! Units of an agent tree's scopes: a unit is a path prefix relative to
//! the workspace root (`""` is the whole workspace). A file belongs to the
//! unit of its longest component-wise prefix; the core's scopes and
//! patches are masks over the units, in order.

use std::path::{Path, PathBuf};

use eukhe_bend::rules::agent_tree::Patch;

/// The version a changed unit carries in a child's patch.
const CHANGED: u64 = 1;

/// The index of the unit `path` belongs to: its longest component-wise
/// prefix among `units`; `None` when no unit holds it.
#[must_use]
pub fn unit_of(units: &[String], path: &Path) -> Option<usize> {
    units
        .iter()
        .enumerate()
        .filter(|(_, unit)| path.starts_with(unit.as_str()))
        .max_by_key(|(_, unit)| Path::new(unit.as_str()).components().count())
        .map(|(index, _)| index)
}

/// The patch of a child that changed `changed`: per unit, `Some(1)` when
/// the child added, modified or removed a file in it, else `None`.
#[must_use]
pub fn unit_patch(units: &[String], changed: &[PathBuf]) -> Patch {
    let mut patch = vec![None; units.len()];
    for unit in changed.iter().filter_map(|path| unit_of(units, path)) {
        patch[unit] = Some(CHANGED);
    }
    patch
}
