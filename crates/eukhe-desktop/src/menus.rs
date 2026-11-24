//! Menu-bar paths and label matching (port of omp
//! `crates/natives/src/desktop/menus.rs`).

use std::fmt;

use serde::{Deserialize, Serialize};

use crate::ax::Availability;

/// Whether a menu item shows a check mark.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Check {
    Checked,
    Unchecked,
}

/// Whether a menu item opens a submenu.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Submenu {
    Leaf,
    Opens,
}

/// One item of a native application menu. `path` holds the native labels,
/// ellipses included.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MenuItem {
    pub title: String,
    pub path: Vec<String>,
    pub availability: Availability,
    pub check: Check,
    pub submenu: Submenu,
    pub shortcut: Option<String>,
}

/// Most labels a path holds.
const MAX_DEPTH: usize = 32;

/// A menu-bar path of 1 to 32 non-blank labels without NUL, such as
/// `["File", "Export…"]`. Labels match ignoring case and a trailing
/// ellipsis.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "Vec<String>", into = "Vec<String>")]
pub struct MenuPath(Vec<String>);

impl MenuPath {
    #[must_use]
    pub fn labels(&self) -> &[String] {
        &self.0
    }
}

impl TryFrom<Vec<String>> for MenuPath {
    type Error = MenuError;

    fn try_from(labels: Vec<String>) -> Result<Self, MenuError> {
        if labels.is_empty() || labels.len() > MAX_DEPTH {
            return Err(MenuError::PathLength);
        }
        if labels
            .iter()
            .any(|label| label.trim().is_empty() || label.contains('\0'))
        {
            return Err(MenuError::BlankLabel);
        }
        Ok(Self(labels))
    }
}

impl From<MenuPath> for Vec<String> {
    fn from(path: MenuPath) -> Self {
        path.0
    }
}

/// The label without surrounding blanks or a trailing `...` or `…`.
fn normalized(label: &str) -> &str {
    let label = label.trim();
    label
        .strip_suffix("...")
        .or_else(|| label.strip_suffix('…'))
        .unwrap_or(label)
        .trim_end()
}

/// Most labels a miss names, and most characters of each.
const MAX_OFFERED_LABELS: usize = 40;
const MAX_OFFERED_CHARS: usize = 80;

/// The one item of `items` labelled `label`: an exact case-insensitive
/// label first, then one equal once ellipses are dropped. Each tier needs
/// exactly one match; order and enabled state never break ties.
pub(crate) fn match_label(items: &[MenuItem], label: &str) -> Result<usize, MenuError> {
    let folded = label.trim().to_lowercase();
    let mut exact = items
        .iter()
        .enumerate()
        .filter(|(_, item)| item.title.trim().to_lowercase() == folded);
    if let Some((index, _)) = exact.next() {
        return match exact.next() {
            None => Ok(index),
            Some(_) => Err(MenuError::Ambiguous {
                label: label.to_owned(),
                tier: Tier::Exact,
            }),
        };
    }
    let folded = normalized(label).to_lowercase();
    let mut loose = items
        .iter()
        .enumerate()
        .filter(|(_, item)| normalized(&item.title).to_lowercase() == folded);
    match (loose.next(), loose.next()) {
        (Some((index, _)), None) => Ok(index),
        (None, _) => Err(MenuError::NotFound {
            label: label.to_owned(),
            offered: offered(items),
        }),
        (Some(_), Some(_)) => Err(MenuError::Ambiguous {
            label: label.to_owned(),
            tier: Tier::Normalized,
        }),
    }
}

fn offered(items: &[MenuItem]) -> Offered {
    let named: Vec<_> = items
        .iter()
        .filter(|item| !item.title.trim().is_empty())
        .collect();
    Offered {
        items: named
            .iter()
            .take(MAX_OFFERED_LABELS)
            .map(|item| OfferedItem {
                title: item.title.trim().chars().take(MAX_OFFERED_CHARS).collect(),
                availability: item.availability,
                submenu: item.submenu,
            })
            .collect(),
        more: named.len().saturating_sub(MAX_OFFERED_LABELS),
    }
}

/// Refuses an item that is no command a press can run.
pub(crate) fn require_command(item: &MenuItem) -> Result<(), MenuError> {
    match (item.availability, item.submenu) {
        (Availability::Disabled, _) => Err(MenuError::Disabled {
            path: item.path.clone(),
        }),
        (Availability::Enabled, Submenu::Opens) => Err(MenuError::NotACommand),
        (Availability::Enabled, Submenu::Leaf) if item.title.trim().is_empty() => {
            Err(MenuError::NotACommand)
        }
        (Availability::Enabled, Submenu::Leaf) => Ok(()),
    }
}

/// Which matching tier found several items.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Tier {
    Exact,
    Normalized,
}

/// The labels a menu level offers, as a miss names them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Offered {
    pub items: Vec<OfferedItem>,
    /// Labels left out.
    pub more: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OfferedItem {
    pub title: String,
    pub availability: Availability,
    pub submenu: Submenu,
}

impl fmt::Display for Offered {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, item) in self.items.iter().enumerate() {
            if index > 0 {
                f.write_str(", ")?;
            }
            crate::ax::tree::write_quoted_label(f, &item.title)?;
            match item.availability {
                Availability::Enabled => {}
                Availability::Disabled => f.write_str(" (disabled)")?,
            }
            match item.submenu {
                Submenu::Leaf => {}
                Submenu::Opens => f.write_str(" ▸")?,
            }
        }
        if self.more > 0 {
            write!(f, " and {} more", self.more)?;
        }
        Ok(())
    }
}

/// Why a menu path names no command.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum MenuError {
    #[error("a menu path holds 1 to 32 labels; nothing was sent")]
    PathLength,
    #[error("a menu path label is blank or holds NUL; nothing was sent")]
    BlankLabel,
    #[error("menu item {label:?} was not found; this menu has {offered}; nothing was sent")]
    NotFound { label: String, offered: Offered },
    #[error("menu label {label:?} matches several items ({tier:?} match); nothing was sent")]
    Ambiguous { label: String, tier: Tier },
    #[error("menu item {} is disabled; nothing was sent", .path.join(" > "))]
    Disabled { path: Vec<String> },
    #[error("select a named leaf menu command, not a submenu or separator; nothing was sent")]
    NotACommand,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn item(title: &str) -> MenuItem {
        MenuItem {
            title: title.to_owned(),
            path: vec![title.to_owned()],
            availability: Availability::Enabled,
            check: Check::Unchecked,
            submenu: Submenu::Leaf,
            shortcut: None,
        }
    }

    #[test]
    fn exact_labels_win_before_ellipsis_normalization() {
        assert_eq!(match_label(&[item("Open…"), item("Open")], "OPEN"), Ok(1));
        assert_eq!(match_label(&[item("Open…")], "open..."), Ok(0));
        assert_eq!(
            match_label(&[item("Save…"), item("Save...")], "save"),
            Err(MenuError::Ambiguous {
                label: "save".to_owned(),
                tier: Tier::Normalized
            })
        );
    }

    #[test]
    fn a_miss_names_the_labels_on_offer() {
        let mut save = item("Save");
        save.availability = Availability::Disabled;
        let mut recent = item("Open Recent");
        recent.submenu = Submenu::Opens;
        let error = match_label(&[item("New"), item(""), save, recent], "Nope")
            .map_err(|error| error.to_string());
        assert_eq!(
            error,
            Err(
                "menu item \"Nope\" was not found; this menu has \"New\", \"Save\" (disabled), \
                 \"Open Recent\" ▸; nothing was sent"
                    .to_owned()
            )
        );
    }

    #[test]
    fn paths_are_checked_at_the_edge() {
        assert_eq!(MenuPath::try_from(Vec::new()), Err(MenuError::PathLength));
        assert_eq!(
            MenuPath::try_from(vec!["File".to_owned(), " ".to_owned()]),
            Err(MenuError::BlankLabel)
        );
        assert!(serde_json::from_str::<MenuPath>("[\"File\",\"Export…\"]").is_ok());
    }
}
