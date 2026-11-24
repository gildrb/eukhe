//! The cross-platform role vocabulary (port of the role tables of omp
//! `crates/natives/src/desktop/ax.rs`).

use std::borrow::Cow;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// An element's role, normalized across platforms. `Other` keeps a role the
/// vocabulary does not name, lowercased, as the platform spelled it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Role {
    Window,
    WebArea,
    Group,
    List,
    ListItem,
    Table,
    Row,
    Cell,
    Outline,
    OutlineItem,
    Menu,
    MenuBar,
    MenuBarItem,
    MenuItem,
    MenuButton,
    PopUpButton,
    TabGroup,
    Tab,
    Toolbar,
    ScrollArea,
    Button,
    CheckBox,
    Radio,
    TextField,
    TextArea,
    StaticText,
    Link,
    Slider,
    ComboBox,
    Image,
    DisclosureTriangle,
    DateTimeArea,
    DateField,
    TimeField,
    Other(String),
}

/// Printed names, as `ax` lines show them and `find` matches them.
const NAMED: &[(&str, Role)] = &[
    ("window", Role::Window),
    ("webarea", Role::WebArea),
    ("group", Role::Group),
    ("list", Role::List),
    ("listitem", Role::ListItem),
    ("table", Role::Table),
    ("row", Role::Row),
    ("cell", Role::Cell),
    ("outline", Role::Outline),
    ("outlineitem", Role::OutlineItem),
    ("menu", Role::Menu),
    ("menubar", Role::MenuBar),
    ("menubaritem", Role::MenuBarItem),
    ("menuitem", Role::MenuItem),
    ("menubutton", Role::MenuButton),
    ("popupbutton", Role::PopUpButton),
    ("tabgroup", Role::TabGroup),
    ("tab", Role::Tab),
    ("toolbar", Role::Toolbar),
    ("scrollarea", Role::ScrollArea),
    ("button", Role::Button),
    ("checkbox", Role::CheckBox),
    ("radio", Role::Radio),
    ("textfield", Role::TextField),
    ("textarea", Role::TextArea),
    ("statictext", Role::StaticText),
    ("link", Role::Link),
    ("slider", Role::Slider),
    ("combobox", Role::ComboBox),
    ("image", Role::Image),
    ("disclosuretriangle", Role::DisclosureTriangle),
    ("datetimearea", Role::DateTimeArea),
    ("datefield", Role::DateField),
    ("timefield", Role::TimeField),
];

impl Role {
    /// The role a printed or platform name stands for, ignoring ASCII case.
    #[must_use]
    pub fn from_name(name: &str) -> Self {
        NAMED
            .iter()
            .find(|(printed, _)| printed.eq_ignore_ascii_case(name))
            .map_or_else(
                || Self::Other(name.to_ascii_lowercase()),
                |(_, role)| role.clone(),
            )
    }

    /// The printed name.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::Other(name) => name,
            known => NAMED
                .iter()
                .find(|(_, role)| role == known)
                .map_or("", |(printed, _)| printed),
        }
    }

    /// A macOS `AX*` role.
    #[must_use]
    pub fn from_macos(native: &str) -> Self {
        Self::from_name(native.strip_prefix("AX").unwrap_or(native))
    }

    /// An AT-SPI role name; `lines` tells a text area from a field.
    #[must_use]
    pub fn from_atspi(native: &str, lines: TextLines) -> Self {
        const ALIASES: &[(&str, Role)] = &[
            ("push button", Role::Button),
            ("toggle button", Role::Button),
            ("label", Role::StaticText),
            ("page tab", Role::Tab),
            ("page tab list", Role::TabGroup),
            ("table cell", Role::Cell),
            ("tree", Role::Outline),
            ("tree item", Role::OutlineItem),
            ("frame", Role::Window),
            ("dialog", Role::Window),
        ];
        if native.eq_ignore_ascii_case("entry") || native.eq_ignore_ascii_case("text") {
            return match lines {
                TextLines::Single => Self::TextField,
                TextLines::Multi => Self::TextArea,
            };
        }
        ALIASES
            .iter()
            .find(|(alias, _)| alias.eq_ignore_ascii_case(native))
            .map_or_else(
                || Self::from_name(&native.replace(' ', "")),
                |(_, role)| role.clone(),
            )
    }

    /// Controls whose own action is a press.
    pub(crate) fn pressable(&self) -> bool {
        matches!(
            self,
            Self::Button
                | Self::CheckBox
                | Self::Radio
                | Self::Link
                | Self::MenuItem
                | Self::MenuBarItem
                | Self::MenuButton
                | Self::PopUpButton
                | Self::Tab
                | Self::DisclosureTriangle
        )
    }

    /// Roles a line keeps even without a name or action.
    pub(crate) fn interactable(&self) -> bool {
        matches!(
            self,
            Self::Button
                | Self::CheckBox
                | Self::Radio
                | Self::TextField
                | Self::TextArea
                | Self::Link
                | Self::MenuItem
                | Self::Tab
                | Self::Slider
                | Self::ComboBox
                | Self::PopUpButton
                | Self::ListItem
                | Self::OutlineItem
                | Self::Cell
        )
    }

    /// Containers that keep their own line around a single survivor: the
    /// role tells where the child sits.
    pub(crate) fn structural(&self) -> bool {
        matches!(
            self,
            Self::Window
                | Self::WebArea
                | Self::List
                | Self::Table
                | Self::Row
                | Self::Menu
                | Self::MenuBar
                | Self::TabGroup
                | Self::Toolbar
                | Self::ScrollArea
                | Self::Outline
        )
    }

    /// Text inputs whose confirm and cancel actions go unlisted.
    pub(crate) fn text_input(&self) -> bool {
        matches!(self, Self::TextField | Self::TextArea | Self::ComboBox)
    }
}

/// Whether an AT-SPI text element holds one line or many.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TextLines {
    Single,
    Multi,
}

impl fmt::Display for Role {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl Serialize for Role {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.name())
    }
}

impl<'de> Deserialize<'de> for Role {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Cow::<'de, str>::deserialize(deserializer).map(|name| Self::from_name(&name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn platform_roles_map_onto_the_vocabulary() {
        assert_eq!(Role::from_macos("AXPopUpButton"), Role::PopUpButton);
        assert_eq!(
            Role::from_macos("AXSplitGroup"),
            Role::Other("splitgroup".to_owned())
        );
        assert_eq!(
            Role::from_atspi("push button", TextLines::Single),
            Role::Button
        );
        assert_eq!(Role::from_atspi("text", TextLines::Multi), Role::TextArea);
        assert_eq!(
            Role::from_atspi("tree item", TextLines::Single),
            Role::OutlineItem
        );
        assert_eq!(
            Role::from_atspi("scroll pane", TextLines::Single),
            Role::Other("scrollpane".to_owned())
        );
        assert_eq!(Role::from_name("radio").to_string(), "radio");
    }
}
