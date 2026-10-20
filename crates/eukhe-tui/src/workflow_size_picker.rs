//! The `/workflow-size` inline picker: the dynamic workflow sizes
//! (`small`, `medium`, `large`) over the inline-picker component, the
//! `/effort` picker's seam. Enter applies the picked size through the
//! caller (the `workflow.size` setting); Esc cancels.

use eukhe_types::workflow::WorkflowSize;

use crate::config_selector::{ConfigSelector, SelectorAction, SelectorKind, SelectorRow};
use crate::keybindings::KeybindingsManager;
use crate::theme::Theme;
use crate::Line;

/// The row description of a size: its limits.
#[must_use]
pub fn size_description(size: WorkflowSize) -> String {
    let limits = size.limits();
    format!(
        "{} agents at once, {} in total",
        limits.concurrency, limits.max_agents
    )
}

/// One key press while the picker is open.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkflowSizePickerAction {
    /// Enter or Space on a size: the caller applies it.
    Apply(WorkflowSize),
    /// Esc or Ctrl+C: close without applying.
    Cancel,
    /// Navigation or filter editing only.
    None,
}

/// The outcome of `/workflow-size [size]`.
#[derive(Debug)]
pub(crate) enum WorkflowSizeCommand {
    /// No argument: open the picker.
    Open(WorkflowSizePicker),
    /// A known size: apply it directly.
    Apply(WorkflowSize),
    /// Not a size: the usage error.
    Unknown(String),
}

/// Dispatch `/workflow-size [size]`; `current` is the setting's value.
pub(crate) fn workflow_size_command(
    arg: &str,
    current: Option<WorkflowSize>,
) -> WorkflowSizeCommand {
    let requested = arg.trim().to_lowercase();
    if requested.is_empty() {
        return WorkflowSizeCommand::Open(WorkflowSizePicker::new(current));
    }
    match WorkflowSize::parse(&requested) {
        Some(size) => WorkflowSizeCommand::Apply(size),
        None => WorkflowSizeCommand::Unknown(requested),
    }
}

/// The picker over the three sizes, the current one checked.
#[derive(Debug)]
pub struct WorkflowSizePicker {
    selector: ConfigSelector,
}

impl WorkflowSizePicker {
    /// Build the picker with `current` checked.
    #[must_use]
    pub fn new(current: Option<WorkflowSize>) -> Self {
        let rows = WorkflowSize::ALL
            .iter()
            .map(|size| SelectorRow::Item {
                key: size.as_str().to_owned(),
                label: size.as_str().to_owned(),
                checked: current == Some(*size),
                type_label: size_description(*size),
                path: String::new(),
            })
            .collect();
        Self {
            selector: ConfigSelector::with_kind(rows, SelectorKind::WorkflowSize),
        }
    }

    /// One bracketed paste into the search.
    pub fn paste(&mut self, text: &str) {
        self.selector.paste(text);
    }

    /// The checked state of one size's row.
    #[must_use]
    pub fn checked(&self, size: WorkflowSize) -> Option<bool> {
        self.selector.checked(size.as_str())
    }

    /// One key id: cancel keys close; Enter/Space apply the selected size.
    pub fn handle_key(&mut self, key: &str, kb: &KeybindingsManager) -> WorkflowSizePickerAction {
        if key == "ctrl+c" {
            return WorkflowSizePickerAction::Cancel;
        }
        match self.selector.handle_key(key, kb) {
            Some(SelectorAction::Close | SelectorAction::Exit) => WorkflowSizePickerAction::Cancel,
            Some(SelectorAction::Toggle { key, .. }) => WorkflowSize::parse(&key).map_or(
                WorkflowSizePickerAction::None,
                WorkflowSizePickerAction::Apply,
            ),
            None => WorkflowSizePickerAction::None,
        }
    }

    /// The picker's rendered frame.
    #[must_use]
    pub fn render(&self, theme: &Theme, width: usize, kb: &KeybindingsManager) -> Vec<Line> {
        self.selector.render(theme, width, kb)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theme::{ColorMode, Theme};

    fn kb() -> KeybindingsManager {
        KeybindingsManager::new()
    }

    #[test]
    fn no_argument_opens_the_picker_with_the_current_size_checked() {
        let WorkflowSizeCommand::Open(picker) =
            workflow_size_command("", Some(WorkflowSize::Large))
        else {
            panic!("expected the picker to open")
        };
        assert_eq!(
            (
                picker.checked(WorkflowSize::Large),
                picker.checked(WorkflowSize::Small)
            ),
            (Some(true), Some(false))
        );
    }

    #[test]
    fn a_size_applies_and_anything_else_is_unknown() {
        assert!(matches!(
            workflow_size_command(" SMALL ", None),
            WorkflowSizeCommand::Apply(WorkflowSize::Small)
        ));
        assert!(matches!(
            workflow_size_command("huge", None),
            WorkflowSizeCommand::Unknown(requested) if requested == "huge"
        ));
    }

    #[test]
    fn enter_applies_the_selected_size_and_escape_cancels() {
        let mut picker = WorkflowSizePicker::new(None);
        assert_eq!(
            picker.handle_key("down", &kb()),
            WorkflowSizePickerAction::None
        );
        assert_eq!(
            picker.handle_key("enter", &kb()),
            WorkflowSizePickerAction::Apply(WorkflowSize::Medium)
        );
        assert_eq!(
            picker.handle_key("escape", &kb()),
            WorkflowSizePickerAction::Cancel
        );
    }

    #[test]
    fn the_frame_lists_the_sizes_and_their_limits() {
        let picker = WorkflowSizePicker::new(None);
        let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
        let text: Vec<String> = picker
            .render(&theme, 70, &kb())
            .iter()
            .map(|line| line.iter().map(|span| span.content.as_str()).collect())
            .collect();
        assert!(
            text.iter().any(|row| row.contains("Workflow Size")),
            "{text:?}"
        );
        assert!(
            text.iter()
                .any(|row| row.contains("12 agents at once, 25 in total")),
            "{text:?}"
        );
    }
}
