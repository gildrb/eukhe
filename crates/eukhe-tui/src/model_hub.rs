//! The `/model` hub: every model role ([`ModelRole::ALL`]) with the model
//! it runs on and where that value comes from. Enter on a role opens the
//! models the role accepts (the [`ModelPicker`] for a chat-group role, the
//! local choice list for a local role); Enter there assigns; Backspace or
//! `x` (with an empty search) clears the role; Esc goes back, then closes;
//! typing searches. The session reads and writes the settings; this
//! module owns the lists and the keys.

use eukhe_types::model_roles::ModelRole;

use crate::client_settings::{LocalRoleChoices, ModelRoleSource, ModelRoleValue};
use crate::keybindings::KeybindingsManager;
use crate::menu_panel::{
    hint_row, key_hint, menu_list_layout, menu_row, no_match_row, scroll_row, search_field_lines,
    MenuSegment,
};
use crate::model_picker::{ModelPicker, ModelPickerAction, ModelSelectionApplied};
use crate::search_input::SearchInput;
use crate::theme::{Theme, ThemeColor};
use crate::Line;

/// The provider part of a local catalog model's selector (`local/<id>`).
pub const LOCAL_PROVIDER: &str = "local";

/// One role row: the model the role runs on and its source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleRow {
    pub role: ModelRole,
    /// The set selector (with the thinking level a role keeps), or the
    /// fallback that runs while it is unset.
    pub value: String,
    /// `session`, `global`, `project`, or `default` (unset).
    pub source: &'static str,
    /// Whether `value` is set (not the fallback).
    pub set: bool,
}

impl RoleRow {
    /// The row of a role read from the settings.
    #[must_use]
    pub fn from_value(role: ModelRole, value: &ModelRoleValue) -> Self {
        let source = match value.source {
            ModelRoleSource::Unset => "default",
            ModelRoleSource::Global => "global",
            ModelRoleSource::Project => "project",
        };
        match &value.selector {
            Some(selector) => RoleRow {
                role,
                value: match value.thinking {
                    Some(level) => format!("{selector} ({})", level.wire_name()),
                    None => selector.clone(),
                },
                source,
                set: true,
            },
            None => RoleRow {
                role,
                value: format!("auto: {}", value.fallback),
                source,
                set: false,
            },
        }
    }

    /// The `chat` row: the live session's model.
    #[must_use]
    pub fn chat(model: Option<String>) -> Self {
        RoleRow {
            role: ModelRole::Chat,
            set: model.is_some(),
            value: model.unwrap_or_else(|| "no model".to_owned()),
            source: "session",
        }
    }
}

/// One entry of a local role's choice list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChoiceItem {
    pub provider: String,
    pub model_id: String,
    /// The muted trailing text (the title and install state, or the
    /// provider).
    pub detail: String,
}

impl ChoiceItem {
    fn selector(&self) -> String {
        format!("{}/{}", self.provider, self.model_id)
    }
}

/// The choice items of a local role: its catalog models, then (for a
/// text role) the provider models `remote` lists as `(provider, id)`.
#[must_use]
pub fn local_choice_items(
    choices: &LocalRoleChoices,
    remote: &[(String, String)],
) -> Vec<ChoiceItem> {
    let local = choices.models.iter().map(|model| ChoiceItem {
        provider: LOCAL_PROVIDER.to_owned(),
        model_id: model.id.clone(),
        detail: if model.installed {
            model.title.clone()
        } else {
            format!("{} (not installed)", model.title)
        },
    });
    let remote = remote
        .iter()
        .filter(|_| choices.takes_remote)
        .map(|(provider, model_id)| ChoiceItem {
            provider: provider.clone(),
            model_id: model_id.clone(),
            detail: provider.clone(),
        });
    local.chain(remote).collect()
}

/// A searchable list: the roles, or a local role's choices.
#[derive(Debug)]
struct List {
    search: SearchInput,
    /// Positions of the matching entries, in list order.
    filtered: Vec<usize>,
    selected: usize,
}

impl List {
    fn new(len: usize) -> Self {
        List {
            search: SearchInput::new(),
            filtered: (0..len).collect(),
            selected: 0,
        }
    }

    fn refilter(&mut self, texts: &[String]) {
        let all: Vec<usize> = (0..texts.len()).collect();
        self.filtered = if self.search.value().trim().is_empty() {
            all
        } else {
            crate::fuzzy::fuzzy_filter(&all, self.search.value(), |at| texts[*at].clone())
        };
        self.selected = self.selected.min(self.filtered.len().saturating_sub(1));
    }

    fn current(&self) -> Option<usize> {
        self.filtered.get(self.selected).copied()
    }

    fn select(&mut self, at: usize) {
        if let Some(position) = self.filtered.iter().position(|&entry| entry == at) {
            self.selected = position;
        }
    }

    /// Up/Down/Page keys: whether the key moved the selection.
    fn navigate(&mut self, key: &str, kb: &KeybindingsManager, page: usize) -> bool {
        let count = self.filtered.len();
        let page = isize::try_from(page).unwrap_or(isize::MAX);
        let step: isize = if kb.matches(key, "tui.select.up") {
            -1
        } else if kb.matches(key, "tui.select.down") {
            1
        } else if kb.matches(key, "tui.select.pageUp") {
            -page
        } else if kb.matches(key, "tui.select.pageDown") {
            page
        } else {
            return false;
        };
        if count == 0 {
            return true;
        }
        let last = count - 1;
        self.selected = match step {
            -1 if self.selected == 0 => last,
            1 if self.selected == last => 0,
            _ => self.selected.saturating_add_signed(step).min(last),
        };
        true
    }

    /// The visible window `(start, end)` of the filtered list.
    fn window(&self, visible: usize) -> (usize, usize) {
        let visible = visible.max(1);
        let start = self
            .selected
            .saturating_sub(visible / 2)
            .min(self.filtered.len().saturating_sub(visible));
        (start, (start + visible).min(self.filtered.len()))
    }
}

/// The step the hub shows.
#[derive(Debug)]
enum Step {
    Roles,
    /// A chat-group role's model list.
    Models {
        role: ModelRole,
        picker: Box<ModelPicker>,
    },
    /// A local role's choice list.
    Choices {
        role: ModelRole,
        items: Vec<ChoiceItem>,
        list: List,
    },
}

/// One key press's outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelHubAction {
    /// Navigation or search only.
    None,
    /// Esc on the roles: close the hub.
    Close,
    /// Enter on a role: the caller opens its model step.
    Choose(ModelRole),
    /// Backspace or `x` on a role: the caller clears it.
    Clear(ModelRole),
    /// Enter on a model: the caller assigns it to the role.
    Assign {
        role: ModelRole,
        selection: ModelSelectionApplied,
    },
}

/// The hub.
#[derive(Debug)]
pub struct ModelHub {
    rows: Vec<RoleRow>,
    roles: List,
    step: Step,
    viewport_rows: usize,
}

impl ModelHub {
    /// The hub on its roles, the first selected.
    #[must_use]
    pub fn new(rows: Vec<RoleRow>, viewport_rows: usize) -> Self {
        ModelHub {
            roles: List::new(rows.len()),
            rows,
            step: Step::Roles,
            viewport_rows,
        }
    }

    /// The role rows, in hub order.
    #[must_use]
    pub fn rows(&self) -> &[RoleRow] {
        &self.rows
    }

    /// Replace the rows (after a write); the selection stays on its role.
    pub fn set_rows(&mut self, rows: Vec<RoleRow>) {
        let selected = self.selected_role();
        self.rows = rows;
        let texts = self.role_texts();
        self.roles.refilter(&texts);
        if let Some(role) = selected {
            self.select_role(role);
        }
    }

    /// Select `role`'s row.
    pub fn select_role(&mut self, role: ModelRole) {
        if let Some(at) = self.rows.iter().position(|row| row.role == role) {
            self.roles.select(at);
        }
    }

    /// The role the roles step has selected.
    #[must_use]
    pub fn selected_role(&self) -> Option<ModelRole> {
        self.roles.current().map(|at| self.rows[at].role)
    }

    /// The role whose model step is open.
    #[must_use]
    pub fn step_role(&self) -> Option<ModelRole> {
        match &self.step {
            Step::Roles => None,
            Step::Models { role, .. } | Step::Choices { role, .. } => Some(*role),
        }
    }

    /// The open model picker and its role (a catalog refresh lands in it).
    pub fn picker_mut(&mut self) -> Option<(ModelRole, &mut ModelPicker)> {
        match &mut self.step {
            Step::Models { role, picker } => Some((*role, picker.as_mut())),
            Step::Roles | Step::Choices { .. } => None,
        }
    }

    /// Open a chat-group role's model step.
    pub fn open_models(&mut self, role: ModelRole, picker: ModelPicker) {
        self.select_role(role);
        self.step = Step::Models {
            role,
            picker: Box::new(picker),
        };
    }

    /// Open a local role's choice step, `current` (a selector) selected.
    pub fn open_choices(&mut self, role: ModelRole, items: Vec<ChoiceItem>, current: Option<&str>) {
        self.select_role(role);
        let mut list = List::new(items.len());
        if let Some(at) =
            current.and_then(|current| items.iter().position(|item| item.selector() == current))
        {
            list.select(at);
        }
        self.step = Step::Choices { role, items, list };
    }

    /// Back to the roles.
    pub fn back_to_roles(&mut self) {
        self.step = Step::Roles;
    }

    /// Pasted text goes to the open step's search field.
    pub fn paste(&mut self, text: &str) {
        match &mut self.step {
            Step::Roles => {
                self.roles.search.paste(text);
                let texts = self.role_texts();
                self.roles.refilter(&texts);
            }
            Step::Models { picker, .. } => picker.paste(text),
            Step::Choices { items, list, .. } => {
                list.search.paste(text);
                list.refilter(&choice_texts(items));
            }
        }
    }

    /// One key id.
    pub fn handle_key(&mut self, key: &str, kb: &KeybindingsManager) -> ModelHubAction {
        let page = self.list_rows();
        match &mut self.step {
            Step::Roles => self.handle_roles_key(key, kb, page),
            Step::Models { role, picker } => match picker.handle_key(key, kb) {
                ModelPickerAction::None => ModelHubAction::None,
                ModelPickerAction::Cancel => {
                    self.step = Step::Roles;
                    ModelHubAction::None
                }
                ModelPickerAction::Apply(selection) => ModelHubAction::Assign {
                    role: *role,
                    selection: *selection,
                },
            },
            Step::Choices { role, items, list } => {
                if key == "ctrl+c" || kb.matches(key, "tui.select.cancel") {
                    self.step = Step::Roles;
                    return ModelHubAction::None;
                }
                if list.navigate(key, kb, page) {
                    return ModelHubAction::None;
                }
                if kb.matches(key, "tui.select.confirm") {
                    return match list.current() {
                        Some(at) => ModelHubAction::Assign {
                            role: *role,
                            selection: ModelSelectionApplied {
                                provider: items[at].provider.clone(),
                                model_id: items[at].model_id.clone(),
                                effort: None,
                            },
                        },
                        None => ModelHubAction::None,
                    };
                }
                let before = list.search.value().to_owned();
                list.search.handle_key(key, kb);
                if list.search.value() != before {
                    list.refilter(&choice_texts(items));
                }
                ModelHubAction::None
            }
        }
    }

    fn handle_roles_key(
        &mut self,
        key: &str,
        kb: &KeybindingsManager,
        page: usize,
    ) -> ModelHubAction {
        let searching = !self.roles.search.value().is_empty();
        if key == "ctrl+c" || kb.matches(key, "tui.select.cancel") {
            if !searching || key == "ctrl+c" {
                return ModelHubAction::Close;
            }
            self.roles = List::new(self.rows.len());
            return ModelHubAction::None;
        }
        if self.roles.navigate(key, kb, page) {
            return ModelHubAction::None;
        }
        if kb.matches(key, "tui.select.confirm") {
            return self
                .selected_role()
                .map_or(ModelHubAction::None, ModelHubAction::Choose);
        }
        if !searching && (key == "x" || kb.matches(key, "tui.editor.deleteCharBackward")) {
            return self
                .selected_role()
                .map_or(ModelHubAction::None, ModelHubAction::Clear);
        }
        let before = self.roles.search.value().to_owned();
        self.roles.search.handle_key(key, kb);
        if self.roles.search.value() != before {
            let texts = self.role_texts();
            self.roles.refilter(&texts);
        }
        ModelHubAction::None
    }

    fn role_texts(&self) -> Vec<String> {
        self.rows
            .iter()
            .map(|row| format!("{} {}", row.role.id(), row.role.label()))
            .collect()
    }

    /// The list rows the viewport leaves after the frame's fixed rows
    /// (title, search field, scroll row, hint, blank).
    fn list_rows(&self) -> usize {
        menu_list_layout(Some(self.viewport_rows), 12, self.rows.len(), 7, 1)
    }

    /// The hub's frame.
    pub fn render(&mut self, theme: &Theme, width: usize, kb: &KeybindingsManager) -> Vec<Line> {
        let visible = self.list_rows();
        match &mut self.step {
            Step::Models { role, picker } => {
                let mut lines = vec![title_row(theme, width, *role)];
                lines.extend(picker.render(theme, width, kb));
                lines
            }
            Step::Choices { role, items, list } => {
                let mut lines = vec![title_row(theme, width, *role)];
                lines.extend(search_field_lines(
                    theme,
                    width,
                    list.search.value(),
                    list.search.cursor(),
                    true,
                    "Search models",
                ));
                let (start, end) = list.window(visible);
                for position in start..end {
                    let item = &items[list.filtered[position]];
                    let primary = vec![theme.fg_span(ThemeColor::Text, item.selector())];
                    lines.push(menu_row(
                        theme,
                        width,
                        primary,
                        &[MenuSegment::muted(&item.detail)],
                        position == list.selected,
                    ));
                }
                if start > 0 || end < list.filtered.len() {
                    lines.push(scroll_row(
                        theme,
                        width,
                        list.selected + 1,
                        list.filtered.len(),
                    ));
                }
                if list.filtered.is_empty() {
                    lines.push(no_match_row(theme, width, "No matching models"));
                }
                let hint = [
                    key_hint(kb, &["tui.select.confirm"], "assign"),
                    key_hint(kb, &["tui.select.cancel"], "back"),
                ];
                lines.push(hint_row(theme, width, &join_hints(&hint)));
                lines.push(Vec::new());
                lines
            }
            Step::Roles => {
                let mut lines = vec![crate::width::truncate_line(
                    &vec![
                        crate::Span::raw(" "),
                        theme.fg_span(ThemeColor::Text, "Model roles"),
                    ],
                    width,
                    "",
                )];
                lines.extend(search_field_lines(
                    theme,
                    width,
                    self.roles.search.value(),
                    self.roles.search.cursor(),
                    true,
                    "Search roles",
                ));
                let (start, end) = self.roles.window(visible);
                for position in start..end {
                    let row = &self.rows[self.roles.filtered[position]];
                    let primary = vec![theme.fg_span(ThemeColor::Text, row.role.label())];
                    let value_color = if row.set {
                        ThemeColor::Accent
                    } else {
                        ThemeColor::Dim
                    };
                    let trailing = [
                        MenuSegment::muted(row.source),
                        MenuSegment::themed(value_color, &row.value),
                    ];
                    lines.push(menu_row(
                        theme,
                        width,
                        primary,
                        &trailing,
                        position == self.roles.selected,
                    ));
                }
                if start > 0 || end < self.roles.filtered.len() {
                    lines.push(scroll_row(
                        theme,
                        width,
                        self.roles.selected + 1,
                        self.roles.filtered.len(),
                    ));
                }
                if self.roles.filtered.is_empty() {
                    lines.push(no_match_row(theme, width, "No matching roles"));
                }
                let hint = [
                    key_hint(kb, &["tui.select.confirm"], "choose"),
                    Some("Backspace/x clear".to_owned()),
                    key_hint(kb, &["tui.select.cancel"], "close"),
                ];
                lines.push(hint_row(theme, width, &join_hints(&hint)));
                lines.push(Vec::new());
                lines
            }
        }
    }
}

fn choice_texts(items: &[ChoiceItem]) -> Vec<String> {
    items
        .iter()
        .map(|item| format!("{} {}", item.selector(), item.detail))
        .collect()
}

fn join_hints(hints: &[Option<String>]) -> String {
    hints
        .iter()
        .flatten()
        .cloned()
        .collect::<Vec<_>>()
        .join(crate::glyphs::SEP)
}

/// The model step's title: the role being assigned.
fn title_row(theme: &Theme, width: usize, role: ModelRole) -> Line {
    crate::width::truncate_line(
        &vec![
            crate::Span::raw(" "),
            theme.fg_span(ThemeColor::Text, format!("Model for {}", role.label())),
        ],
        width,
        crate::glyphs::ELLIPSIS,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::client_settings::LocalRoleModel;

    fn kb() -> KeybindingsManager {
        KeybindingsManager::new()
    }

    fn rows() -> Vec<RoleRow> {
        ModelRole::ALL
            .into_iter()
            .map(|role| RoleRow {
                role,
                value: format!("p/{}", role.id()),
                source: "global",
                set: true,
            })
            .collect()
    }

    #[test]
    fn the_roles_step_lists_every_role_with_its_value_and_source() {
        let mut hub = ModelHub::new(rows(), 30);
        let text: Vec<String> = hub
            .render(
                &Theme::builtin("eukhe", crate::theme::ColorMode::TrueColor),
                100,
                &kb(),
            )
            .iter()
            .map(|line| line.iter().map(|span| span.content.as_str()).collect())
            .collect();
        for role in ModelRole::ALL {
            assert!(
                text.iter().any(|line| line.contains(role.label())
                    && line.contains(&format!("p/{}", role.id()))
                    && line.contains("global")),
                "{} in {text:#?}",
                role.id()
            );
        }
    }

    #[test]
    fn enter_chooses_backspace_and_x_clear_esc_closes() {
        let mut hub = ModelHub::new(rows(), 30);
        assert_eq!(hub.handle_key("down", &kb()), ModelHubAction::None);
        assert_eq!(
            hub.handle_key("enter", &kb()),
            ModelHubAction::Choose(ModelRole::Memory)
        );
        assert_eq!(
            hub.handle_key("backspace", &kb()),
            ModelHubAction::Clear(ModelRole::Memory)
        );
        assert_eq!(
            hub.handle_key("x", &kb()),
            ModelHubAction::Clear(ModelRole::Memory)
        );
        assert_eq!(hub.handle_key("escape", &kb()), ModelHubAction::Close);
    }

    #[test]
    fn typing_searches_the_roles_and_esc_clears_the_search_first() {
        let mut hub = ModelHub::new(rows(), 30);
        for key in ["d", "i", "c"] {
            hub.handle_key(key, &kb());
        }
        assert_eq!(hub.selected_role(), Some(ModelRole::Dictation));
        // With a search typed, Backspace edits it instead of clearing.
        assert_eq!(hub.handle_key("backspace", &kb()), ModelHubAction::None);
        assert_eq!(hub.handle_key("escape", &kb()), ModelHubAction::None);
        assert_eq!(hub.selected_role(), Some(ModelRole::Chat));
        assert_eq!(hub.handle_key("escape", &kb()), ModelHubAction::Close);
    }

    #[test]
    fn a_local_choice_assigns_its_selector_and_esc_goes_back() {
        let choices = LocalRoleChoices {
            models: vec![LocalRoleModel {
                id: "lfm2.5-230m".to_owned(),
                title: "LFM2.5 230M".to_owned(),
                installed: false,
            }],
            takes_remote: true,
        };
        let items = local_choice_items(&choices, &[("prov".to_owned(), "m1".to_owned())]);
        assert_eq!(items[0].detail, "LFM2.5 230M (not installed)");
        let mut hub = ModelHub::new(rows(), 30);
        hub.open_choices(ModelRole::Titles, items, Some("prov/m1"));
        assert_eq!(hub.step_role(), Some(ModelRole::Titles));
        assert_eq!(
            hub.handle_key("enter", &kb()),
            ModelHubAction::Assign {
                role: ModelRole::Titles,
                selection: ModelSelectionApplied {
                    provider: "prov".to_owned(),
                    model_id: "m1".to_owned(),
                    effort: None,
                },
            }
        );
        assert_eq!(hub.handle_key("escape", &kb()), ModelHubAction::None);
        assert_eq!(hub.step_role(), None);
        assert_eq!(hub.selected_role(), Some(ModelRole::Titles));
    }

    #[test]
    fn a_speech_role_lists_only_its_local_models() {
        let choices = LocalRoleChoices {
            models: vec![LocalRoleModel {
                id: "kokoro".to_owned(),
                title: "Kokoro".to_owned(),
                installed: true,
            }],
            takes_remote: false,
        };
        let items = local_choice_items(&choices, &[("prov".to_owned(), "m1".to_owned())]);
        assert_eq!(
            items.iter().map(ChoiceItem::selector).collect::<Vec<_>>(),
            ["local/kokoro"]
        );
    }
}
