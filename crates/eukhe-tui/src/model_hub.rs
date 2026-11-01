//! The `/model` hub: every model role ([`ModelRole::ALL`]) with the model
//! it runs on and where that value comes from, then the all-roles model
//! (`modelRoles.all`, the model of every role without its own). Enter on a
//! row opens the models it accepts (the [`ModelPicker`] for a chat-group
//! role and the all-roles model, the local choice list for a local role);
//! Enter there assigns; Backspace or `x` (with an empty search) clears the
//! row; Esc goes back, then closes; typing searches. The session reads and
//! writes the settings; this module owns the lists and the keys.

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

/// What a hub row sets: one model role, or the all-roles model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HubTarget {
    Role(ModelRole),
    /// `modelRoles.all`: the model of every role without its own.
    AllRoles,
}

impl HubTarget {
    /// The row's label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            HubTarget::Role(role) => role.label(),
            HubTarget::AllRoles => "All roles",
        }
    }

    /// The word the row's search matches besides its label (a role's id).
    fn id(self) -> &'static str {
        match self {
            HubTarget::Role(role) => role.id(),
            HubTarget::AllRoles => "all",
        }
    }
}

/// One hub row: the model the target runs on and its source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleRow {
    pub target: HubTarget,
    /// The selector that applies (with the thinking level a role keeps),
    /// or the fallback that runs while nothing is set.
    pub value: String,
    /// `session`, `global`, `project`, `all roles` (the all-roles model),
    /// or `default` (unset).
    pub source: &'static str,
    /// Whether `value` is the target's own setting (not the all-roles
    /// model, not the fallback).
    pub set: bool,
}

impl RoleRow {
    /// The row of a target read from the settings.
    #[must_use]
    pub fn from_value(target: HubTarget, value: &ModelRoleValue) -> Self {
        let (source, own) = match value.source {
            ModelRoleSource::Unset => ("default", false),
            ModelRoleSource::Global => ("global", true),
            ModelRoleSource::Project => ("project", true),
            ModelRoleSource::AllRoles => ("all roles", false),
        };
        match &value.selector {
            Some(selector) => RoleRow {
                target,
                value: match value.thinking {
                    Some(level) => format!("{selector} ({})", level.wire_name()),
                    None => selector.clone(),
                },
                source,
                set: own,
            },
            None => RoleRow {
                target,
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
            target: HubTarget::Role(ModelRole::Chat),
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
    /// A chat-group role's or the all-roles model's model list.
    Models {
        target: HubTarget,
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
    /// Enter on a row: the caller opens its model step.
    Choose(HubTarget),
    /// Backspace or `x` on a row: the caller clears it.
    Clear(HubTarget),
    /// Enter on a model: the caller assigns it to the target.
    Assign {
        target: HubTarget,
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

    /// The rows, in hub order.
    #[must_use]
    pub fn rows(&self) -> &[RoleRow] {
        &self.rows
    }

    /// Replace the rows (after a write); the selection stays on its row.
    pub fn set_rows(&mut self, rows: Vec<RoleRow>) {
        let selected = self.selected_target();
        self.rows = rows;
        let texts = self.role_texts();
        self.roles.refilter(&texts);
        if let Some(target) = selected {
            self.select_target(target);
        }
    }

    /// Select `target`'s row.
    pub fn select_target(&mut self, target: HubTarget) {
        if let Some(at) = self.rows.iter().position(|row| row.target == target) {
            self.roles.select(at);
        }
    }

    /// The target the roles step has selected.
    #[must_use]
    pub fn selected_target(&self) -> Option<HubTarget> {
        self.roles.current().map(|at| self.rows[at].target)
    }

    /// The target whose model step is open.
    #[must_use]
    pub fn step_target(&self) -> Option<HubTarget> {
        match &self.step {
            Step::Roles => None,
            Step::Models { target, .. } => Some(*target),
            Step::Choices { role, .. } => Some(HubTarget::Role(*role)),
        }
    }

    /// The open model picker and its target (a catalog refresh lands in
    /// it).
    pub fn picker_mut(&mut self) -> Option<(HubTarget, &mut ModelPicker)> {
        match &mut self.step {
            Step::Models { target, picker } => Some((*target, picker.as_mut())),
            Step::Roles | Step::Choices { .. } => None,
        }
    }

    /// Open the model step of a chat-group role or the all-roles model.
    pub fn open_models(&mut self, target: HubTarget, picker: ModelPicker) {
        self.select_target(target);
        self.step = Step::Models {
            target,
            picker: Box::new(picker),
        };
    }

    /// Open a local role's choice step, `current` (a selector) selected.
    pub fn open_choices(&mut self, role: ModelRole, items: Vec<ChoiceItem>, current: Option<&str>) {
        self.select_target(HubTarget::Role(role));
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
            Step::Models { target, picker } => match picker.handle_key(key, kb) {
                ModelPickerAction::None => ModelHubAction::None,
                ModelPickerAction::Cancel => {
                    self.step = Step::Roles;
                    ModelHubAction::None
                }
                ModelPickerAction::Apply(selection) => ModelHubAction::Assign {
                    target: *target,
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
                            target: HubTarget::Role(*role),
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
                .selected_target()
                .map_or(ModelHubAction::None, ModelHubAction::Choose);
        }
        if !searching && (key == "x" || kb.matches(key, "tui.editor.deleteCharBackward")) {
            return self
                .selected_target()
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
            .map(|row| format!("{} {}", row.target.id(), row.target.label()))
            .collect()
    }

    /// The list rows the viewport leaves after the frame's fixed rows
    /// (title, search field, scroll row, hint, blank): every row when
    /// they fit.
    fn list_rows(&self) -> usize {
        menu_list_layout(
            Some(self.viewport_rows),
            self.rows.len(),
            self.rows.len(),
            7,
            1,
        )
    }

    /// The hub's frame.
    pub fn render(&mut self, theme: &Theme, width: usize, kb: &KeybindingsManager) -> Vec<Line> {
        let visible = self.list_rows();
        match &mut self.step {
            Step::Models { target, picker } => {
                let mut lines = vec![title_row(theme, width, *target)];
                lines.extend(picker.render(theme, width, kb));
                lines
            }
            Step::Choices { role, items, list } => {
                let mut lines = vec![title_row(theme, width, HubTarget::Role(*role))];
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
                    let primary = vec![theme.fg_span(ThemeColor::Text, row.target.label())];
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

/// The model step's title: the row being assigned.
fn title_row(theme: &Theme, width: usize, target: HubTarget) -> Line {
    crate::width::truncate_line(
        &vec![
            crate::Span::raw(" "),
            theme.fg_span(ThemeColor::Text, format!("Model for {}", target.label())),
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

    /// Every role, then the all-roles row.
    fn rows() -> Vec<RoleRow> {
        ModelRole::ALL
            .into_iter()
            .map(HubTarget::Role)
            .chain([HubTarget::AllRoles])
            .map(|target| RoleRow {
                target,
                value: format!("p/{}", target.id()),
                source: "global",
                set: true,
            })
            .collect()
    }

    #[test]
    fn the_roles_step_lists_every_row_with_its_value_and_source() {
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
        for target in ModelRole::ALL
            .into_iter()
            .map(HubTarget::Role)
            .chain([HubTarget::AllRoles])
        {
            assert!(
                text.iter().any(|line| line.contains(target.label())
                    && line.contains(&format!("p/{}", target.id()))
                    && line.contains("global")),
                "{} in {text:#?}",
                target.id()
            );
        }
    }

    /// A role's own setting is set; a role on the all-roles model shows
    /// that model under `all roles`, not as its own; an unset one its
    /// fallback.
    #[test]
    fn a_row_names_where_its_model_comes_from() {
        let value = |selector: Option<&str>, source| ModelRoleValue {
            selector: selector.map(str::to_owned),
            source,
            fallback: "the session model".to_owned(),
            thinking: None,
        };
        let memory = HubTarget::Role(ModelRole::Memory);
        assert_eq!(
            [
                RoleRow::from_value(memory, &value(Some("p/own"), ModelRoleSource::Project)),
                RoleRow::from_value(memory, &value(Some("p/all"), ModelRoleSource::AllRoles)),
                RoleRow::from_value(memory, &value(None, ModelRoleSource::Unset)),
                RoleRow::from_value(
                    HubTarget::AllRoles,
                    &value(Some("p/all"), ModelRoleSource::Global)
                ),
            ],
            [
                RoleRow {
                    target: memory,
                    value: "p/own".to_owned(),
                    source: "project",
                    set: true,
                },
                RoleRow {
                    target: memory,
                    value: "p/all".to_owned(),
                    source: "all roles",
                    set: false,
                },
                RoleRow {
                    target: memory,
                    value: "auto: the session model".to_owned(),
                    source: "default",
                    set: false,
                },
                RoleRow {
                    target: HubTarget::AllRoles,
                    value: "p/all".to_owned(),
                    source: "global",
                    set: true,
                },
            ]
        );
    }

    #[test]
    fn enter_chooses_backspace_and_x_clear_esc_closes() {
        let mut hub = ModelHub::new(rows(), 30);
        let memory = HubTarget::Role(ModelRole::Memory);
        assert_eq!(hub.handle_key("down", &kb()), ModelHubAction::None);
        assert_eq!(
            hub.handle_key("enter", &kb()),
            ModelHubAction::Choose(memory)
        );
        assert_eq!(
            hub.handle_key("backspace", &kb()),
            ModelHubAction::Clear(memory)
        );
        assert_eq!(hub.handle_key("x", &kb()), ModelHubAction::Clear(memory));
        // Up from the first row wraps to the all-roles row, the last.
        assert_eq!(hub.handle_key("up", &kb()), ModelHubAction::None);
        assert_eq!(hub.handle_key("up", &kb()), ModelHubAction::None);
        assert_eq!(
            hub.handle_key("enter", &kb()),
            ModelHubAction::Choose(HubTarget::AllRoles)
        );
        assert_eq!(hub.handle_key("escape", &kb()), ModelHubAction::Close);
    }

    #[test]
    fn typing_searches_the_roles_and_esc_clears_the_search_first() {
        let mut hub = ModelHub::new(rows(), 30);
        for key in ["d", "i", "c"] {
            hub.handle_key(key, &kb());
        }
        assert_eq!(
            hub.selected_target(),
            Some(HubTarget::Role(ModelRole::Dictation))
        );
        // With a search typed, Backspace edits it instead of clearing.
        assert_eq!(hub.handle_key("backspace", &kb()), ModelHubAction::None);
        assert_eq!(hub.handle_key("escape", &kb()), ModelHubAction::None);
        assert_eq!(
            hub.selected_target(),
            Some(HubTarget::Role(ModelRole::Chat))
        );
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
        let titles = HubTarget::Role(ModelRole::Titles);
        let mut hub = ModelHub::new(rows(), 30);
        hub.open_choices(ModelRole::Titles, items, Some("prov/m1"));
        assert_eq!(hub.step_target(), Some(titles));
        assert_eq!(
            hub.handle_key("enter", &kb()),
            ModelHubAction::Assign {
                target: titles,
                selection: ModelSelectionApplied {
                    provider: "prov".to_owned(),
                    model_id: "m1".to_owned(),
                    effort: None,
                },
            }
        );
        assert_eq!(hub.handle_key("escape", &kb()), ModelHubAction::None);
        assert_eq!(hub.step_target(), None);
        assert_eq!(hub.selected_target(), Some(titles));
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
