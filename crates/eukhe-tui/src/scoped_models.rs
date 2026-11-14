//! The `/scoped-models` selector: which of the signed-in providers' models
//! the model-cycle keys (`app.model.cycleForward`/`cycleBackward`) step
//! through, and in which order. A change applies to the session at once;
//! the save key writes it to the `enabledModels` setting for later
//! sessions. Every scope edit is a pure function over [`Scope`]; the
//! session applies and saves what [`ScopedModelsAction`] names.

use std::collections::HashMap;

use eukhe_types::ai::Model;

use crate::keybindings::{format_key_text, KeybindingsManager};
use crate::menu_panel::{
    hint_row, key_hint, menu_list_layout, menu_row, no_match_row, scroll_row, search_field_lines,
    MenuSegment,
};
use crate::search_input::SearchInput;
use crate::theme::{Theme, ThemeColor};
use crate::{Line, Span};

#[cfg(test)]
mod tests;

/// The models the cycle keys step through, as `provider/id` keys.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Scope {
    /// No scope: the cycle steps through every available model.
    All,
    /// These models, in this order (a key no available model has stays
    /// listed as unavailable).
    Only(Vec<String>),
}

impl Scope {
    fn contains(&self, key: &str) -> bool {
        match self {
            Scope::All => true,
            Scope::Only(keys) => keys.iter().any(|enabled| enabled == key),
        }
    }
}

/// An explicit list that names every available model is no scope.
fn normalized(keys: Vec<String>, all: &[String]) -> Scope {
    if keys.len() == all.len() && keys.iter().all(|key| all.contains(key)) {
        Scope::All
    } else {
        Scope::Only(keys)
    }
}

/// `key` switched on or off.
fn toggled(scope: &Scope, all: &[String], key: &str) -> Scope {
    match scope {
        Scope::All => Scope::Only(all.iter().filter(|other| *other != key).cloned().collect()),
        Scope::Only(keys) if keys.iter().any(|enabled| enabled == key) => Scope::Only(
            keys.iter()
                .filter(|enabled| *enabled != key)
                .cloned()
                .collect(),
        ),
        Scope::Only(keys) => {
            let mut keys = keys.clone();
            keys.push(key.to_string());
            normalized(keys, all)
        }
    }
}

/// `targets` switched on, appended in their order.
fn with_enabled(scope: &Scope, all: &[String], targets: &[String]) -> Scope {
    match scope {
        Scope::All => Scope::All,
        Scope::Only(keys) => {
            let mut keys = keys.clone();
            for target in targets {
                if !keys.contains(target) {
                    keys.push(target.clone());
                }
            }
            normalized(keys, all)
        }
    }
}

/// `targets` switched off.
fn with_disabled(scope: &Scope, all: &[String], targets: &[String]) -> Scope {
    let keep = |key: &String| !targets.contains(key);
    match scope {
        Scope::All => Scope::Only(all.iter().filter(|key| keep(key)).cloned().collect()),
        Scope::Only(keys) => Scope::Only(keys.iter().filter(|key| keep(key)).cloned().collect()),
    }
}

/// The enabled `key` one step earlier ([`Step::Earlier`]) or later in
/// the cycle order; unchanged at either end or outside an explicit list.
fn moved(scope: &Scope, key: &str, step: Step) -> Scope {
    let Scope::Only(keys) = scope else {
        return Scope::All;
    };
    let Some(index) = keys.iter().position(|enabled| enabled == key) else {
        return scope.clone();
    };
    let target = match step {
        Step::Earlier => index.checked_sub(1),
        Step::Later => Some(index + 1).filter(|next| *next < keys.len()),
    };
    let mut keys = keys.clone();
    if let Some(target) = target {
        keys.swap(index, target);
    }
    Scope::Only(keys)
}

/// The listed order: the enabled models in cycle order, then the rest in
/// catalog order.
fn listed_keys(scope: &Scope, all: &[String]) -> Vec<String> {
    match scope {
        Scope::All => all.to_vec(),
        Scope::Only(keys) => keys
            .iter()
            .cloned()
            .chain(all.iter().filter(|key| !keys.contains(key)).cloned())
            .collect(),
    }
}

/// A reorder direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Step {
    Earlier,
    Later,
}

/// Whether the shown scope differs from the saved setting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Saved {
    Yes,
    No,
}

/// One key press's outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopedModelsAction {
    /// Navigation or search only.
    None,
    /// The scope changed: the session applies it.
    Changed(Scope),
    /// The save key: the session writes the scope to the settings.
    Save(Scope),
    /// Esc (or Ctrl+C on an empty search): close the selector.
    Close,
}

/// The selector.
#[derive(Debug)]
pub struct ScopedModelsSelector {
    /// The available models, in catalog order.
    models: Vec<Model>,
    /// `provider/id` of each model, indexed alike.
    keys: Vec<String>,
    /// The row label of each model, indexed alike.
    labels: Vec<String>,
    scope: Scope,
    search: SearchInput,
    /// The listed keys that match the search, in listed order.
    filtered: Vec<String>,
    selected: usize,
    saved: Saved,
    viewport_rows: usize,
    /// The thinking level each scoped entry of the session pins
    /// (`provider/id` key to level), carried to what the session applies
    /// and saves.
    pinned_levels: HashMap<String, String>,
}

impl ScopedModelsSelector {
    /// The selector over `models` (the signed-in providers' models),
    /// showing `scope` (the session's) with the levels its entries pin.
    #[must_use]
    pub fn new(
        models: Vec<Model>,
        scope: Scope,
        pinned_levels: HashMap<String, String>,
        viewport_rows: usize,
    ) -> Self {
        let keys = models.iter().map(model_key).collect();
        let labels = crate::model_labels::row_labels(&models);
        let mut selector = ScopedModelsSelector {
            models,
            keys,
            labels,
            scope,
            search: SearchInput::new(),
            filtered: Vec::new(),
            selected: 0,
            saved: Saved::Yes,
            viewport_rows,
            pinned_levels,
        };
        selector.refilter();
        selector
    }

    /// The levels the session's scoped entries pin.
    #[must_use]
    pub fn pinned_levels(&self) -> &HashMap<String, String> {
        &self.pinned_levels
    }

    /// The scope shown now.
    #[must_use]
    pub fn scope(&self) -> &Scope {
        &self.scope
    }

    /// Pasted text goes to the search field.
    pub fn paste(&mut self, text: &str) {
        self.search.paste(text);
        self.refilter();
    }

    /// Mark the shown scope as the saved one (after the settings write).
    pub fn mark_saved(&mut self) {
        self.saved = Saved::Yes;
    }

    /// Replace the available models (a catalog refresh landed): the scope
    /// and the selected row stay.
    pub fn update_models(&mut self, models: Vec<Model>) {
        let selected = self.selected_key().map(str::to_string);
        self.keys = models.iter().map(model_key).collect();
        self.labels = crate::model_labels::row_labels(&models);
        self.models = models;
        self.refilter();
        if let Some(position) =
            selected.and_then(|key| self.filtered.iter().position(|listed| *listed == key))
        {
            self.selected = position;
        }
    }

    /// The keys the session's cycle steps through for `scope`: its
    /// available models in order; none (the whole catalog) for no scope,
    /// for a scope without an available model, and for one that names
    /// every available model.
    #[must_use]
    pub fn session_keys(&self, scope: &Scope) -> Vec<String> {
        let Scope::Only(keys) = scope else {
            return Vec::new();
        };
        let available: Vec<String> = keys
            .iter()
            .filter(|key| self.keys.contains(key))
            .cloned()
            .collect();
        if available.len() == self.keys.len() {
            return Vec::new();
        }
        available
    }

    fn index_of(&self, key: &str) -> Option<usize> {
        self.keys.iter().position(|known| known == key)
    }

    fn selected_key(&self) -> Option<&str> {
        self.filtered.get(self.selected).map(String::as_str)
    }

    /// Rebuild the listed rows for the scope and the search, keeping the
    /// selection's position in range.
    fn refilter(&mut self) {
        let listed = listed_keys(&self.scope, &self.keys);
        let query = self.search.value().trim().to_string();
        self.filtered = if query.is_empty() {
            listed
        } else {
            let texts: Vec<String> = listed
                .iter()
                .map(|key| match self.index_of(key) {
                    Some(index) => format!(
                        "{key} {} {} {}",
                        self.models[index].provider, self.models[index].id, self.labels[index]
                    ),
                    None => key.clone(),
                })
                .collect();
            let positions: Vec<usize> = (0..listed.len()).collect();
            crate::fuzzy::fuzzy_filter(&positions, &query, |at| texts[*at].clone())
                .into_iter()
                .map(|at| listed[at].clone())
                .collect()
        };
        self.selected = self.selected.min(self.filtered.len().saturating_sub(1));
    }

    /// Apply a new scope: re-list, keep the selection on `follow` when
    /// given, and report the change.
    fn change(&mut self, scope: Scope, follow: Option<String>) -> ScopedModelsAction {
        self.scope = scope;
        self.saved = Saved::No;
        self.refilter();
        if let Some(position) =
            follow.and_then(|key| self.filtered.iter().position(|listed| *listed == key))
        {
            self.selected = position;
        }
        ScopedModelsAction::Changed(self.scope.clone())
    }

    /// The keys a bulk edit reaches: the search's matches while searching,
    /// else every available model.
    fn bulk_targets(&self) -> Vec<String> {
        if self.search.value().trim().is_empty() {
            self.keys.clone()
        } else {
            self.filtered.clone()
        }
    }

    /// One key id.
    pub fn handle_key(&mut self, key: &str, kb: &KeybindingsManager) -> ScopedModelsAction {
        if self.navigate(key, kb) {
            return ScopedModelsAction::None;
        }
        let selected = self.selected_key().map(str::to_string);
        for (binding, step) in [
            ("app.models.reorderUp", Step::Earlier),
            ("app.models.reorderDown", Step::Later),
        ] {
            if kb.matches(key, binding) {
                let Some(selected) = selected else {
                    return ScopedModelsAction::None;
                };
                let next = moved(&self.scope, &selected, step);
                if next == self.scope {
                    return ScopedModelsAction::None;
                }
                return self.change(next, Some(selected));
            }
        }
        if kb.matches(key, "tui.select.confirm") {
            return match selected {
                Some(selected) => {
                    let next = toggled(&self.scope, &self.keys, &selected);
                    self.change(next, Some(selected))
                }
                None => ScopedModelsAction::None,
            };
        }
        if kb.matches(key, "app.models.enableAll") {
            let next = with_enabled(&self.scope, &self.keys, &self.bulk_targets());
            return self.change(next, selected);
        }
        if kb.matches(key, "app.models.clearAll") {
            let targets = match (&self.scope, self.search.value().trim().is_empty()) {
                (Scope::Only(keys), true) => keys.clone(),
                (Scope::All | Scope::Only(_), _) => self.bulk_targets(),
            };
            let next = with_disabled(&self.scope, &self.keys, &targets);
            return self.change(next, selected);
        }
        if kb.matches(key, "app.models.toggleProvider") {
            let Some(provider) = selected
                .as_deref()
                .and_then(|key| self.index_of(key))
                .map(|index| self.models[index].provider.clone())
            else {
                return ScopedModelsAction::None;
            };
            let targets: Vec<String> = self
                .models
                .iter()
                .zip(&self.keys)
                .filter(|(model, _)| model.provider == provider)
                .map(|(_, key)| key.clone())
                .collect();
            let next = if targets.iter().all(|target| self.scope.contains(target)) {
                with_disabled(&self.scope, &self.keys, &targets)
            } else {
                with_enabled(&self.scope, &self.keys, &targets)
            };
            return self.change(next, selected);
        }
        if kb.matches(key, "app.models.save") {
            return ScopedModelsAction::Save(self.scope.clone());
        }
        if key == "ctrl+c" {
            if self.search.value().is_empty() {
                return ScopedModelsAction::Close;
            }
            self.search = SearchInput::new();
            self.refilter();
            return ScopedModelsAction::None;
        }
        if kb.matches(key, "tui.select.cancel") {
            return ScopedModelsAction::Close;
        }
        let before = self.search.value().to_string();
        self.search.handle_key(key, kb);
        if self.search.value() != before {
            self.refilter();
        }
        ScopedModelsAction::None
    }

    /// Up/Down/Page keys: whether the key moved the selection.
    fn navigate(&mut self, key: &str, kb: &KeybindingsManager) -> bool {
        let page = isize::try_from(self.list_rows()).unwrap_or(isize::MAX);
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
        let Some(last) = self.filtered.len().checked_sub(1) else {
            return true;
        };
        self.selected = match step {
            -1 if self.selected == 0 => last,
            1 if self.selected == last => 0,
            _ => self.selected.saturating_add_signed(step).min(last),
        };
        true
    }

    /// The list rows the viewport leaves after the frame's fixed rows
    /// (title, note, search field, scroll row, detail, hint, blank).
    fn list_rows(&self) -> usize {
        menu_list_layout(Some(self.viewport_rows), 10, self.filtered.len(), 9, 1)
    }

    fn window(&self) -> (usize, usize) {
        let visible = self.list_rows().max(1);
        let start = self
            .selected
            .saturating_sub(visible / 2)
            .min(self.filtered.len().saturating_sub(visible));
        (start, (start + visible).min(self.filtered.len()))
    }

    /// The count beside the title: `all enabled`, or `<n>/<total>
    /// enabled` plus the unavailable entries; `(unsaved)` while the
    /// scope differs from the saved setting.
    fn count_text(&self) -> String {
        let count = match &self.scope {
            Scope::All => "all enabled".to_string(),
            Scope::Only(keys) => {
                let available = keys.iter().filter(|key| self.keys.contains(key)).count();
                let missing = keys.len() - available;
                let total = self.keys.len();
                if missing > 0 {
                    format!("{available}/{total} enabled, {missing} unavailable")
                } else {
                    format!("{available}/{total} enabled")
                }
            }
        };
        match self.saved {
            Saved::Yes => count,
            Saved::No => format!("{count} (unsaved)"),
        }
    }

    /// The selector's frame.
    #[must_use]
    pub fn render(&self, theme: &Theme, width: usize, kb: &KeybindingsManager) -> Vec<Line> {
        let truncate = |line: Line| crate::width::truncate_line(&line, width, "");
        let mut lines = vec![truncate(vec![
            Span::raw(" "),
            theme.fg_span(ThemeColor::Text, "Scoped models"),
            Span::raw("  "),
            theme.fg_span(ThemeColor::Muted, self.count_text()),
        ])];
        let save = key_hint(kb, &["app.models.save"], "saves it to settings");
        let note = match save {
            Some(save) => format!("Applies to this session; {save}."),
            None => "Applies to this session.".to_string(),
        };
        lines.push(truncate(vec![
            Span::raw(" "),
            theme.fg_span(ThemeColor::Muted, note),
        ]));
        lines.extend(search_field_lines(
            theme,
            width,
            self.search.value(),
            self.search.cursor(),
            true,
            "Search models",
        ));
        let (start, end) = self.window();
        let window = &self.filtered[start..end];
        let window_labels: Vec<&str> = window
            .iter()
            .map(|key| {
                self.index_of(key)
                    .map_or(key.as_str(), |index| self.labels[index].as_str())
            })
            .collect();
        let shared = crate::model_labels::shared_prefixes(&window_labels);
        for (offset, (key, (label, shared))) in window
            .iter()
            .zip(window_labels.iter().zip(shared))
            .enumerate()
        {
            let selected = start + offset == self.selected;
            let available = self.index_of(key);
            let mark = if available.is_some() && self.scope.contains(key) {
                "[x] "
            } else {
                "[ ] "
            };
            let trailing =
                available.map_or("unavailable", |index| self.models[index].provider.as_str());
            // The label takes the row less the marker, the check box and
            // the trailing provider; the selected row takes the provider's
            // columns when its label needs them.
            let inner = width.saturating_sub(2 + mark.len());
            let room = inner.saturating_sub(trailing.len() + 2);
            let (text, trailing) = if selected && crate::width::str_width(label) > room {
                (crate::model_labels::cut_label(label, shared, inner), "")
            } else {
                (
                    crate::model_labels::cut_label(label, shared, room),
                    trailing,
                )
            };
            let tone = if available.is_some() {
                ThemeColor::Text
            } else {
                ThemeColor::Dim
            };
            let primary = vec![
                theme.fg_span(ThemeColor::Accent, mark),
                theme.fg_span(tone, text),
            ];
            let segments: Vec<MenuSegment> = std::iter::once(trailing)
                .filter(|text| !text.is_empty())
                .map(MenuSegment::muted)
                .collect();
            lines.push(menu_row(theme, width, primary, &segments, selected));
        }
        if start > 0 || end < self.filtered.len() {
            lines.push(scroll_row(
                theme,
                width,
                self.selected + 1,
                self.filtered.len(),
            ));
        }
        if self.filtered.is_empty() {
            lines.push(no_match_row(theme, width, "No matching models"));
        } else if let Some(key) = self.selected_key() {
            lines.push(truncate(vec![
                Span::raw("  "),
                theme.fg_span(ThemeColor::Muted, key.to_string()),
            ]));
        }
        let hints = [
            key_hint(kb, &["tui.select.confirm"], "toggle"),
            key_hint(kb, &["app.models.enableAll"], "all"),
            key_hint(kb, &["app.models.clearAll"], "none"),
            reorder_hint(kb),
            key_hint(kb, &["app.models.save"], "save"),
            key_hint(kb, &["tui.select.cancel"], "close"),
        ];
        let hint = hints
            .iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>()
            .join(crate::glyphs::SEP);
        // The refresh pointer rides the hint only when the row holds it.
        let with_refresh = format!("{hint}{}{REFRESH_HINT}", crate::glyphs::SEP);
        let hint = if crate::width::str_width(&with_refresh) < width {
            with_refresh
        } else {
            hint
        };
        lines.push(hint_row(theme, width, &hint));
        lines.push(Vec::new());
        lines
    }
}

/// Where the selector points for models the catalog lacks.
const REFRESH_HINT: &str = "/models refresh adds new models";

/// The reorder keys as one hint: `Alt+up/down reorder` when both keys
/// share their modifiers, else each key spelled out.
fn reorder_hint(kb: &KeybindingsManager) -> Option<String> {
    let up = kb
        .first_key("app.models.reorderUp")
        .map(|key| format_key_text(&key));
    let down = kb
        .first_key("app.models.reorderDown")
        .map(|key| format_key_text(&key));
    let keys = match (up, down) {
        (Some(up), Some(down)) => match (up.rsplit_once('+'), down.rsplit_once('+')) {
            (Some((up_mods, up_key)), Some((down_mods, down_key))) if up_mods == down_mods => {
                format!("{up_mods}+{up_key}/{down_key}")
            }
            _ => format!("{up}/{down}"),
        },
        (Some(key), None) | (None, Some(key)) => key,
        (None, None) => return None,
    };
    Some(format!("{keys} reorder"))
}

/// The `provider/id` key of a model.
#[must_use]
pub fn model_key(model: &Model) -> String {
    format!("{}/{}", model.provider, model.id)
}
