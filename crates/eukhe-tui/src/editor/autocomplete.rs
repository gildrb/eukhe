//! Editor autocomplete integration: slash-command and file/path completion via
//! the configured provider, and the command paths' Tab and Enter
//! (`command_paths`: the Bend model decides what a key does to a slash
//! command alone on the prompt).

use std::sync::mpsc::TryRecvError;

use super::text_utils::{char_at, char_prefix, ends_with_symbol_token};
use super::{AutocompleteSearch, Editor, EditorEvent, PendingAutocomplete};
use crate::command_paths::PathKey;

impl Editor {
    // ---- autocomplete ------------------------------------------------------

    pub(crate) fn current_slash_command_context(
        &self,
    ) -> Option<crate::autocomplete::SlashContext> {
        crate::autocomplete::get_slash_command_context(
            &self.lines,
            self.cursor_line,
            self.cursor_col,
        )
    }

    /// The `/command <partial>` argument context at the prompt start, when
    /// the cursor sits in the argument text of a recognized command token:
    /// the command name plus the typed partial. Tab interception uses this
    /// to open a picker-command's menu filtered to the partial.
    #[must_use]
    pub fn picker_argument_context(&self) -> Option<(String, String)> {
        let context = self.current_slash_command_context()?;
        if context.kind != crate::autocomplete::SlashKind::Argument || !context.at_prompt_start {
            return None;
        }
        // The context only reports text up to the cursor, so a cursor
        // inside the argument (`/model g|p`) would filter the picker on
        // the head and leave the tail behind on accept. Only intercept
        // when the cursor sits at the argument's end.
        let line: Vec<char> = self.lines[self.cursor_line].chars().collect();
        let remainder = &line[self.cursor_col.min(line.len())..];
        if remainder.iter().any(|c| !c.is_whitespace()) {
            return None;
        }
        // Applying from the picker clears the editor (the command is
        // fulfilled), so draft text on a later line would be silently
        // discarded with it. Only intercept when every line below the
        // cursor's is whitespace.
        let later_line_has_text = self
            .lines
            .iter()
            .skip(self.cursor_line + 1)
            .any(|line| line.chars().any(|c| !c.is_whitespace()));
        if later_line_has_text {
            return None;
        }
        context.command_name.map(|name| (name, context.prefix))
    }

    pub(crate) fn is_slash_name_completion_at_prompt_start(&self) -> bool {
        let ctx = self.current_slash_command_context();
        let kind_slash = self
            .autocomplete
            .as_ref()
            .is_some_and(|s| s.kind == Some(crate::autocomplete::SuggestionKind::SlashCommand));
        let default_slash = self.autocomplete.is_some()
            && self.autocomplete.as_ref().unwrap().prefix.starts_with('/');
        (kind_slash || default_slash)
            && matches!(ctx, Some(c) if c.kind == crate::autocomplete::SlashKind::Name && c.at_prompt_start)
    }

    pub(crate) fn apply_completion(
        &self,
        item: &crate::autocomplete::CompletionItem,
        prefix: &str,
    ) -> crate::autocomplete::CompletionResult {
        match self.autocomplete_provider.as_ref() {
            Some(provider) => provider.apply_completion(
                &self.lines,
                self.cursor_line,
                self.cursor_col,
                item,
                prefix,
            ),
            None => crate::autocomplete::CompletionResult {
                lines: self.lines.clone(),
                cursor_line: self.cursor_line,
                cursor_col: self.cursor_col,
            },
        }
    }

    /// The slash command alone on the prompt with the cursor at its end:
    /// the text up to and with its `/`, and the line the command paths
    /// read.
    pub(crate) fn slash_path(&self) -> Option<(String, String)> {
        crate::autocomplete::slash_path_at(&self.lines, self.cursor_line, self.cursor_col)
    }

    /// Tab or Enter at the end of a slash command, with the table place of
    /// the selected menu row (none without a row): the command paths' key
    /// rule rewrites the line, opens the menu at it, or submits it. False
    /// when the prompt holds no slash command ending at the cursor (the
    /// caller keeps its own handling).
    pub(crate) fn apply_path_key(&mut self, key: PathKey, place: Option<usize>) -> bool {
        let Some((head, line)) = self.slash_path() else {
            return false;
        };
        let Some(table) = self.command_table() else {
            return false;
        };
        let out = table.key(&line, place, key);
        // The usage of the path a completion lands on, for the ghost hint
        // while its text stays.
        let landed = format!("{head}{}", out.line);
        let hint = table
            .place(
                &out.line
                    .split(' ')
                    .filter(|word| !word.is_empty())
                    .map(str::to_lowercase)
                    .collect::<Vec<_>>(),
            )
            .and_then(|place| table.row(place))
            .and_then(|row| row.usage.clone());
        self.cancel_autocomplete();
        if out.line != line {
            self.push_undo_snapshot();
            self.last_action = None;
            self.selection_anchor = None;
            self.lines = vec![landed.clone()];
            self.cursor_line = 0;
            self.set_cursor_col(landed.chars().count());
            self.emit(EditorEvent::Changed(self.get_text()));
        }
        self.path_hint = hint.map(|hint| (landed, hint));
        if out.submit {
            if !self.disable_submit {
                self.submit_value();
            }
            return true;
        }
        if out.open {
            // Tab with no row completes files past the command's own
            // rows (`/export pa` + Tab), as before the command paths.
            let files = key == PathKey::Tab
                && place.is_none()
                && self
                    .current_slash_command_context()
                    .is_some_and(|c| c.kind == crate::autocomplete::SlashKind::Argument);
            self.request_autocomplete(files, files);
        }
        true
    }

    /// The ghost hint after the cursor at the end of a slash command: the
    /// rest of the selected row's name and its usage while the slash menu
    /// is open, else the usage of the path a Tab or Enter completed.
    #[must_use]
    pub fn ghost_hint(&self) -> Option<String> {
        self.slash_path()?;
        if let Some(state) = self.autocomplete.as_ref() {
            if state.kind != Some(crate::autocomplete::SuggestionKind::SlashCommand) {
                return None;
            }
            let item = state.selected_item()?;
            let typed = state.prefix.strip_prefix('/').unwrap_or(&state.prefix);
            let typed_len = typed.chars().count();
            let rest: String = if item.value.to_lowercase().starts_with(&typed.to_lowercase()) {
                item.value.chars().skip(typed_len).collect()
            } else {
                String::new()
            };
            let hint = match (rest.is_empty(), item.argument_hint) {
                (true, None) => return None,
                (true, Some(usage)) => usage,
                (false, None) => rest,
                (false, Some(usage)) => format!("{rest} {usage}"),
            };
            return Some(hint);
        }
        let (text, hint) = self.path_hint.as_ref()?;
        (*text == self.get_text()).then(|| hint.clone())
    }

    pub(crate) fn handle_tab_completion(&mut self) {
        if self.autocomplete_provider.is_none() {
            return;
        }
        // An empty prompt has nothing to complete: the forced file pass
        // would otherwise list the whole cwd (`file_suggestions("")`),
        // a junk menu with no anchor token. Tab on an empty (or
        // whitespace-only) prompt is a no-op; completion after text is
        // typed keeps its existing behavior.
        if self.get_text().trim().is_empty() {
            return;
        }
        // Tab at the end of a slash command: the command paths' key rule
        // (no row: the menu of the line opens).
        if self.apply_path_key(PathKey::Tab, None) {
            return;
        }
        if matches!(self.current_slash_command_context(), Some(c) if c.kind == crate::autocomplete::SlashKind::Name)
        {
            self.request_autocomplete(false, true);
        } else {
            self.request_autocomplete(true, true);
        }
    }

    pub(crate) fn maybe_autocomplete_after_insert(&mut self, ch: &str) {
        if self.autocomplete.is_none() {
            let slash_ctx = self.current_slash_command_context();
            let c = ch.chars().next().unwrap_or(' ');
            if c == '/'
                && matches!(&slash_ctx, Some(ctx) if ctx.kind == crate::autocomplete::SlashKind::Name)
            {
                self.request_autocomplete(false, false);
            } else if c == ' ' && self.slash_path().is_some() {
                // A space after a command or subcommand opens the menu of
                // its children at once.
                self.request_autocomplete(false, false);
            } else if c == '@' || c == '#' {
                let current_line = &self.lines[self.cursor_line];
                let before = char_prefix(current_line, self.cursor_col);
                let prev = char_at(&before, before.chars().count().saturating_sub(2));
                if before.chars().count() <= 1 || prev == Some(' ') || prev == Some('\t') {
                    self.request_autocomplete(false, false);
                }
            } else if c.is_ascii_alphanumeric() || ".-_".contains(c) {
                let current_line = &self.lines[self.cursor_line];
                let before = char_prefix(current_line, self.cursor_col);
                if slash_ctx.is_some() || ends_with_symbol_token(&before) {
                    self.request_autocomplete(false, false);
                }
            }
        } else {
            self.refresh_autocomplete_after_edit(false);
        }
    }

    pub(crate) fn request_autocomplete(&mut self, force: bool, explicit_tab: bool) {
        let Some(provider) = self.autocomplete_provider.as_ref() else {
            return;
        };
        if force {
            let should = provider.should_trigger_file_completion(
                &self.lines,
                self.cursor_line,
                self.cursor_col,
            );
            if !should {
                return;
            }
        }
        // A new request aborts the in-flight search (TS cancels the
        // previous lookup at request time): dropping the handle sets
        // its cancel flag and the walk quits.
        self.autocomplete_search = None;
        // TS resolves suggestions asynchronously (a `getSuggestions`
        // promise): the dropdown only materializes after the current
        // keystroke batch, so the request parks here and the host loop
        // materializes it when the input queue drains.
        self.pending_autocomplete = Some(PendingAutocomplete {
            force,
            explicit_tab,
        });
    }

    /// Materialize the parked suggestion request (TS
    /// `runAutocompleteRequest` after the promise resolves). The host loop
    /// calls this once the input queue drains, so a burst of keystrokes
    /// never sees a dropdown open mid-batch; a background `@` search is
    /// polled here too.
    pub fn materialize_autocomplete(&mut self) {
        if let Some(pending) = self.pending_autocomplete.take() {
            self.run_autocomplete_request(pending);
            return;
        }
        let Some(active) = self.autocomplete_search.take() else {
            return;
        };
        // TS `isAutocompleteRequestCurrent`: the editor moved past the
        // snapshot the search answers, so the result would land stale --
        // drop the handle (cancelling the walk) without touching the UI.
        if self.lines != active.lines
            || self.cursor_line != active.cursor_line
            || self.cursor_col != active.cursor_col
        {
            return;
        }
        // An empty channel keeps the search running for the next tick; a
        // closed one (a panicked walk thread) reads as no suggestions.
        let result = match active.search.results.try_recv() {
            Ok(result) => result,
            Err(TryRecvError::Empty) => {
                self.autocomplete_search = Some(active);
                return;
            }
            Err(TryRecvError::Disconnected) => None,
        };
        self.apply_suggestions(result, active.request);
    }

    fn run_autocomplete_request(&mut self, request: PendingAutocomplete) {
        let Some(provider) = self.autocomplete_provider.as_ref() else {
            return;
        };
        match provider.get_suggestions(
            &self.lines,
            self.cursor_line,
            self.cursor_col,
            request.force,
        ) {
            Some(crate::autocomplete::SuggestionLookup::Searching(search)) => {
                self.autocomplete_search = Some(AutocompleteSearch {
                    search,
                    request,
                    lines: self.lines.clone(),
                    cursor_line: self.cursor_line,
                    cursor_col: self.cursor_col,
                });
            }
            Some(crate::autocomplete::SuggestionLookup::Ready(suggestions)) => {
                self.apply_suggestions(Some(suggestions), request);
            }
            None => self.apply_suggestions(None, request),
        }
    }

    /// Apply a resolved lookup (TS `runAutocompleteRequest` once the
    /// promise settles): no items cancels the open menu, a forced Tab
    /// with a single item applies it inline, and otherwise the dropdown
    /// opens with the best match selected.
    fn apply_suggestions(
        &mut self,
        suggestions: Option<crate::autocomplete::Suggestions>,
        request: PendingAutocomplete,
    ) {
        let Some(suggestions) = suggestions else {
            self.cancel_autocomplete();
            return;
        };
        if suggestions.items.is_empty() {
            self.cancel_autocomplete();
            return;
        }
        if request.force && request.explicit_tab && suggestions.items.len() == 1 {
            let item = suggestions.items[0].clone();
            self.push_undo_snapshot();
            self.last_action = None;
            let prefix = suggestions.prefix;
            let result = self.apply_completion(&item, &prefix);
            self.lines = result.lines;
            self.cursor_line = result.cursor_line;
            self.set_cursor_col(result.cursor_col);
            self.emit(EditorEvent::Changed(self.get_text()));
            return;
        }
        let matching_prefix =
            if suggestions.kind == Some(crate::autocomplete::SuggestionKind::SlashCommand) {
                suggestions
                    .prefix
                    .strip_prefix('/')
                    .unwrap_or(&suggestions.prefix)
                    .to_string()
            } else {
                suggestions.prefix.clone()
            };
        let mut state = crate::autocomplete::AutocompleteState::new(
            suggestions.items,
            5,
            suggestions.prefix.clone(),
            suggestions.kind,
        );
        if let Some(idx) = state.best_match_index(&matching_prefix) {
            state.set_selected_index(idx);
        }
        let was_showing = self.autocomplete.is_some();
        self.autocomplete = Some(state);
        if was_showing != self.autocomplete.is_some() {
            self.emit(EditorEvent::AutocompleteToggled(
                self.autocomplete.is_some(),
            ));
        }
    }

    pub(crate) fn refresh_autocomplete_after_edit(&mut self, retrigger: bool) {
        let current_line = &self.lines[self.cursor_line];
        let before = char_prefix(current_line, self.cursor_col);
        let has_ctx =
            self.current_slash_command_context().is_some() || ends_with_symbol_token(&before);

        // An edit that empties the prompt cancels both the open menu and
        // the parked request (a parked request can exist without an open
        // menu; if it survived, it would materialize a dropdown on an
        // empty prompt).
        if self.get_text().trim().is_empty() {
            self.cancel_autocomplete();
            return;
        }
        if self.autocomplete.is_some() {
            let force = self.autocomplete.as_ref().is_some_and(|s| s.forced);
            self.request_autocomplete(force, false);
            return;
        }
        if retrigger && has_ctx {
            self.request_autocomplete(false, false);
        }
    }

    pub fn cancel_autocomplete(&mut self) {
        let was = self.autocomplete.is_some();
        self.autocomplete = None;
        self.pending_autocomplete = None;
        self.autocomplete_search = None;
        if was {
            self.emit(EditorEvent::AutocompleteToggled(false));
        }
    }

    // ---- layout / rendering ------------------------------------------------
}
