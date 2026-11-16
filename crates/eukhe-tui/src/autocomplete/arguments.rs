//! The argument text of a slash command alone on the prompt: the rows of
//! its words, options and live values (`eukhe_types::slash_arguments`),
//! a Tab or a row that completes the token at the cursor, and the ghost
//! hint of what the cursor's place expects.

use eukhe_types::slash_arguments::{self, starts, LiveValues, Row};

use super::{
    slash_line, slash_path_at, CombinedAutocompleteProvider, CompletionItem, CompletionResult,
    SuggestionKind, Suggestions,
};
use crate::command_paths::Resolution;

/// The text of `line` after its first `n` words (words split by spaces,
/// as the command paths read them); none when the line ends in its
/// `n`-th word.
fn after_words(line: &str, n: usize) -> Option<&str> {
    (0..n).try_fold(line, |rest, _| {
        let rest = rest.trim_start_matches(' ');
        rest.find(' ').map(|end| &rest[end..])
    })
}

fn row_item(value: &str, description: &str, hint: Option<&str>) -> CompletionItem {
    CompletionItem {
        value: value.to_string(),
        label: value.to_string(),
        description: Some(description.to_string()),
        argument_hint: hint.map(str::to_string),
        source_tag: None,
        path_row: None,
    }
}

impl CombinedAutocompleteProvider {
    /// The path a command line names (its names with one space between)
    /// and its argument text; none for a line still in its last name
    /// (one word: no call into the command rules).
    fn argument_text<'a>(&self, line: &'a str) -> Option<(Vec<String>, &'a str)> {
        if !line.trim_start_matches(' ').contains(' ') {
            return None;
        }
        let path = match self.table.resolve(line) {
            Resolution::Runs { path, .. } | Resolution::Opens { path } => path,
            Resolution::Unknown { .. } | Resolution::NoCommand => return None,
        };
        let text = after_words(line, path.len())?;
        Some((path, text))
    }

    fn row_items(&self, row: Row, token: &str) -> Vec<CompletionItem> {
        match row {
            Row::Word(word) => vec![row_item(word.name, word.description, word.then.usage)],
            Row::Opt(opt) => vec![row_item(opt.name, opt.description, opt.value)],
            Row::Live(source) => self
                .live
                .get(&source)
                .map_or(&[][..], Vec::as_slice)
                .iter()
                .filter(|item| starts(&item.value, token))
                .cloned()
                .collect(),
        }
    }

    /// The argument place a command line (`line`: the text after the `/`,
    /// the cursor at its end) is at, from one resolve: its rows (maybe
    /// none) and what the place expects (`<dollars>` after
    /// `/budget set cost=`; a path without an argument text shows its
    /// usage until its text starts). None without rows or hint.
    #[must_use]
    pub fn argument_place(&self, line: &str) -> Option<Suggestions> {
        let (path, text) = self.argument_text(line)?;
        self.place_of(&path, text)
    }

    fn place_of(&self, path: &[String], text: &str) -> Option<Suggestions> {
        let place = match slash_arguments::grammar(&path.join(" ")) {
            Some(grammar) => {
                let menu = slash_arguments::menu(grammar, text);
                Suggestions {
                    prefix: menu.token.to_string(),
                    kind: Some(SuggestionKind::Argument),
                    items: menu
                        .rows
                        .iter()
                        .flat_map(|row| self.row_items(*row, menu.token))
                        .collect(),
                    hint: menu.hint.map(str::to_string),
                }
            }
            None => Suggestions {
                prefix: String::new(),
                kind: Some(SuggestionKind::Argument),
                items: Vec::new(),
                hint: self
                    .table
                    .place(path)
                    .and_then(|place| self.table.row(place))
                    .and_then(|row| row.usage.clone())
                    .filter(|_| text.trim().is_empty()),
            },
        };
        (!place.items.is_empty() || place.hint.is_some()).then_some(place)
    }

    /// The menu of a line whose resolved path is `path` and argument text
    /// `text` lists no children: the menu walks the words before the last
    /// and lists the children of the path it lands on, and a walk past
    /// the path never returns to it, so a text holding a whole word past
    /// the path, or a path without children, answers none.
    fn menu_lists_none(&self, path: &[String], text: &str) -> bool {
        text.trim_start_matches(' ').contains(' ') || self.table.children(path).next().is_none()
    }

    /// The rows past a slash command's name (`before`: the chars before
    /// the cursor): the children of the path the line names, else the
    /// argument place of a command alone on the prompt with the cursor at
    /// its end. A key in an argument text asks the command rules once
    /// (the resolve), skipping a menu that lists none.
    pub(super) fn command_rows(
        &self,
        lines: &[String],
        cursor_line: usize,
        cursor_col: usize,
        before: &[char],
    ) -> Option<Suggestions> {
        let Some((_, line)) = slash_path_at(lines, cursor_line, cursor_col) else {
            return self.path_suggestions(&slash_line(before));
        };
        let argument = self.argument_text(&line);
        if let Some((path, text)) = &argument {
            if self.menu_lists_none(path, text) {
                return self.place_of(path, text);
            }
        }
        self.path_suggestions(&line)
            .or_else(|| argument.and_then(|(path, text)| self.place_of(&path, text)))
    }

    /// A row of the argument menu applied: the token at the cursor
    /// becomes the row's value, a space follows unless the value takes
    /// its own (`cost=`). None for an item that is no row of the line.
    pub(super) fn apply_argument(
        &self,
        lines: &[String],
        cursor_line: usize,
        cursor_col: usize,
        item: &CompletionItem,
        prefix: &str,
    ) -> Option<CompletionResult> {
        let (head, line) = slash_path_at(lines, cursor_line, cursor_col)?;
        let rows = self.argument_place(&line)?;
        if rows.prefix != prefix || !rows.items.contains(item) {
            return None;
        }
        let kept = &line[..line.len() - prefix.len()];
        let space = if item.value.ends_with('=') { "" } else { " " };
        let text = format!("{head}{kept}{}{space}", item.value);
        Some(CompletionResult {
            cursor_col: text.chars().count(),
            lines: vec![text],
            cursor_line: 0,
        })
    }

    /// Replace the live values of one source (the open effects' ids).
    pub fn set_live_values(&mut self, source: LiveValues, items: Vec<CompletionItem>) {
        self.live.insert(source, items);
    }
}

#[cfg(test)]
mod tests;
