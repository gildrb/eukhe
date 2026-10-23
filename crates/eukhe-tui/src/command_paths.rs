//! The paths of the slash commands (docs/interface.md, "Slash commands"):
//! the path a typed line names, the menu below its last word, and what Tab
//! and Enter do to the line. The rules run as the Bend model
//! `bend/command.bend`, one call of the compiled core each
//! (`bend/ffi_command.bend`; LAWS.bend section `commands`). This module
//! builds the table the model reads (the registry's commands and
//! subcommands, the interface's argument lists) and reads its answers.
//!
//! A line is the text after the leading `/`. Every name crosses in
//! lowercase (the model matches typed words in any case against lowercase
//! names: the laws' well-formed table).

use std::collections::HashMap;

use eukhe_bend::wire::{Reader, WireError, Writer, STR_MAX};
use eukhe_bend::Entry;
use eukhe_types::slash_commands::Subcommand;

use crate::autocomplete::{CompletionItem, SlashCommandEntry};

/// The longest line the menu and the keys ask the model about: a longer
/// line is argument text (no menu, Enter submits it as typed). A submitted
/// line is resolved up to the wire's [`STR_MAX`].
pub const KEY_LINE_MAX: usize = 4096;

/// One declared path: a command, a subcommand, or an argument value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathRow {
    pub path: Vec<String>,
    pub aliases: Vec<String>,
    pub description: Option<String>,
    /// The text that follows the path (the menu's trailing hint and the
    /// editor's ghost hint).
    pub usage: Option<String>,
    pub source_tag: Option<String>,
    /// Enter on the bare path runs it (a default, or no child).
    run: bool,
    /// A word that names no child starts the path's argument text.
    free: bool,
    /// The path expects text after it (a completion leaves a space).
    arg: bool,
}

impl PathRow {
    /// The last name of the path.
    #[must_use]
    pub fn name(&self) -> &str {
        self.path.last().map_or("", String::as_str)
    }
}

/// What a submitted line does (`bend/command.bend` `resolve`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    /// Run the path with its argument text (as typed, untrimmed).
    Runs { path: Vec<String>, args: String },
    /// A bare path with no default: its menu opens instead.
    Opens { path: Vec<String> },
    /// A word below `path` that names none of its children: nothing runs.
    Unknown { path: Vec<String>, word: String },
    /// The first word names no command of the table.
    NoCommand,
}

/// The menu of a typed line (`bend/command.bend` `menu`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathMenu {
    /// The first word: the command names (ranked fuzzily by the provider).
    Names,
    /// The children of `path` the last word starts, by table place.
    Kids { path: Vec<String>, rows: Vec<usize> },
    /// No menu.
    Shut,
}

/// A key the model decides.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathKey {
    Tab,
    Enter,
}

/// A key's answer: the new line, whether its menu opens, whether it is
/// submitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyOutcome {
    pub line: String,
    pub open: bool,
    pub submit: bool,
}

/// The table of every declared path, in menu order.
#[derive(Debug, Clone, Default)]
pub struct CommandTable {
    rows: Vec<PathRow>,
    places: HashMap<Vec<String>, usize>,
}

impl CommandTable {
    /// The table of `commands` (each with its subcommands) and the
    /// argument lists keyed by path (`"tier"`, `"workflows size"`).
    #[must_use]
    pub fn build(
        commands: &[SlashCommandEntry],
        arguments: &HashMap<&'static str, Vec<CompletionItem>>,
    ) -> CommandTable {
        let mut table = CommandTable::default();
        for command in commands {
            let name = command.name.to_lowercase();
            let values = arguments.get(name.as_str()).map_or(&[][..], Vec::as_slice);
            let has_kids = !command.subcommands.is_empty() || !values.is_empty();
            table.push(PathRow {
                path: vec![name],
                aliases: command.aliases.iter().map(|a| a.to_lowercase()).collect(),
                description: command.description.clone(),
                usage: command.argument_hint.clone(),
                source_tag: command.source_tag.clone(),
                run: !has_kids || command.subcommand_optional,
                free: command.takes_argument || !has_kids,
                arg: command.takes_argument,
            });
        }
        for command in commands {
            let name = command.name.to_lowercase();
            for sub in command.subcommands {
                table.push_subcommand(&name, sub, arguments, command.takes_argument);
            }
            let values = arguments.get(name.as_str()).map_or(&[][..], Vec::as_slice);
            table.push_values(std::slice::from_ref(&name), values, command.takes_argument);
        }
        table
    }

    fn push(&mut self, row: PathRow) {
        self.places
            .entry(row.path.clone())
            .or_insert(self.rows.len());
        self.rows.push(row);
    }

    fn push_subcommand(
        &mut self,
        command: &str,
        sub: &Subcommand,
        arguments: &HashMap<&'static str, Vec<CompletionItem>>,
        text_follows: bool,
    ) {
        let path = vec![command.to_string(), sub.name.to_lowercase()];
        let key = path.join(" ");
        let values = arguments.get(key.as_str()).map_or(&[][..], Vec::as_slice);
        self.push(PathRow {
            path: path.clone(),
            aliases: Vec::new(),
            description: Some(sub.description.to_string()),
            usage: sub.usage.map(str::to_string),
            source_tag: None,
            run: !sub.usage.is_some_and(|usage| usage.starts_with('<')),
            free: values.is_empty(),
            arg: sub.usage.is_some(),
        });
        self.push_values(&path, values, text_follows);
    }

    /// The argument values below `path`: leaves; text follows them when
    /// the command takes text.
    fn push_values(&mut self, path: &[String], values: &[CompletionItem], text_follows: bool) {
        for value in values {
            let mut full = path.to_vec();
            full.push(value.value.to_lowercase());
            self.push(PathRow {
                path: full,
                aliases: Vec::new(),
                description: value.description.clone(),
                usage: None,
                source_tag: None,
                run: true,
                free: true,
                arg: text_follows,
            });
        }
    }

    #[must_use]
    pub fn row(&self, place: usize) -> Option<&PathRow> {
        self.rows.get(place)
    }

    /// The place of a declared path.
    #[must_use]
    pub fn place(&self, path: &[String]) -> Option<usize> {
        self.places.get(path).copied()
    }

    /// The children of `path`, in table order.
    pub fn children<'a>(&'a self, path: &'a [String]) -> impl Iterator<Item = &'a PathRow> {
        self.rows
            .iter()
            .filter(move |row| row.path.len() == path.len() + 1 && row.path.starts_with(path))
    }

    fn write_table(&self, w: &mut Writer) {
        w.count(self.rows.len());
        for row in &self.rows {
            w.count(row.path.len());
            for name in &row.path {
                w.str(name);
            }
            w.count(row.aliases.len());
            for alias in &row.aliases {
                w.str(alias);
            }
            w.bool(row.run).bool(row.free).bool(row.arg);
        }
    }

    /// What the submitted `line` does; a line past the wire's longest
    /// string names no command (it goes to the model as a prompt).
    #[must_use]
    pub fn resolve(&self, line: &str) -> Resolution {
        if line.chars().count() > STR_MAX {
            return Resolution::NoCommand;
        }
        crate::bend_core::decide(
            Entry::Command,
            |w| {
                self.write_table(w);
                w.tag(0).str(line);
            },
            |r| match r.tag_of(4, "a resolution tag")? {
                0 => Ok(Resolution::Runs {
                    path: read_path(r)?,
                    args: r.str()?.to_string(),
                }),
                1 => Ok(Resolution::Opens {
                    path: read_path(r)?,
                }),
                2 => Ok(Resolution::Unknown {
                    path: read_path(r)?,
                    word: r.str()?.to_string(),
                }),
                // `tag_of` answered at most 3.
                3..=u32::MAX => Ok(Resolution::NoCommand),
            },
        )
    }

    /// The menu of the typed `line` (the text up to the cursor).
    #[must_use]
    pub fn menu(&self, line: &str) -> PathMenu {
        if line.chars().count() > KEY_LINE_MAX {
            return PathMenu::Shut;
        }
        crate::bend_core::decide(
            Entry::Command,
            |w| {
                self.write_table(w);
                w.tag(1).str(line);
            },
            |r| match r.tag_of(3, "a menu tag")? {
                0 => Ok(PathMenu::Names),
                1 => {
                    let path = read_path(r)?;
                    let n = r.count()?;
                    let rows = (0..n)
                        .map(|_| {
                            let at = r.nat()?;
                            usize::try_from(at).map_err(|_| WireError::Malformed {
                                at: 0,
                                expected: "a table place",
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(PathMenu::Kids { path, rows })
                }
                // `tag_of` answered at most 2.
                2..=u32::MAX => Ok(PathMenu::Shut),
            },
        )
    }

    /// What `key` does to the typed `line` with the selected row at
    /// `place` (none when no menu row is selected).
    #[must_use]
    pub fn key(&self, line: &str, place: Option<usize>, key: PathKey) -> KeyOutcome {
        if line.chars().count() > KEY_LINE_MAX {
            return KeyOutcome {
                line: line.to_string(),
                open: false,
                submit: key == PathKey::Enter,
            };
        }
        crate::bend_core::decide(
            Entry::Command,
            |w| {
                self.write_table(w);
                w.tag(2).str(line);
                match place {
                    None => {
                        w.tag(0);
                    }
                    Some(place) => {
                        w.tag(1).count(place);
                    }
                }
                w.tag(match key {
                    PathKey::Tab => 0,
                    PathKey::Enter => 1,
                });
            },
            |r| {
                Ok(KeyOutcome {
                    line: r.str()?.to_string(),
                    open: r.bool()?,
                    submit: r.bool()?,
                })
            },
        )
    }
}

fn read_path(r: &mut Reader<'_>) -> Result<Vec<String>, WireError> {
    let n = r.count()?;
    (0..n).map(|_| r.str().map(str::to_string)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table() -> CommandTable {
        let mut arguments = HashMap::new();
        arguments.insert(
            "workflows size",
            ["small", "medium", "large"]
                .into_iter()
                .map(|size| CompletionItem {
                    value: size.to_string(),
                    label: size.to_string(),
                    description: None,
                    argument_hint: None,
                    source_tag: None,
                    path_row: None,
                })
                .collect(),
        );
        CommandTable::build(
            &crate::autocomplete::CombinedAutocompleteProvider::builtin_entries(),
            &arguments,
        )
    }

    fn path(names: &[&str]) -> Vec<String> {
        names.iter().map(ToString::to_string).collect()
    }

    /// The laws hold for a well-formed table: every name the registry
    /// sends is lowercase, has no space and is not empty.
    #[test]
    fn the_registry_table_is_well_formed() {
        let table = table();
        for row in &table.rows {
            for name in row.path.iter().chain(&row.aliases) {
                assert!(
                    !name.is_empty() && !name.contains(' ') && name.to_lowercase() == *name,
                    "{name:?} in {:?}",
                    row.path
                );
            }
        }
    }

    /// The user's bug: `/memory model` ran `/memory` with `model` as its
    /// text; it runs the subcommand, and an unknown word runs nothing.
    #[test]
    fn a_subcommand_runs_itself_never_its_parent() {
        let table = table();
        assert_eq!(
            [
                table.resolve("memory model"),
                table.resolve("memory"),
                table.resolve("memory x"),
                table.resolve("workflows size large"),
                table.resolve("goal memory  model"),
                table.resolve("nothing"),
            ],
            [
                Resolution::Runs {
                    path: path(&["memory", "model"]),
                    args: String::new()
                },
                Resolution::Runs {
                    path: path(&["memory"]),
                    args: String::new()
                },
                Resolution::Unknown {
                    path: path(&["memory"]),
                    word: "x".to_string()
                },
                Resolution::Runs {
                    path: path(&["workflows", "size", "large"]),
                    args: String::new()
                },
                Resolution::Runs {
                    path: path(&["goal"]),
                    args: "memory  model".to_string()
                },
                Resolution::NoCommand,
            ]
        );
    }

    /// Rust-encoded tables and lines read back on the Bend side: the menu
    /// below `memory` lists exactly its children, by place.
    #[test]
    fn the_menu_lists_the_children_by_place() {
        let table = table();
        let view = table.place(&path(&["memory", "view"])).unwrap();
        let model = table.place(&path(&["memory", "model"])).unwrap();
        assert_eq!(
            [
                table.menu("memory "),
                table.menu("memory MO"),
                table.menu("mem")
            ],
            [
                PathMenu::Kids {
                    path: path(&["memory"]),
                    rows: vec![view, model]
                },
                PathMenu::Kids {
                    path: path(&["memory"]),
                    rows: vec![model]
                },
                PathMenu::Names,
            ]
        );
    }
}
