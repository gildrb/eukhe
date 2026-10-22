//! The console-variable command language (docs/control.md S4,
//! `bend/cvar.bend`): the lines of a `.cfg` file, the `/set` slash command
//! family, and the commands a key bind runs.
//!
//! A script is lines. A line that starts with `#` or `//` is a comment.
//! Each line is a command list: commands separated by `;` outside quotes.
//! A command is words separated by whitespace; a word in double quotes
//! keeps its spaces and `;`, with the escapes `\"` and `\\`.
//!
//! ```text
//! set <id> <value>        set a cvar
//! toggle <id>             flip a Bool cvar
//! alias <name> "<cmds>"   name a command list
//! bind <key> "<cmds>"     the commands a press of <key> runs
//! action <id>             a built-in client action
//! <name>                  run the alias <name>
//! ```
//!
//! The expansion of runs of aliases (`eukhe_bend::rules::cvar`, the model
//! `bend/cvar.bend` compiled) replaces each run of an alias with its
//! commands. It nests at most one level per alias of the table: a deeper
//! nest repeats an alias, so it is a cycle ([`ExpandError::Cycle`]). A run
//! of an alias that does not exist is [`ExpandError::Unknown`].

use std::fmt;

/// One command of the language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command {
    /// `set <id> <value>`: the value as written; the cvar's type reads it.
    Set { id: String, value: String },
    /// `toggle <id>`: flip a Bool cvar.
    Toggle { id: String },
    /// `alias <name> "<cmds>"`: define (or redefine) an alias.
    Alias { name: String, body: Vec<Command> },
    /// `bind <key> "<cmds>"`: the commands a press of `key` runs.
    Bind { key: String, body: Vec<Command> },
    /// `action <id>`: a built-in client action (for example a key bind's
    /// `app.interrupt`).
    Action { id: String },
    /// `<name>`: run the alias `name`.
    Run { alias: String },
}

/// What is wrong with a command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseErrorKind {
    /// A `"` with no closing `"`.
    UnclosedQuote,
    /// A command without one of its words (`set` without a value).
    Missing {
        command: &'static str,
        word: &'static str,
    },
    /// A word after the last word of a command.
    Extra { command: String, word: String },
}

/// A command that does not parse, with its line (from 1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub kind: ParseErrorKind,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let line = self.line;
        match &self.kind {
            ParseErrorKind::UnclosedQuote => write!(f, "line {line}: a quote is not closed"),
            ParseErrorKind::Missing { command, word } => {
                write!(f, "line {line}: `{command}` needs a {word}")
            }
            ParseErrorKind::Extra { command, word } => {
                write!(f, "line {line}: `{command}` does not take `{word}`")
            }
        }
    }
}

impl std::error::Error for ParseError {}

/// One word of a command list, or the `;` that ends a command.
enum Token {
    Word(String),
    End,
}

/// The words and command ends of one line.
fn tokens(line: &str) -> Result<Vec<Token>, ParseErrorKind> {
    let mut out = Vec::new();
    let mut chars = line.chars().peekable();
    while let Some(&c) = chars.peek() {
        if c == ';' {
            chars.next();
            out.push(Token::End);
        } else if c.is_whitespace() {
            chars.next();
        } else if c == '"' {
            chars.next();
            let mut word = String::new();
            loop {
                match chars.next() {
                    None => return Err(ParseErrorKind::UnclosedQuote),
                    Some('"') => break,
                    Some('\\') => match chars.next() {
                        Some(escaped @ ('"' | '\\')) => word.push(escaped),
                        Some(other) => {
                            word.push('\\');
                            word.push(other);
                        }
                        None => return Err(ParseErrorKind::UnclosedQuote),
                    },
                    Some(other) => word.push(other),
                }
            }
            out.push(Token::Word(word));
        } else {
            let mut word = String::new();
            while let Some(&c) = chars.peek() {
                if c.is_whitespace() || c == ';' || c == '"' {
                    break;
                }
                word.push(c);
                chars.next();
            }
            out.push(Token::Word(word));
        }
    }
    Ok(out)
}

/// The command of one `;`-separated group of words.
fn command(words: Vec<String>) -> Result<Command, ParseErrorKind> {
    let mut words = words.into_iter();
    let Some(head) = words.next() else {
        return Err(ParseErrorKind::Missing {
            command: "",
            word: "command",
        });
    };
    let mut take = |command: &'static str, word: &'static str| {
        words
            .next()
            .ok_or(ParseErrorKind::Missing { command, word })
    };
    let parsed = match head.as_str() {
        "set" => Command::Set {
            id: take("set", "cvar id")?,
            value: take("set", "value")?,
        },
        "toggle" => Command::Toggle {
            id: take("toggle", "cvar id")?,
        },
        "alias" => Command::Alias {
            name: take("alias", "name")?,
            body: parse_list(&take("alias", "command list")?)?,
        },
        "bind" => Command::Bind {
            key: take("bind", "key")?,
            body: parse_list(&take("bind", "command list")?)?,
        },
        "action" => Command::Action {
            id: take("action", "action id")?,
        },
        _ => Command::Run {
            alias: head.clone(),
        },
    };
    match words.next() {
        Some(word) => Err(ParseErrorKind::Extra {
            command: head,
            word,
        }),
        None => Ok(parsed),
    }
}

/// The commands of one command list (one line, or the quoted body of an
/// `alias` or a `bind`). Empty commands (`;;`) are skipped.
///
/// # Errors
///
/// An unclosed quote, a command without one of its words, or a word too
/// many.
pub fn parse_list(text: &str) -> Result<Vec<Command>, ParseErrorKind> {
    let mut commands = Vec::new();
    let mut words = Vec::new();
    for token in tokens(text)? {
        match token {
            Token::Word(word) => words.push(word),
            Token::End => {
                if !words.is_empty() {
                    commands.push(command(std::mem::take(&mut words))?);
                }
            }
        }
    }
    if !words.is_empty() {
        commands.push(command(words)?);
    }
    Ok(commands)
}

/// The commands of a script (a `.cfg` file), in order, and the lines that
/// do not parse. A bad line is skipped; the other lines still apply.
#[must_use]
pub fn parse_script(text: &str) -> (Vec<Command>, Vec<ParseError>) {
    let mut commands = Vec::new();
    let mut errors = Vec::new();
    for (at, line) in text.lines().enumerate() {
        let trimmed = line.trim_start();
        if trimmed.starts_with('#') || trimmed.starts_with("//") {
            continue;
        }
        match parse_list(line) {
            Ok(parsed) => commands.extend(parsed),
            Err(kind) => errors.push(ParseError { line: at + 1, kind }),
        }
    }
    (commands, errors)
}

/// A word as the language reads it back: quoted when it holds a space, a
/// `;`, a quote or a backslash, or is empty.
fn word(text: &str) -> String {
    if !text.is_empty()
        && !text
            .chars()
            .any(|c| c.is_whitespace() || matches!(c, ';' | '"' | '\\'))
    {
        return text.to_string();
    }
    let mut quoted = String::with_capacity(text.len() + 2);
    quoted.push('"');
    for c in text.chars() {
        if matches!(c, '"' | '\\') {
            quoted.push('\\');
        }
        quoted.push(c);
    }
    quoted.push('"');
    quoted
}

/// A command list as one line of the language (`;`-separated).
#[must_use]
pub fn render_list(commands: &[Command]) -> String {
    commands
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("; ")
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Command::Set { id, value } => write!(f, "set {} {}", word(id), word(value)),
            Command::Toggle { id } => write!(f, "toggle {}", word(id)),
            Command::Alias { name, body } => {
                write!(f, "alias {} {}", word(name), word(&render_list(body)))
            }
            Command::Bind { key, body } => {
                write!(f, "bind {} {}", word(key), word(&render_list(body)))
            }
            Command::Action { id } => write!(f, "action {}", word(id)),
            Command::Run { alias } => f.write_str(&word(alias)),
        }
    }
}

/// The alias table: each name once, in the order first defined.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Aliases(Vec<(String, Vec<Command>)>);

impl Aliases {
    /// Define `name`; a redefinition replaces the body in place.
    pub fn define(&mut self, name: String, body: Vec<Command>) {
        match self.0.iter_mut().find(|(known, _)| *known == name) {
            Some((_, old)) => *old = body,
            None => self.0.push((name, body)),
        }
    }

    /// The commands of alias `name`.
    #[must_use]
    pub fn body(&self, name: &str) -> Option<&[Command]> {
        self.0
            .iter()
            .find(|(known, _)| known == name)
            .map(|(_, body)| body.as_slice())
    }

    /// The aliases, in the order first defined.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &[Command])> {
        self.0
            .iter()
            .map(|(name, body)| (name.as_str(), body.as_slice()))
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// Why an expansion stopped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpandError {
    /// The expansion nested deeper than the table has aliases: an alias
    /// runs itself, at most through other aliases. `alias` is the run at
    /// which the depth ran out.
    Cycle { alias: String },
    /// A run of an alias that does not exist.
    Unknown { alias: String },
}

impl fmt::Display for ExpandError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpandError::Cycle { alias } => write!(f, "alias `{alias}` runs itself (a cycle)"),
            ExpandError::Unknown { alias } => write!(f, "no alias `{alias}`"),
        }
    }
}

impl std::error::Error for ExpandError {}

/// The key binds, in order: the first bind of a key wins.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Binds(Vec<(String, Vec<Command>)>);

impl Binds {
    /// Add a bind after the others (a key bound before keeps its first
    /// bind).
    pub fn push(&mut self, key: String, body: Vec<Command>) {
        self.0.push((key, body));
    }

    /// The binds, in order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &[Command])> {
        self.0
            .iter()
            .map(|(key, body)| (key.as_str(), body.as_slice()))
    }
}

#[cfg(test)]
mod tests;
