//! The grammar the interpreter runs: lists of `&&`/`||` chains of
//! pipelines of simple commands (assignments, words, redirections). Any
//! other syntax is [`Unsupported`]: the script then runs whole in the
//! external shell.

/// Syntax outside the grammar, named for the reader.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Unsupported(pub &'static str);

/// One `&&`/`||` chain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AndOr {
    pub first: Pipeline,
    pub rest: Vec<(Link, Pipeline)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Link {
    /// `&&`: runs when the previous pipeline succeeded.
    And,
    /// `||`: runs when the previous pipeline failed.
    Or,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Pipeline {
    pub commands: Vec<Command>,
}

/// One simple command: a step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Command {
    pub assigns: Vec<Assign>,
    pub words: Vec<Word>,
    pub redirects: Vec<Redirect>,
}

/// `NAME=value`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Assign {
    pub name: String,
    pub value: Word,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Word {
    pub parts: Vec<Part>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Quoting {
    /// Subject to field splitting and pathname expansion.
    Bare,
    /// Inside quotes, or escaped.
    Quoted,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Part {
    Lit {
        text: String,
        quoting: Quoting,
    },
    /// `$NAME`, `${NAME}`.
    Var {
        name: String,
        quoting: Quoting,
    },
    /// `$?`.
    Status {
        quoting: Quoting,
    },
    /// A leading `~`.
    Tilde,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Redirect {
    pub fd: u32,
    pub op: RedirectOp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RedirectOp {
    /// `<`.
    Read(Word),
    /// `>`.
    Write(Word),
    /// `>>`.
    Append(Word),
    /// `>&N`: the fd goes where fd N goes.
    Dup(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WriteMode {
    Truncate,
    Append,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Word(Word),
    Newline,
    Semi,
    And,
    Or,
    Pipe,
    /// `<`, `>`, `>>` before their target word.
    Redirect {
        fd: u32,
        op: RedirectKind,
    },
    /// `>&N`.
    Dup {
        fd: u32,
        to: u32,
    },
    /// `&>`, `&>>` before their target word.
    Both(WriteMode),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RedirectKind {
    Read,
    Write(WriteMode),
}

impl RedirectKind {
    /// The redirection of `word` this kind names.
    fn op(self, word: Word) -> RedirectOp {
        match self {
            Self::Read => RedirectOp::Read(word),
            Self::Write(WriteMode::Truncate) => RedirectOp::Write(word),
            Self::Write(WriteMode::Append) => RedirectOp::Append(word),
        }
    }
}

/// Words that start syntax outside the grammar at command position.
const RESERVED: &[&str] = &[
    "if", "then", "else", "elif", "fi", "for", "while", "until", "do", "done", "case", "esac",
    "function", "select", "time", "coproc", "{", "}", "!", "[[", "]]",
];

/// Builtins whose meaning needs a real shell's state.
const SHELL_ONLY: &[&str] = &[
    "set",
    "source",
    ".",
    "eval",
    "exec",
    "trap",
    "read",
    "shift",
    "alias",
    "unalias",
    "local",
    "return",
    "declare",
    "typeset",
    "readonly",
    "let",
    "wait",
    "jobs",
    "fg",
    "bg",
    "disown",
    "getopts",
    "hash",
    "ulimit",
    "umask",
    "pushd",
    "popd",
    "dirs",
    "builtin",
    "command",
    "type",
    "enable",
    "shopt",
    "caller",
    "compgen",
    "complete",
    "history",
    "logout",
    "times",
    "suspend",
    "mapfile",
    "readarray",
    "break",
    "continue",
];

/// The script's chains, or the first syntax outside the grammar.
pub(crate) fn parse(source: &str) -> Result<Vec<AndOr>, Unsupported> {
    let tokens = lex(source)?;
    let mut at = 0;
    let mut list = Vec::new();
    loop {
        while matches!(tokens.get(at), Some(Token::Newline)) {
            at += 1;
        }
        if at == tokens.len() {
            return Ok(list);
        }
        let first = pipeline(&tokens, &mut at)?;
        let mut rest = Vec::new();
        loop {
            let link = match tokens.get(at) {
                Some(Token::And) => Link::And,
                Some(Token::Or) => Link::Or,
                Some(
                    Token::Word(_)
                    | Token::Newline
                    | Token::Semi
                    | Token::Pipe
                    | Token::Redirect { .. }
                    | Token::Dup { .. }
                    | Token::Both(_),
                )
                | None => break,
            };
            at += 1;
            while matches!(tokens.get(at), Some(Token::Newline)) {
                at += 1;
            }
            rest.push((link, pipeline(&tokens, &mut at)?));
        }
        list.push(AndOr { first, rest });
        match tokens.get(at) {
            None => return Ok(list),
            Some(Token::Semi | Token::Newline) => at += 1,
            Some(
                Token::Word(_)
                | Token::And
                | Token::Or
                | Token::Pipe
                | Token::Redirect { .. }
                | Token::Dup { .. }
                | Token::Both(_),
            ) => return Err(Unsupported("an operator in an unexpected place")),
        }
    }
}

/// The simple commands of a script outside the grammar, found without
/// running it, to name what the script as a whole may do: the script is
/// cut at every `(`, `)`, `` ` ``, `$(`, `;`, `&`, `|` and newline (not
/// inside single quotes), the reserved words that open each piece are
/// dropped, and each piece parses as a command of the grammar. A piece
/// that still does not parse gives one command of its blank-separated
/// words, quotes removed (a leading `~` stays the home directory), with
/// the words after `<`, `>` and `>>` as redirection targets. The result
/// over-approximates: a piece may be no command at all.
pub(crate) fn parts(source: &str) -> Vec<Command> {
    let mut pieces = vec![String::new()];
    let mut quoted = false;
    let mut chars = source.chars().peekable();
    while let Some(c) = chars.next() {
        let cut = match c {
            '\'' => {
                quoted = !quoted;
                false
            }
            '$' if !quoted && chars.peek() == Some(&'(') => {
                chars.next();
                true
            }
            '(' | ')' | '`' | ';' | '&' | '|' | '\n' => !quoted,
            _ => false,
        };
        if cut {
            pieces.push(String::new());
        } else if let Some(piece) = pieces.last_mut() {
            piece.push(c);
        }
    }
    let mut commands = Vec::new();
    for piece in &pieces {
        let mut words: Vec<&str> = piece.split_whitespace().collect();
        let opened = words
            .iter()
            .take_while(|word| RESERVED.contains(word))
            .count();
        words.drain(..opened);
        if words.is_empty() {
            continue;
        }
        if let Ok(list) = parse(&words.join(" ")) {
            for chain in list {
                let rest = chain.rest.into_iter().map(|(_, pipeline)| pipeline);
                for pipeline in std::iter::once(chain.first).chain(rest) {
                    commands.extend(pipeline.commands);
                }
            }
            continue;
        }
        let mut command = Command {
            assigns: Vec::new(),
            words: Vec::new(),
            redirects: Vec::new(),
        };
        let mut redirect: Option<RedirectKind> = None;
        for raw in words {
            let (kind, text) = match raw.trim_start_matches(|c: char| c.is_ascii_digit()) {
                rest if rest.starts_with(">>") => {
                    (Some(RedirectKind::Write(WriteMode::Append)), &rest[2..])
                }
                rest if rest.starts_with('>') => {
                    (Some(RedirectKind::Write(WriteMode::Truncate)), &rest[1..])
                }
                rest if rest.starts_with('<') => {
                    (Some(RedirectKind::Read), rest.trim_start_matches('<'))
                }
                _ => (None, raw),
            };
            let text: String = text.chars().filter(|&c| c != '\'' && c != '"').collect();
            let kind = kind.or(redirect.take());
            if text.is_empty() {
                redirect = kind;
                continue;
            }
            let word = match text.strip_prefix('~') {
                Some(rest) if rest.is_empty() || rest.starts_with('/') => Word {
                    parts: vec![
                        Part::Tilde,
                        Part::Lit {
                            text: rest.to_string(),
                            quoting: Quoting::Quoted,
                        },
                    ],
                },
                Some(_) | None => Word {
                    parts: vec![Part::Lit {
                        text,
                        quoting: Quoting::Quoted,
                    }],
                },
            };
            match kind {
                None => command.words.push(word),
                Some(kind) => command.redirects.push(Redirect {
                    fd: match kind {
                        RedirectKind::Read => 0,
                        RedirectKind::Write(_) => 1,
                    },
                    op: kind.op(word),
                }),
            }
        }
        if !(command.words.is_empty() && command.redirects.is_empty()) {
            commands.push(command);
        }
    }
    commands
}

fn pipeline(tokens: &[Token], at: &mut usize) -> Result<Pipeline, Unsupported> {
    let mut commands = vec![command(tokens, at)?];
    while matches!(tokens.get(*at), Some(Token::Pipe)) {
        *at += 1;
        while matches!(tokens.get(*at), Some(Token::Newline)) {
            *at += 1;
        }
        commands.push(command(tokens, at)?);
    }
    Ok(Pipeline { commands })
}

/// A redirection's target word.
fn target(tokens: &[Token], at: &mut usize) -> Result<Word, Unsupported> {
    match tokens.get(*at) {
        Some(Token::Word(word)) => {
            *at += 1;
            Ok(word.clone())
        }
        Some(
            Token::Newline
            | Token::Semi
            | Token::And
            | Token::Or
            | Token::Pipe
            | Token::Redirect { .. }
            | Token::Dup { .. }
            | Token::Both(_),
        )
        | None => Err(Unsupported("a redirection without a target")),
    }
}

fn command(tokens: &[Token], at: &mut usize) -> Result<Command, Unsupported> {
    let mut command = Command {
        assigns: Vec::new(),
        words: Vec::new(),
        redirects: Vec::new(),
    };
    loop {
        match tokens.get(*at) {
            Some(Token::Word(word)) => {
                *at += 1;
                if command.words.is_empty() {
                    if let Some(assign) = assignment(word)? {
                        command.assigns.push(assign);
                        continue;
                    }
                    if let Some(name) = bare_literal(word) {
                        if RESERVED.contains(&name) {
                            return Err(Unsupported("a compound command or reserved word"));
                        }
                        if SHELL_ONLY.contains(&name) {
                            return Err(Unsupported("a builtin that needs a full shell"));
                        }
                    }
                }
                command.words.push(word.clone());
            }
            Some(Token::Redirect { fd, op }) => {
                *at += 1;
                let word = target(tokens, at)?;
                command.redirects.push(Redirect {
                    fd: *fd,
                    op: op.op(word),
                });
            }
            Some(Token::Dup { fd, to }) => {
                *at += 1;
                command.redirects.push(Redirect {
                    fd: *fd,
                    op: RedirectOp::Dup(*to),
                });
            }
            Some(Token::Both(mode)) => {
                *at += 1;
                let word = target(tokens, at)?;
                let op = match mode {
                    WriteMode::Truncate => RedirectOp::Write(word),
                    WriteMode::Append => RedirectOp::Append(word),
                };
                command.redirects.push(Redirect { fd: 1, op });
                command.redirects.push(Redirect {
                    fd: 2,
                    op: RedirectOp::Dup(1),
                });
            }
            Some(Token::Newline | Token::Semi | Token::And | Token::Or | Token::Pipe) | None => {
                break;
            }
        }
    }
    if command.assigns.is_empty() && command.words.is_empty() && command.redirects.is_empty() {
        return Err(Unsupported("an empty command"));
    }
    Ok(command)
}

/// The word's text when it is one unquoted literal.
pub(crate) fn bare_literal(word: &Word) -> Option<&str> {
    match word.parts.as_slice() {
        [Part::Lit {
            text,
            quoting: Quoting::Bare,
        }] => Some(text),
        _ => None,
    }
}

fn is_name(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// `NAME=value` when the word starts with an unquoted `NAME=`.
fn assignment(word: &Word) -> Result<Option<Assign>, Unsupported> {
    let Some(Part::Lit {
        text,
        quoting: Quoting::Bare,
    }) = word.parts.first()
    else {
        return Ok(None);
    };
    let Some((name, value)) = text.split_once('=') else {
        return Ok(None);
    };
    if name.ends_with('+') && is_name(&name[..name.len() - 1]) {
        return Err(Unsupported("an appending assignment (`+=`)"));
    }
    if !is_name(name) {
        return Ok(None);
    }
    let mut parts = Vec::with_capacity(word.parts.len());
    if !value.is_empty() {
        parts.push(Part::Lit {
            text: value.to_string(),
            quoting: Quoting::Bare,
        });
    }
    parts.extend(word.parts[1..].iter().cloned());
    Ok(Some(Assign {
        name: name.to_string(),
        value: Word { parts },
    }))
}

/// Append text to the word being built, merging with its last literal.
fn push_text(word: &mut Option<Word>, text: &str, quoting: Quoting) {
    let word = word.get_or_insert_with(Word::default);
    if let Some(Part::Lit {
        text: last,
        quoting: last_quoting,
    }) = word.parts.last_mut()
    {
        if *last_quoting == quoting {
            last.push_str(text);
            return;
        }
    }
    word.parts.push(Part::Lit {
        text: text.to_string(),
        quoting,
    });
}

fn flush(word: &mut Option<Word>, tokens: &mut Vec<Token>) {
    if let Some(word) = word.take() {
        tokens.push(Token::Word(word));
    }
}

/// A `$` at `chars[*at]`: a parameter, or a literal `$`.
fn dollar(
    chars: &[char],
    at: &mut usize,
    word: &mut Option<Word>,
    quoting: Quoting,
) -> Result<(), Unsupported> {
    let next = chars.get(*at + 1).copied();
    match next {
        Some('(') => Err(Unsupported("command substitution (`$(`)")),
        Some('\'') => Err(Unsupported("ANSI-C quoting (`$'`)")),
        Some('"') => Err(Unsupported("locale quoting (`$\"`)")),
        Some('?') => {
            *at += 2;
            word.get_or_insert_with(Word::default)
                .parts
                .push(Part::Status { quoting });
            Ok(())
        }
        Some('{') => {
            let start = *at + 2;
            let Some(len) = chars[start..].iter().position(|&c| c == '}') else {
                return Err(Unsupported("an unterminated `${`"));
            };
            let name: String = chars[start..start + len].iter().collect();
            if !is_name(&name) {
                return Err(Unsupported("a parameter expansion other than `${NAME}`"));
            }
            *at = start + len + 1;
            word.get_or_insert_with(Word::default)
                .parts
                .push(Part::Var { name, quoting });
            Ok(())
        }
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {
            let start = *at + 1;
            let len = chars[start..]
                .iter()
                .position(|&c| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(chars.len() - start);
            let name: String = chars[start..start + len].iter().collect();
            *at = start + len;
            word.get_or_insert_with(Word::default)
                .parts
                .push(Part::Var { name, quoting });
            Ok(())
        }
        Some(c) if c.is_ascii_digit() || matches!(c, '@' | '*' | '#' | '$' | '!' | '-') => {
            Err(Unsupported("a special or positional parameter"))
        }
        _ => {
            *at += 1;
            push_text(word, "$", quoting);
            Ok(())
        }
    }
}

/// The digits of the word being built when it is a bare number: the fd
/// of the redirection that follows it.
fn take_fd(word: &mut Option<Word>) -> Option<u32> {
    let fd = word
        .as_ref()
        .and_then(bare_literal)
        .filter(|text| text.chars().all(|c| c.is_ascii_digit()))
        .and_then(|text| text.parse().ok())?;
    *word = None;
    Some(fd)
}

/// Characters that end an unquoted word.
fn ends_word(c: char) -> bool {
    matches!(
        c,
        ' ' | '\t' | '\n' | ';' | '&' | '|' | '<' | '>' | '(' | ')'
    )
}

#[allow(clippy::too_many_lines)] // One scanner over the whole token grammar reads best in one place.
fn lex(source: &str) -> Result<Vec<Token>, Unsupported> {
    let chars: Vec<char> = source.chars().collect();
    let mut tokens = Vec::new();
    let mut word: Option<Word> = None;
    let mut at = 0;
    while let Some(&c) = chars.get(at) {
        let next = chars.get(at + 1).copied();
        match c {
            ' ' | '\t' => {
                flush(&mut word, &mut tokens);
                at += 1;
            }
            '\n' => {
                flush(&mut word, &mut tokens);
                tokens.push(Token::Newline);
                at += 1;
            }
            '#' if word.is_none() => {
                while chars.get(at).is_some_and(|&c| c != '\n') {
                    at += 1;
                }
            }
            ';' => {
                if next == Some(';') {
                    return Err(Unsupported("a `;;` outside `case`"));
                }
                flush(&mut word, &mut tokens);
                tokens.push(Token::Semi);
                at += 1;
            }
            '&' => {
                flush(&mut word, &mut tokens);
                match next {
                    Some('&') => {
                        tokens.push(Token::And);
                        at += 2;
                    }
                    Some('>') if chars.get(at + 2) == Some(&'>') => {
                        tokens.push(Token::Both(WriteMode::Append));
                        at += 3;
                    }
                    Some('>') => {
                        tokens.push(Token::Both(WriteMode::Truncate));
                        at += 2;
                    }
                    _ => return Err(Unsupported("a background job (`&`)")),
                }
            }
            '|' => {
                flush(&mut word, &mut tokens);
                match next {
                    Some('|') => {
                        tokens.push(Token::Or);
                        at += 2;
                    }
                    Some('&') => return Err(Unsupported("a `|&` pipe")),
                    _ => {
                        tokens.push(Token::Pipe);
                        at += 1;
                    }
                }
            }
            '<' | '>' => {
                let fd = take_fd(&mut word);
                flush(&mut word, &mut tokens);
                let fd = fd.unwrap_or(u32::from(c == '>'));
                if fd > 2 {
                    return Err(Unsupported("a file descriptor above 2"));
                }
                if c == '<' {
                    match next {
                        Some('<') => return Err(Unsupported("a here-document (`<<`)")),
                        Some('(') => return Err(Unsupported("process substitution (`<(`)")),
                        Some('>' | '&') => return Err(Unsupported("a `<>` or `<&` redirection")),
                        _ => {
                            tokens.push(Token::Redirect {
                                fd,
                                op: RedirectKind::Read,
                            });
                            at += 1;
                        }
                    }
                } else {
                    match next {
                        Some('>') => {
                            tokens.push(Token::Redirect {
                                fd,
                                op: RedirectKind::Write(WriteMode::Append),
                            });
                            at += 2;
                        }
                        Some('&') => match chars.get(at + 2) {
                            Some(&to @ ('0' | '1' | '2'))
                                if chars.get(at + 3).is_none_or(|&c| ends_word(c)) =>
                            {
                                tokens.push(Token::Dup {
                                    fd,
                                    to: to.to_digit(10).unwrap_or(1),
                                });
                                at += 3;
                            }
                            _ => return Err(Unsupported("a `>&` other than `>&0`, `>&1`, `>&2`")),
                        },
                        Some('(') => return Err(Unsupported("process substitution (`>(`)")),
                        Some('|') => {
                            tokens.push(Token::Redirect {
                                fd,
                                op: RedirectKind::Write(WriteMode::Truncate),
                            });
                            at += 2;
                        }
                        _ => {
                            tokens.push(Token::Redirect {
                                fd,
                                op: RedirectKind::Write(WriteMode::Truncate),
                            });
                            at += 1;
                        }
                    }
                }
            }
            '(' | ')' => return Err(Unsupported("a subshell or group (`(`)")),
            '`' => return Err(Unsupported("command substitution (`` ` ``)")),
            '\'' => {
                let start = at + 1;
                let Some(len) = chars[start..].iter().position(|&c| c == '\'') else {
                    return Err(Unsupported("an unterminated quote"));
                };
                let text: String = chars[start..start + len].iter().collect();
                push_text(&mut word, &text, Quoting::Quoted);
                at = start + len + 1;
            }
            '"' => {
                at += 1;
                // An empty `""` is still a word.
                push_text(&mut word, "", Quoting::Quoted);
                loop {
                    match chars.get(at).copied() {
                        None => return Err(Unsupported("an unterminated quote")),
                        Some('"') => {
                            at += 1;
                            break;
                        }
                        Some('`') => return Err(Unsupported("command substitution (`` ` ``)")),
                        Some('$') => dollar(&chars, &mut at, &mut word, Quoting::Quoted)?,
                        Some('\\') => match chars.get(at + 1).copied() {
                            Some('\n') => at += 2,
                            Some(escaped @ ('$' | '`' | '"' | '\\')) => {
                                push_text(&mut word, &escaped.to_string(), Quoting::Quoted);
                                at += 2;
                            }
                            _ => {
                                push_text(&mut word, "\\", Quoting::Quoted);
                                at += 1;
                            }
                        },
                        Some(c) => {
                            push_text(&mut word, &c.to_string(), Quoting::Quoted);
                            at += 1;
                        }
                    }
                }
            }
            '\\' => match next {
                Some('\n') => at += 2,
                Some(escaped) => {
                    push_text(&mut word, &escaped.to_string(), Quoting::Quoted);
                    at += 2;
                }
                None => {
                    push_text(&mut word, "\\", Quoting::Bare);
                    at += 1;
                }
            },
            '$' => dollar(&chars, &mut at, &mut word, Quoting::Bare)?,
            '~' if word.is_none() && next.is_none_or(|c| c == '/' || ends_word(c)) => {
                word.get_or_insert_with(Word::default)
                    .parts
                    .push(Part::Tilde);
                at += 1;
            }
            '{' => {
                let rest: String = chars[at + 1..]
                    .iter()
                    .take_while(|&&c| !ends_word(c) && c != '\'' && c != '"')
                    .collect();
                if let Some(inner) = rest.split('}').next().filter(|_| rest.contains('}')) {
                    if inner.contains(',') || inner.contains("..") {
                        return Err(Unsupported("brace expansion"));
                    }
                }
                push_text(&mut word, "{", Quoting::Bare);
                at += 1;
            }
            c => {
                push_text(&mut word, &c.to_string(), Quoting::Bare);
                at += 1;
            }
        }
    }
    flush(&mut word, &mut tokens);
    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(text: &str) -> Part {
        Part::Lit {
            text: text.to_string(),
            quoting: Quoting::Bare,
        }
    }

    fn quoted(text: &str) -> Part {
        Part::Lit {
            text: text.to_string(),
            quoting: Quoting::Quoted,
        }
    }

    fn word(parts: Vec<Part>) -> Word {
        Word { parts }
    }

    fn simple(words: Vec<Word>, redirects: Vec<Redirect>) -> Command {
        Command {
            assigns: Vec::new(),
            words,
            redirects,
        }
    }

    #[test]
    fn a_script_parses_into_chains_of_pipelines() {
        let parsed =
            parse("X=1 cat 'a b'\"$X\" < in | grep -n x 2>&1 >> out && ls ~/d || echo $?; pwd")
                .unwrap();
        assert_eq!(
            parsed,
            vec![
                AndOr {
                    first: Pipeline {
                        commands: vec![
                            Command {
                                assigns: vec![Assign {
                                    name: "X".to_string(),
                                    value: word(vec![lit("1")]),
                                }],
                                words: vec![
                                    word(vec![lit("cat")]),
                                    word(vec![
                                        quoted("a b"),
                                        Part::Var {
                                            name: "X".to_string(),
                                            quoting: Quoting::Quoted,
                                        },
                                    ]),
                                ],
                                redirects: vec![Redirect {
                                    fd: 0,
                                    op: RedirectOp::Read(word(vec![lit("in")])),
                                }],
                            },
                            simple(
                                vec![
                                    word(vec![lit("grep")]),
                                    word(vec![lit("-n")]),
                                    word(vec![lit("x")])
                                ],
                                vec![
                                    Redirect {
                                        fd: 2,
                                        op: RedirectOp::Dup(1),
                                    },
                                    Redirect {
                                        fd: 1,
                                        op: RedirectOp::Append(word(vec![lit("out")])),
                                    },
                                ],
                            ),
                        ],
                    },
                    rest: vec![
                        (
                            Link::And,
                            Pipeline {
                                commands: vec![simple(
                                    vec![word(vec![lit("ls")]), word(vec![Part::Tilde, lit("/d")])],
                                    Vec::new(),
                                )],
                            },
                        ),
                        (
                            Link::Or,
                            Pipeline {
                                commands: vec![simple(
                                    vec![
                                        word(vec![lit("echo")]),
                                        word(vec![Part::Status {
                                            quoting: Quoting::Bare,
                                        }]),
                                    ],
                                    Vec::new(),
                                )],
                            },
                        ),
                    ],
                },
                AndOr {
                    first: Pipeline {
                        commands: vec![simple(vec![word(vec![lit("pwd")])], Vec::new())],
                    },
                    rest: Vec::new(),
                },
            ]
        );
    }

    #[test]
    fn syntax_outside_the_grammar_is_named() {
        let cases = [
            (
                "for f in *; do echo $f; done",
                "a compound command or reserved word",
            ),
            ("echo $(date)", "command substitution (`$(`)"),
            ("sleep 1 &", "a background job (`&`)"),
            ("cat <<EOF\nx\nEOF", "a here-document (`<<`)"),
            ("(cd /; ls)", "a subshell or group (`(`)"),
            ("set -e", "a builtin that needs a full shell"),
            ("echo {a,b}", "brace expansion"),
            ("echo 'open", "an unterminated quote"),
            ("echo ${X:-y}", "a parameter expansion other than `${NAME}`"),
            ("ls &&", "an empty command"),
        ];
        let got: Vec<_> = cases
            .iter()
            .map(|(script, _)| parse(script).map(|_| ()))
            .collect();
        let want: Vec<_> = cases
            .iter()
            .map(|&(_, why)| Err(Unsupported(why)))
            .collect();
        assert_eq!(got, want);
    }

    #[test]
    fn comments_continuations_and_find_braces_stay_in_the_grammar() {
        let parsed = parse("# note\nfind . -exec rm {} \\; # gone\\\nls").unwrap();
        assert_eq!(
            parsed,
            vec![
                AndOr {
                    first: Pipeline {
                        commands: vec![simple(
                            vec![
                                word(vec![lit("find")]),
                                word(vec![lit(".")]),
                                word(vec![lit("-exec")]),
                                word(vec![lit("rm")]),
                                word(vec![lit("{}")]),
                                word(vec![quoted(";")]),
                            ],
                            Vec::new(),
                        )],
                    },
                    rest: Vec::new(),
                },
                AndOr {
                    first: Pipeline {
                        commands: vec![simple(vec![word(vec![lit("ls")])], Vec::new())],
                    },
                    rest: Vec::new(),
                },
            ]
        );
    }

    #[test]
    fn a_script_outside_the_grammar_gives_every_command_it_holds() {
        let got =
            parts("if grep -q x f; then (cat ~/.ssh/k > out.txt); fi; echo \"$(curl u)\" ${X:-y}");
        assert_eq!(
            got,
            vec![
                simple(
                    vec![
                        word(vec![lit("grep")]),
                        word(vec![lit("-q")]),
                        word(vec![lit("x")]),
                        word(vec![lit("f")]),
                    ],
                    Vec::new(),
                ),
                simple(
                    vec![
                        word(vec![lit("cat")]),
                        word(vec![Part::Tilde, lit("/.ssh/k")])
                    ],
                    vec![Redirect {
                        fd: 1,
                        op: RedirectOp::Write(word(vec![lit("out.txt")])),
                    }],
                ),
                simple(vec![word(vec![quoted("echo")])], Vec::new()),
                simple(
                    vec![word(vec![lit("curl")]), word(vec![lit("u")])],
                    Vec::new()
                ),
                simple(vec![word(vec![quoted("${X:-y}")])], Vec::new()),
            ]
        );
    }
}
