//! What follows a slash command's path: the words, options and live
//! values its handler reads (`/budget set cost= time=`, `/accept cmd`,
//! `/effects ran <id>`, `/loop 7 --until`), and the menu of a typed
//! argument text over them. The command table (`slash_commands`) names
//! the paths; this table names their argument text. Completion only: the
//! handlers parse their text themselves.

/// The argument text below one place: a command path, or a word of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Grammar {
    /// The words the text may open with, each with the text after it.
    pub words: &'static [Word],
    /// The options the text may hold, each once, before its free text.
    pub options: &'static [Opt],
    /// The value that comes before the options (`/loop 7 --until`,
    /// `/force bash --tries 2`).
    pub lead: Lead,
    /// The interface's live values the text may open with.
    pub live: Option<LiveValues>,
    /// What the text holds, shown when nothing is offered.
    pub usage: Option<&'static str>,
}

/// One word that may open the text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Word {
    pub name: &'static str,
    pub description: &'static str,
    /// The text after the word.
    pub then: &'static Grammar,
}

/// One option: a flag (`--stop`), a flag with the next token as its
/// value (`--until <cmd>`), or a key with its value attached (`cost=`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Opt {
    pub name: &'static str,
    pub description: &'static str,
    /// The value it takes; none for a flag.
    pub value: Option<&'static str>,
}

/// The value before a text's options.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lead {
    /// The options come first.
    None,
    /// One value may come before them (`/loop 7 --until`).
    Optional,
    /// One value comes before them (`/force bash --tries 2`).
    Required,
}

impl Lead {
    /// The fewest values before the options.
    fn least(self) -> usize {
        match self {
            Lead::None | Lead::Optional => 0,
            Lead::Required => 1,
        }
    }

    /// The most values before the options.
    fn most(self) -> usize {
        match self {
            Lead::None => 0,
            Lead::Optional | Lead::Required => 1,
        }
    }
}

/// The live values an interface supplies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LiveValues {
    /// The ids of the session's steps treated as not run that nobody
    /// corrected.
    OpenEffects,
}

/// One menu row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Row {
    Word(&'static Word),
    Opt(&'static Opt),
    /// The live values matching the token (the interface filters them).
    Live(LiveValues),
}

/// The menu of a typed argument text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgumentMenu<'a> {
    /// The token at the cursor: what a completion replaces.
    pub token: &'a str,
    pub rows: Vec<Row>,
    /// What the cursor's place expects, when no row is offered.
    pub hint: Option<&'static str>,
}

impl Opt {
    /// The key form (`cost=`): its value is in the same token.
    #[must_use]
    pub fn is_key(&self) -> bool {
        self.name.ends_with('=')
    }

    fn names(&self, token: &str) -> bool {
        if self.is_key() {
            token.starts_with(self.name)
        } else {
            token == self.name
        }
    }

    /// The flag takes the next token as its value.
    fn takes_next(&self) -> bool {
        !self.is_key() && self.value.is_some()
    }
}

/// `name` starts with the typed `token`, in any ASCII case: a row the
/// token may complete to.
#[must_use]
pub fn starts(name: &str, token: &str) -> bool {
    name.get(..token.len())
        .is_some_and(|head| head.eq_ignore_ascii_case(token))
}

/// The text split into its completed tokens and the token at its end
/// (empty after whitespace; none inside an open quote). A quoted run is
/// one token (`--until 'bun test'`).
fn tokens(text: &str) -> (Vec<&str>, Option<&str>) {
    enum At {
        Gap,
        Token(usize),
        Quote(usize, char),
    }
    let mut done = Vec::new();
    let mut at = At::Gap;
    for (i, c) in text.char_indices() {
        at = match at {
            At::Gap if c.is_whitespace() => At::Gap,
            At::Gap if c == '\'' || c == '"' => At::Quote(i, c),
            At::Gap => At::Token(i),
            At::Token(start) if c.is_whitespace() => {
                done.push(&text[start..i]);
                At::Gap
            }
            At::Token(start) => At::Token(start),
            At::Quote(start, quote) if c == quote => At::Token(start),
            At::Quote(start, quote) => At::Quote(start, quote),
        };
    }
    let last = match at {
        At::Gap => Some(""),
        At::Token(start) => Some(&text[start..]),
        At::Quote(..) => None,
    };
    (done, last)
}

/// Where the completed tokens left the text.
#[derive(Debug, Clone)]
struct Place {
    grammar: &'static Grammar,
    used: Vec<&'static str>,
    /// The tokens of free text so far.
    values: usize,
    /// The flag whose value is the next token.
    awaiting: Option<&'static Opt>,
}

impl Place {
    fn new(grammar: &'static Grammar) -> Place {
        Place {
            grammar,
            used: Vec::new(),
            values: 0,
            awaiting: None,
        }
    }

    fn step(self, token: &str) -> Place {
        if self.awaiting.is_some() {
            return Place {
                awaiting: None,
                ..self
            };
        }
        let free = self.values > self.grammar.lead.most();
        if !free {
            if let Some(opt) = self.grammar.options.iter().find(|opt| opt.names(token)) {
                let mut used = self.used;
                used.push(opt.name);
                return Place {
                    used,
                    awaiting: opt.takes_next().then_some(opt),
                    ..self
                };
            }
        }
        if self.values == 0 {
            if let Some(word) = self
                .grammar
                .words
                .iter()
                .find(|word| word.name.eq_ignore_ascii_case(token))
            {
                return Place::new(word.then);
            }
        }
        Place {
            values: self.values + 1,
            ..self
        }
    }

    fn menu(self, token: &str) -> (Vec<Row>, Option<&'static str>) {
        if let Some(opt) = self.awaiting {
            return (Vec::new(), opt.value.filter(|_| token.is_empty()));
        }
        if let Some(opt) = self
            .grammar
            .options
            .iter()
            .find(|opt| opt.is_key() && opt.names(token))
        {
            return (Vec::new(), opt.value.filter(|_| token == opt.name));
        }
        let free = self.values > self.grammar.lead.most();
        if free {
            return (Vec::new(), None);
        }
        let early = self.values < self.grammar.lead.least();
        let first = self.values == 0;
        let words = self
            .grammar
            .words
            .iter()
            .filter(|word| first && starts(word.name, token))
            .map(Row::Word);
        let live = self.grammar.live.filter(|_| first).map(Row::Live);
        let options = self
            .grammar
            .options
            .iter()
            .filter(|opt| !early && !self.used.contains(&opt.name) && starts(opt.name, token))
            .map(Row::Opt);
        let rows: Vec<Row> = words.chain(live).chain(options).collect();
        let hint = self
            .grammar
            .usage
            .filter(|_| rows.is_empty() && token.is_empty() && first);
        (rows, hint)
    }
}

/// The menu of `text`, the argument text up to the cursor below a place
/// of `grammar`.
#[must_use]
pub fn menu<'a>(grammar: &'static Grammar, text: &'a str) -> ArgumentMenu<'a> {
    let (done, last) = tokens(text);
    let Some(token) = last else {
        return ArgumentMenu {
            token: "",
            rows: Vec::new(),
            hint: None,
        };
    };
    let place = done.into_iter().fold(Place::new(grammar), Place::step);
    let (rows, hint) = place.menu(token);
    ArgumentMenu { token, rows, hint }
}

/// The argument text of a command path (its names with one space
/// between: `"budget"`, `"effects ran"`).
#[must_use]
pub fn grammar(path: &str) -> Option<&'static Grammar> {
    GRAMMARS
        .iter()
        .find(|(at, _)| *at == path)
        .map(|(_, grammar)| *grammar)
}

/// Every path with an argument text, for the table's own checks.
pub fn paths() -> impl Iterator<Item = &'static str> {
    GRAMMARS.iter().map(|(path, _)| *path)
}

const fn text(usage: &'static str) -> Grammar {
    Grammar {
        words: &[],
        options: &[],
        lead: Lead::None,
        live: None,
        usage: Some(usage),
    }
}

const fn word(name: &'static str, description: &'static str, then: &'static Grammar) -> Word {
    Word {
        name,
        description,
        then,
    }
}

const fn flag(name: &'static str, description: &'static str) -> Opt {
    Opt {
        name,
        description,
        value: None,
    }
}

const fn opt(name: &'static str, value: &'static str, description: &'static str) -> Opt {
    Opt {
        name,
        description,
        value: Some(value),
    }
}

const fn words(words: &'static [Word]) -> Grammar {
    Grammar {
        words,
        options: &[],
        lead: Lead::None,
        live: None,
        usage: None,
    }
}

const NOTHING: Grammar = Grammar {
    words: &[],
    options: &[],
    lead: Lead::None,
    live: None,
    usage: None,
};

const ON_OFF: Grammar = words(&[
    word("on", "Turn it on", &NOTHING),
    word("off", "Turn it off", &NOTHING),
]);

const BUDGET_AMOUNTS: Grammar = Grammar {
    words: &[],
    options: &[
        opt("cost=", "<dollars>", "Money: 1.50 or $1.50"),
        opt("tokens=", "<n>", "Tokens: 200000, 200k, 1.5m"),
        opt("time=", "<duration>", "Work time: 90s, 10m, 2h"),
        opt("calls=", "<n>", "Tool calls"),
        opt("requests=", "<n>", "Model requests"),
    ],
    lead: Lead::None,
    live: None,
    usage: Some("cost= tokens= time= calls= requests="),
};

const BUDGET: Grammar = words(&[
    word("set", "Give the session a budget", &BUDGET_AMOUNTS),
    word("add", "Add to the session's budget", &BUDGET_AMOUNTS),
    word("audit", "Replay the budget ledger", &NOTHING),
    word("on", "Enforce the budget's limits", &NOTHING),
    word("off", "Stop enforcing the budget's limits", &NOTHING),
]);

const ACCEPT_TIMEOUT: Opt = opt("--timeout", "<seconds>", "The check's time limit");

const ACCEPT: Grammar = words(&[
    word("status", "Show the checks and their verdicts", &NOTHING),
    word(
        "cmd",
        "Add a command that must exit with the expected code",
        &Grammar {
            words: &[],
            options: &[
                opt(
                    "--expect",
                    "<code>",
                    "The exit code that passes (default 0)",
                ),
                ACCEPT_TIMEOUT,
                opt(
                    "--protect",
                    "<path>",
                    "A path the work must leave unchanged",
                ),
            ],
            lead: Lead::None,
            live: None,
            usage: Some("<command>"),
        },
    ),
    word(
        "judge",
        "Add a condition a model judge checks",
        &Grammar {
            words: &[],
            options: &[opt("--model", "<provider/id>", "The judge's model")],
            lead: Lead::None,
            live: None,
            usage: Some("<condition>"),
        },
    ),
    word(
        "until",
        "Add a command that exits 0 once the condition holds",
        &Grammar {
            words: &[],
            options: &[ACCEPT_TIMEOUT],
            lead: Lead::None,
            live: None,
            usage: Some("<command>"),
        },
    ),
    word(
        "intent",
        "Turn the intent judge on or off (judges your messages on the final state)",
        &ON_OFF,
    ),
    word(
        "returns",
        "The most returns in a row to the agent",
        &text("<n>"),
    ),
    word("clear", "Drop every check", &NOTHING),
]);

const LOOP_CONDITION: &str = "'<command>'|<condition in words>";

const LOOP: Grammar = Grammar {
    words: &[],
    options: &[
        opt(
            "--until",
            LOOP_CONDITION,
            "Stop once the command exits 0 (quoted) or the condition holds (words)",
        ),
        opt(
            "--while",
            LOOP_CONDITION,
            "Go on while the command exits 0 (quoted) or the condition holds (words)",
        ),
        flag("--stop", "End the loop"),
    ],
    lead: Lead::Optional,
    live: None,
    usage: Some("[count|duration] [prompt]"),
};

const HEARTBEAT: Grammar = Grammar {
    words: &[
        word("status", "Show this session's heartbeat", &NOTHING),
        word("pause", "Pause the heartbeat", &NOTHING),
        word("resume", "Resume the heartbeat", &NOTHING),
        word("stop", "Remove the heartbeat", &NOTHING),
        word("clear", "Remove the heartbeat", &NOTHING),
    ],
    options: &[
        opt("--every", "<interval>", "How often it beats (default 5m)"),
        flag("--steer", "Deliver it into the running turn (the default)"),
        flag("--follow-up", "Queue it after the running turn"),
    ],
    lead: Lead::None,
    live: None,
    usage: Some("<instruction>"),
};

const AUTONOMOUS: Grammar = Grammar {
    words: &[
        word("status", "Show autonomous mode", &NOTHING),
        word("on", "Turn autonomous mode on", &NOTHING),
        word("off", "Turn autonomous mode off", &NOTHING),
    ],
    options: &[],
    lead: Lead::None,
    live: None,
    usage: Some("<task>"),
};

const EFFECT_ID: Grammar = Grammar {
    words: &[],
    options: &[],
    lead: Lead::None,
    live: Some(LiveValues::OpenEffects),
    usage: Some("<id>"),
};

/// The argument texts, by command path.
const GRAMMARS: &[(&str, &Grammar)] = &[
    ("budget", &BUDGET),
    ("accept", &ACCEPT),
    ("loop", &LOOP),
    ("heartbeat", &HEARTBEAT),
    ("autonomous", &AUTONOMOUS),
    ("effects ran", &EFFECT_ID),
    ("effects not-run", &EFFECT_ID),
    (
        "factory",
        &words(&[
            word("on", "Open the agent factory gate", &NOTHING),
            word("off", "Close the agent factory gate", &NOTHING),
            word("status", "Show the gate", &NOTHING),
        ]),
    ),
    ("speed", &ON_OFF),
    (
        "cvar",
        &words(&[word(
            "save",
            "Save this session's console variables to its agent cfg",
            &NOTHING,
        )]),
    ),
    (
        "set",
        &Grammar {
            words: &[],
            options: &[flag("--global", "Set it in the global config.cfg")],
            lead: Lead::None,
            live: None,
            usage: Some("<id> <value>"),
        },
    ),
    (
        "rlm-max-depth",
        &Grammar {
            words: &[],
            options: &[flag("--global", "Also set the global default")],
            lead: Lead::Required,
            live: None,
            usage: Some("<n>"),
        },
    ),
    (
        "force",
        &Grammar {
            words: &[],
            options: &[opt("--tries", "<n>", "Retries per forced run (default 1)")],
            lead: Lead::Required,
            live: None,
            usage: Some("<tool>"),
        },
    ),
    (
        "new",
        &Grammar {
            words: &[],
            options: &[opt(
                "--name",
                "\"<session name>\" --",
                "Name the new session",
            )],
            lead: Lead::None,
            live: None,
            usage: Some("[prompt]"),
        },
    ),
];

#[cfg(test)]
mod tests;
