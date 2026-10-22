use super::*;

fn set(id: &str, value: &str) -> Command {
    Command::Set {
        id: id.to_string(),
        value: value.to_string(),
    }
}

fn run(alias: &str) -> Command {
    Command::Run {
        alias: alias.to_string(),
    }
}

#[test]
fn a_script_parses_lists_quotes_and_nested_bodies() {
    let (commands, errors) = parse_script(
        "# a comment\n\
         set steeringMode one-at-a-time; toggle retry.enabled\n\
         // another comment\n\
         alias fast \"set transport sse; set theme \\\"dark mode\\\"\"\n\
         bind ctrl+k \"action app.interrupt; fast\"\n\
         set theme\n\
         set a \"b\n\
         fast extra\n",
    );
    assert_eq!(
        (commands, errors),
        (
            vec![
                set("steeringMode", "one-at-a-time"),
                Command::Toggle {
                    id: "retry.enabled".to_string()
                },
                Command::Alias {
                    name: "fast".to_string(),
                    body: vec![set("transport", "sse"), set("theme", "dark mode")],
                },
                Command::Bind {
                    key: "ctrl+k".to_string(),
                    body: vec![
                        Command::Action {
                            id: "app.interrupt".to_string()
                        },
                        run("fast"),
                    ],
                },
            ],
            vec![
                ParseError {
                    line: 6,
                    kind: ParseErrorKind::Missing {
                        command: "set",
                        word: "value"
                    },
                },
                ParseError {
                    line: 7,
                    kind: ParseErrorKind::UnclosedQuote,
                },
                ParseError {
                    line: 8,
                    kind: ParseErrorKind::Extra {
                        command: "fast".to_string(),
                        word: "extra".to_string()
                    },
                },
            ],
        )
    );
}

#[test]
fn a_rendered_list_parses_back_to_itself() {
    let commands = vec![
        set("theme", "a \"quoted\" ; \\ value"),
        set("x", ""),
        Command::Alias {
            name: "go".to_string(),
            body: vec![set("a", "b c"), run("other")],
        },
        Command::Bind {
            key: "ctrl+shift+p".to_string(),
            body: vec![Command::Bind {
                key: "x".to_string(),
                body: vec![set("deep", "\"q\"")],
            }],
        },
    ];
    assert_eq!(parse_list(&render_list(&commands)), Ok(commands));
}

#[test]
fn a_redefined_alias_keeps_its_place_and_takes_the_new_body() {
    let mut aliases = Aliases::default();
    aliases.define("a".to_string(), vec![set("x", "1")]);
    aliases.define("b".to_string(), vec![]);
    aliases.define("a".to_string(), vec![set("x", "2")]);
    let mut expected = Aliases::default();
    expected.define("a".to_string(), vec![set("x", "2")]);
    expected.define("b".to_string(), vec![]);
    assert_eq!(aliases, expected);
}
