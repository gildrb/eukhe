use super::*;
use crate::slash_commands::SlashCommandRegistry;

/// The names of a menu's rows, `*` for the live values.
fn names(grammar: &str, text: &str) -> (Vec<&'static str>, Option<&'static str>) {
    let menu = menu(grammar_at(grammar), text);
    let rows = menu
        .rows
        .iter()
        .map(|row| match row {
            Row::Word(word) => word.name,
            Row::Opt(opt) => opt.name,
            Row::Live(LiveValues::OpenEffects) => "*",
        })
        .collect();
    (rows, menu.hint)
}

fn grammar_at(path: &str) -> &'static Grammar {
    grammar(path).unwrap_or_else(|| panic!("no grammar at {path}"))
}

#[test]
fn every_grammar_path_names_a_command() {
    let registry = SlashCommandRegistry::builtin();
    for path in paths() {
        let mut names = path.split(' ');
        let command = names.next().and_then(|name| registry.get(name));
        let sub = names.next();
        assert!(
            command.is_some_and(|command| sub
                .is_none_or(|sub| command.subcommands.iter().any(|known| known.name == sub))),
            "{path}"
        );
    }
}

#[test]
fn words_open_the_text_and_lead_to_their_own_text() {
    assert_eq!(
        [
            names("budget", ""),
            names("budget", "s"),
            names("budget", "set "),
            names("budget", "set cost=2 "),
            names("budget", "set cost=2 t"),
            names("budget", "set co"),
            names("budget", "set cost="),
            names("budget", "set cost=2"),
            names("budget", "audit "),
        ],
        [
            (vec!["set", "add", "audit", "on", "off"], None),
            (vec!["set"], None),
            (
                vec!["cost=", "tokens=", "time=", "calls=", "requests="],
                None
            ),
            (vec!["tokens=", "time=", "calls=", "requests="], None),
            (vec!["tokens=", "time="], None),
            (vec!["cost="], None),
            (vec![], Some("<dollars>")),
            (vec![], None),
            (vec![], None),
        ]
    );
}

#[test]
fn a_flag_with_a_value_waits_for_it_then_offers_the_rest() {
    assert_eq!(
        [
            names("loop", ""),
            names("loop", "7 "),
            names("loop", "7 --u"),
            names("loop", "7 --until "),
            names("loop", "7 --until 'bun "),
            names("loop", "7 --until 'bun test' "),
            names("loop", "7 --until 'bun test' fix the tests "),
            names("loop", "7 fix the "),
            names("loop", "7 --stop "),
        ],
        [
            (vec!["--until", "--while", "--stop"], None),
            (vec!["--until", "--while", "--stop"], None),
            (vec!["--until"], None),
            (vec![], Some("'<command>'|<condition in words>")),
            (vec![], None),
            (vec!["--while", "--stop"], None),
            (vec![], None),
            (vec![], None),
            (vec!["--until", "--while"], None),
        ]
    );
}

#[test]
fn a_word_with_text_names_what_it_expects() {
    assert_eq!(
        [
            names("accept", "cmd "),
            names("accept", "cmd --timeout 10 "),
            names("accept", "cmd make test"),
            names("accept", "returns "),
            names("accept", "intent "),
            names("accept", "CMD --e"),
        ],
        [
            (vec!["--expect", "--timeout", "--protect"], None),
            (vec!["--expect", "--protect"], None),
            (vec![], None),
            (vec![], Some("<n>")),
            (vec!["on", "off"], None),
            (vec!["--expect"], None),
        ]
    );
}

#[test]
fn live_values_open_the_text_and_the_usage_shows_without_rows() {
    assert_eq!(
        [
            names("effects ran", ""),
            names("effects ran", "tool:"),
            names("effects ran", "tool:a "),
            names("heartbeat", "check the build"),
            names("set", ""),
        ],
        [
            (vec!["*"], None),
            (vec!["*"], None),
            (vec![], None),
            (vec![], None),
            (vec!["--global"], None),
        ]
    );
    assert_eq!(
        [
            names("force", ""),
            names("force", "bash "),
            names("force", "--tries 2 "),
            names("rlm-max-depth", "3 --g"),
        ],
        [
            (vec![], Some("<tool>")),
            (vec!["--tries"], None),
            (vec![], Some("<tool>")),
            (vec!["--global"], None),
        ]
    );
}

#[test]
fn the_menu_names_the_token_it_replaces() {
    assert_eq!(
        [
            menu(grammar_at("budget"), "set ti").token,
            menu(grammar_at("budget"), "set ").token,
            menu(grammar_at("loop"), "--until 'a b").token,
        ],
        ["ti", "", ""]
    );
}
