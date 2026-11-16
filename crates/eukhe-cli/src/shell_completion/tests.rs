use super::*;

/// What the bash script offers for `line` (the cursor at its end; a
/// trailing space starts a new word).
fn bash_offers(line: &str) -> Vec<String> {
    let words: Vec<String> = line.split(' ').map(quoted).collect();
    let program = format!(
        "{}\nCOMP_WORDS=({}); COMP_CWORD={}; _{APP_NAME}; printf '%s\\n' \"${{COMPREPLY[@]}}\"",
        script(Shell::Bash),
        words.join(" "),
        words.len() - 1
    );
    let output = std::process::Command::new("bash")
        .arg("-c")
        .arg(program)
        .output()
        .expect("bash runs");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect()
}

#[test]
fn bash_completes_commands_subcommands_options_and_values() {
    assert_eq!(
        [
            bash_offers("eukhe bud"),
            bash_offers("eukhe budget a"),
            bash_offers("eukhe budget set --c"),
            bash_offers("eukhe models r"),
            bash_offers("eukhe --mode "),
            bash_offers("eukhe --budget-c"),
            bash_offers("eukhe ti"),
            bash_offers("eukhe completion "),
        ],
        [
            vec!["budget"],
            vec!["add", "audit"],
            vec!["--cost", "--calls"],
            vec!["refresh"],
            vec!["text", "json", "rpc", "acp", "daemon"],
            vec!["--budget-cost", "--budget-calls"],
            vec!["tiny-models", "tiny"],
            vec!["bash", "zsh", "fish", "nu"],
        ]
        .map(|offers| offers.into_iter().map(String::from).collect::<Vec<_>>())
    );
}

/// Every option the help lists is one the parser reads.
#[test]
fn every_listed_option_parses() {
    let unknown: Vec<&str> = top_level_options()
        .filter_map(|(head, description)| flag(head, description))
        .flat_map(|flag| flag.names)
        .filter_map(|name| name.strip_prefix("--"))
        .filter(|name| !crate::args::KNOWN_LONG_OPTIONS.contains(name))
        .collect();
    assert_eq!(unknown, Vec::<&str>::new());
}

#[test]
fn an_option_line_reads_its_spellings_value_and_choices() {
    assert_eq!(
        [
            spec_flag("-a, --all  Include saved agents"),
            spec_flag("--calls, --tool-calls <N>  Tool calls"),
            flag("--mode <text|json>", "Select the output mode"),
            flag("--", "Treat all following arguments as messages"),
        ],
        [
            Some(Flag {
                names: vec!["-a", "--all"],
                value: false,
                choices: vec![],
                description: "Include saved agents",
            }),
            Some(Flag {
                names: vec!["--calls", "--tool-calls"],
                value: true,
                choices: vec![],
                description: "Tool calls",
            }),
            Some(Flag {
                names: vec!["--mode"],
                value: true,
                choices: vec!["text", "json"],
                description: "Select the output mode",
            }),
            None,
        ]
    );
}
