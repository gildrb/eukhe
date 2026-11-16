//! `eukhe completion <bash|zsh|fish|nu>`: the shell completion script,
//! generated from the command table and the option groups the help prints
//! (`command_registry`), so a command, a subcommand or an option completes
//! the moment it is in the help.

use crate::command_registry::{
    command_aliases, get_child_command_specs, top_level_options, CommandSpec, COMMAND_SPECS,
};
use crate::config::APP_NAME;

/// A shell the script is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shell {
    Bash,
    Zsh,
    Fish,
    Nu,
}

impl Shell {
    fn from_name(name: &str) -> Option<Shell> {
        match name {
            "bash" => Some(Shell::Bash),
            "zsh" => Some(Shell::Zsh),
            "fish" => Some(Shell::Fish),
            "nu" | "nushell" => Some(Shell::Nu),
            _ => None,
        }
    }
}

/// A word that may come next: a command, or an alias of one.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Word {
    name: &'static str,
    /// The path the word leads to (an alias leads to its command's).
    to: String,
    summary: &'static str,
}

/// One option of a place.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Flag {
    /// Every spelling (`-a`, `--all`).
    names: Vec<&'static str>,
    /// It takes a value.
    value: bool,
    /// The values it takes, when the help lists them (`<text|json>`).
    choices: Vec<&'static str>,
    description: &'static str,
}

/// One place of a command line: the words and options that may follow.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Place {
    /// The command path, its names with one space between; empty at the
    /// top.
    path: String,
    summary: &'static str,
    words: Vec<Word>,
    flags: Vec<Flag>,
}

/// An option as the help prints it (`-a, --all`, `--mode <a|b>`) and its
/// description; none for the end-of-options marker.
fn flag(head: &'static str, description: &'static str) -> Option<Flag> {
    let forms: Vec<&'static str> = head.split(", ").collect();
    let names: Vec<&'static str> = forms
        .iter()
        .filter_map(|form| form.split_whitespace().next())
        .filter(|name| name.starts_with('-') && *name != "--")
        .collect();
    let value = forms.last().and_then(|form| form.split_whitespace().nth(1));
    let choices = value
        .and_then(|value| value.strip_prefix('<')?.strip_suffix('>'))
        .filter(|inner| inner.contains('|'))
        .map(|inner| inner.split('|').collect())
        .unwrap_or_default();
    (!names.is_empty()).then(|| Flag {
        names,
        value: value.is_some(),
        choices,
        description,
    })
}

/// An option line of a command spec (`--json  Print JSON`).
fn spec_flag(line: &'static str) -> Option<Flag> {
    let (head, description) = line.split_once("  ").unwrap_or((line, ""));
    flag(head.trim(), description.trim())
}

fn spec_place(spec: &'static CommandSpec) -> Place {
    Place {
        path: spec.path.join(" "),
        summary: spec.summary,
        words: get_child_command_specs(spec.path)
            .into_iter()
            .map(|child| Word {
                name: child.path[child.path.len() - 1],
                to: child.path.join(" "),
                summary: child.summary,
            })
            .collect(),
        flags: spec.options.iter().copied().filter_map(spec_flag).collect(),
    }
}

/// Every place of the command line: the top, then each command.
fn places() -> Vec<Place> {
    let commands = COMMAND_SPECS.iter().filter(|spec| spec.path.len() == 1);
    let words = commands
        .clone()
        .map(|spec| Word {
            name: spec.path[0],
            to: spec.path[0].to_string(),
            summary: spec.summary,
        })
        .chain(command_aliases().map(|(alias, spec)| Word {
            name: alias,
            to: spec.path[0].to_string(),
            summary: spec.summary,
        }))
        .collect();
    let top = Place {
        path: String::new(),
        summary: "",
        words,
        flags: top_level_options()
            .filter_map(|(head, description)| flag(head, description))
            .collect(),
    };
    std::iter::once(top)
        .chain(COMMAND_SPECS.iter().map(spec_place))
        .collect()
}

/// The steps from a place by a word: `(<path>/<word>, <next path>)`.
fn steps(places: &[Place]) -> Vec<(String, &str)> {
    places
        .iter()
        .flat_map(|place| {
            place
                .words
                .iter()
                .map(move |word| (format!("{}/{}", place.path, word.name), word.to.as_str()))
        })
        .collect()
}

/// The options that take a value, with the values they take.
fn value_flags(places: &[Place]) -> Vec<(&'static str, Vec<&'static str>)> {
    let mut out: Vec<(&'static str, Vec<&'static str>)> = Vec::new();
    for flag in places.iter().flat_map(|place| &place.flags) {
        for name in flag.names.iter().filter(|_| flag.value) {
            if !out.iter().any(|(known, _)| known == name) {
                out.push((name, flag.choices.clone()));
            }
        }
    }
    out
}

/// `text` inside single quotes for a POSIX-like shell.
fn quoted(text: &str) -> String {
    format!("'{}'", text.replace('\'', r"'\''"))
}

/// The first line of `text`, for one-line descriptions.
fn line(text: &str) -> &str {
    text.lines().next().unwrap_or_default()
}

fn bash(places: &[Place]) -> String {
    let steps = steps(places)
        .iter()
        .map(|(from, to)| format!("            {}) path={} ;;\n", quoted(from), quoted(to)))
        .collect::<Vec<_>>()
        .concat();
    let values = value_flags(places)
        .iter()
        .map(|(name, choices)| {
            format!(
                "        {name}) COMPREPLY=($(compgen -W {} -- \"$cur\")); return ;;\n",
                quoted(&choices.join(" "))
            )
        })
        .collect::<Vec<_>>()
        .concat();
    let words = places
        .iter()
        .map(|place| {
            let names: Vec<&str> = place
                .words
                .iter()
                .map(|word| word.name)
                .chain(
                    place
                        .flags
                        .iter()
                        .flat_map(|flag| flag.names.iter().copied()),
                )
                .collect();
            format!(
                "        {}) words={} ;;\n",
                quoted(&place.path),
                quoted(&names.join(" "))
            )
        })
        .collect::<Vec<_>>()
        .concat();
    format!(
        "# {APP_NAME} completion for bash: source <({APP_NAME} completion bash)\n\
_{APP_NAME}() {{
    local cur=${{COMP_WORDS[COMP_CWORD]}} prev=${{COMP_WORDS[COMP_CWORD-1]}} path= words= i
    for ((i = 1; i < COMP_CWORD; i++)); do
        case \"$path/${{COMP_WORDS[i]}}\" in
{steps}        esac
    done
    case \"$prev\" in
{values}    esac
    case \"$path\" in
{words}    esac
    COMPREPLY=($(compgen -W \"$words\" -- \"$cur\"))
}}
complete -o default -F _{APP_NAME} {APP_NAME}
"
    )
}

fn zsh_item(name: &str, description: &str) -> String {
    quoted(&format!(
        "{}:{}",
        name.replace(':', r"\:"),
        line(description)
    ))
}

fn zsh(places: &[Place]) -> String {
    let steps = steps(places)
        .iter()
        .map(|(from, to)| format!("      ({}) path_={} ;;\n", quoted(from), quoted(to)))
        .collect::<Vec<_>>()
        .concat();
    let values = value_flags(places)
        .iter()
        .map(|(name, choices)| {
            let action = if choices.is_empty() {
                "_files".to_string()
            } else {
                format!("compadd -- {}", choices.join(" "))
            };
            format!("    ({name}) {action}; return ;;\n")
        })
        .collect::<Vec<_>>()
        .concat();
    let items = places
        .iter()
        .map(|place| {
            let items: Vec<String> = place
                .words
                .iter()
                .map(|word| zsh_item(word.name, word.summary))
                .chain(place.flags.iter().flat_map(|flag| {
                    flag.names
                        .iter()
                        .map(|name| zsh_item(name, flag.description))
                }))
                .collect();
            format!(
                "    ({}) items=({}) ;;\n",
                quoted(&place.path),
                items.join(" ")
            )
        })
        .collect::<Vec<_>>()
        .concat();
    format!(
        "#compdef {APP_NAME}
# {APP_NAME} completion for zsh: {APP_NAME} completion zsh > \"${{fpath[1]}}/_{APP_NAME}\"
_{APP_NAME}() {{
  local path_= i
  local -a items
  for ((i = 2; i < CURRENT; i++)); do
    case \"$path_/${{words[i]}}\" in
{steps}    esac
  done
  case \"${{words[CURRENT-1]}}\" in
{values}  esac
  case \"$path_\" in
{items}  esac
  _describe -t commands {APP_NAME} items || _files
}}
if [[ $zsh_eval_context[-1] == loadautofunc ]]; then
  _{APP_NAME} \"$@\"
else
  compdef _{APP_NAME} {APP_NAME}
fi
"
    )
}

fn fish_flag(at: &str, flag: &Flag) -> String {
    let condition = quoted(&format!("__{APP_NAME}_at {}", quoted(at)));
    let names: Vec<String> = flag
        .names
        .iter()
        .map(|name| match name.strip_prefix("--") {
            Some(long) => format!(" -l {long}"),
            None => format!(" -s {}", name.trim_start_matches('-')),
        })
        .collect();
    let value = if flag.value { " -r" } else { "" };
    let choices = if flag.choices.is_empty() {
        String::new()
    } else {
        format!(" -f -a {}", quoted(&flag.choices.join(" ")))
    };
    format!(
        "complete -c {APP_NAME} -n {condition}{}{value}{choices} -d {}\n",
        names.concat(),
        quoted(line(flag.description))
    )
}

fn fish(places: &[Place]) -> String {
    let steps = steps(places)
        .iter()
        .map(|(from, to)| {
            format!(
                "            case {}\n                set path {}\n",
                quoted(from),
                quoted(to)
            )
        })
        .collect::<Vec<_>>()
        .concat();
    let rows = places
        .iter()
        .flat_map(|place| {
            let condition = quoted(&format!("__{APP_NAME}_at {}", quoted(&place.path)));
            // Below a command, its words replace the file fallback; the
            // top keeps files (`@file`, a message).
            let files = if place.path.is_empty() { "" } else { " -f" };
            place
                .words
                .iter()
                .map(move |word| {
                    format!(
                        "complete -c {APP_NAME} -n {condition}{files} -a {} -d {}\n",
                        word.name,
                        quoted(line(word.summary))
                    )
                })
                .chain(place.flags.iter().map(|flag| fish_flag(&place.path, flag)))
        })
        .collect::<Vec<_>>()
        .concat();
    format!(
        "# {APP_NAME} completion for fish: {APP_NAME} completion fish > ~/.config/fish/completions/{APP_NAME}.fish
function __{APP_NAME}_path
    set -l path ''
    for word in (commandline -opc)[2..-1]
        switch \"$path/$word\"
{steps}        end
    end
    echo $path
end
function __{APP_NAME}_at
    test (__{APP_NAME}_path | string collect) = \"$argv[1]\"
end
{rows}"
    )
}

/// The nushell name of a value flag's choices completer.
fn nu_choices(name: &str) -> String {
    format!("nu-complete {APP_NAME} {name}")
}

fn nu_flag(flag: &Flag) -> Option<String> {
    let long = flag.names.iter().find_map(|name| name.strip_prefix("--"));
    let short = flag
        .names
        .iter()
        .find(|name| !name.starts_with("--"))
        .map(|name| name.trim_start_matches('-'));
    // nushell gives every extern its own --help.
    let name = long.filter(|long| *long != "help")?;
    let short = short.map(|short| format!("(-{short})")).unwrap_or_default();
    let kind = match (flag.value, flag.choices.is_empty()) {
        (false, _) => String::new(),
        (true, true) => ": string".to_string(),
        (true, false) => format!(": string@\"{}\"", nu_choices(name)),
    };
    Some(format!(
        "    --{name}{short}{kind} # {}\n",
        line(flag.description)
    ))
}

fn nu(places: &[Place]) -> String {
    let completers = value_flags(places)
        .iter()
        .filter(|(_, choices)| !choices.is_empty())
        .filter_map(|(name, choices)| {
            let long = name.strip_prefix("--")?;
            let values: Vec<String> = choices
                .iter()
                .map(|choice| format!("\"{choice}\""))
                .collect();
            Some(format!(
                "def \"{}\" [] {{ [{}] }}\n\n",
                nu_choices(long),
                values.join(" ")
            ))
        })
        .collect::<Vec<_>>()
        .concat();
    let aliases: Vec<(&str, &str)> = command_aliases()
        .map(|(alias, spec)| (alias, spec.path[0]))
        .collect();
    let externs = places
        .iter()
        .flat_map(|place| {
            let names = std::iter::once(place.path.clone()).chain(
                aliases
                    .iter()
                    .filter(|(_, command)| {
                        place.path == *command || place.path.starts_with(&format!("{command} "))
                    })
                    .map(|(alias, command)| format!("{alias}{}", &place.path[command.len()..])),
            );
            let flags = place
                .flags
                .iter()
                .filter_map(nu_flag)
                .collect::<Vec<_>>()
                .concat();
            let summary = line(place.summary).to_string();
            names
                .map(move |path| {
                    let name = if path.is_empty() {
                        APP_NAME.to_string()
                    } else {
                        format!("{APP_NAME} {path}")
                    };
                    format!(
                        "# {summary}\nexport extern \"{name}\" [\n{flags}    ...args: string\n]\n\n"
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
        .concat();
    format!(
        "# {APP_NAME} completion for nushell: {APP_NAME} completion nu | save -f ~/.config/nushell/{APP_NAME}.nu\n\
# then add `use ~/.config/nushell/{APP_NAME}.nu *` to config.nu\n\n{completers}{externs}"
    )
}

/// The completion script of `shell`.
#[must_use]
pub fn script(shell: Shell) -> String {
    let places = places();
    match shell {
        Shell::Bash => bash(&places),
        Shell::Zsh => zsh(&places),
        Shell::Fish => fish(&places),
        Shell::Nu => nu(&places),
    }
}

/// `eukhe completion <shell>`: prints the script; a missing or unknown
/// shell is a usage error (exit 2).
pub fn run_completion_command(args: &[String]) -> i32 {
    let [name] = args else {
        eprintln!("Usage: {APP_NAME} completion <bash|zsh|fish|nu>");
        return 2;
    };
    if let Some(shell) = Shell::from_name(name) {
        print!("{}", script(shell));
        0
    } else {
        eprintln!("Unknown shell: {name}. Use bash, zsh, fish or nu.");
        2
    }
}

#[cfg(test)]
mod tests;
