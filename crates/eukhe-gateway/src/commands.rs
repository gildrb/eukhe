//! The phone commands and what one text message means to the gateway: a
//! command, an answer the gateway sends itself, or a prompt for the agent.
//! Signal has no command menu, so a lone `/` lists the commands, a prefix
//! lists the commands it starts, and a near miss names the closest. The
//! compiled Bend core decides (`bend/gateway_commands.bend`, entry
//! `bend/ffi_gateway_commands.bend`, laws `laws/gateway_commands.bend`),
//! and holds the one copy of the command list; this file sends the text
//! with the session command names and reads the meaning.

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};
use eukhe_types::slash_commands::SESSION_SLASH_COMMAND_NAMES;

/// A phone command (case-insensitive name, exact argument count).
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum PhoneCommand {
    Help,
    Sessions,
    /// `/use N`, with `N` as written.
    Use(String),
    Latest,
    New,
    Stop,
    Status,
    Memory,
    /// `/model` lists; `/model N` switches to the Nth listed model.
    Model(Option<String>),
    /// `/reasoning` shows; `/reasoning <level>` sets it.
    Reasoning(Option<String>),
}

/// What one text message means to the gateway.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Parsed {
    Command(PhoneCommand),
    /// A command-shaped message that runs nothing: the gateway answers it
    /// (the command list, a usage line, or a suggestion) and the agent
    /// never sees it.
    Answer(String),
    /// Text for the agent.
    Prompt,
}

/// Parse one text message (without images).
///
/// A first word of `/` plus letters, digits, `-` or `_` is command-shaped;
/// any other text (a path such as `/tmp/x`, a sentence) goes to the agent,
/// and so does a session command (`/compact`, ...): the session runs it.
/// A command-shaped message that names a command with the wrong arguments
/// gets its usage; an unknown name alone gets suggestions; an unknown name
/// followed by more words goes to the agent. A Signal message body is far
/// below the wire's `STR_MAX`.
pub(crate) fn parse(text: &str) -> Parsed {
    expect_core(Entry::GatewayCommands, parse_call(text))
}

/// The `/help` text: the core's answer to a lone `/` (laws
/// `gateway_commands_spec`, `gateway_commands_example`), so the command
/// list has one copy, in the Bend model.
pub(crate) fn help() -> String {
    let answer = parse_call("/").and_then(|parsed| match parsed {
        Parsed::Answer(text) => Ok(text),
        Parsed::Command(_) | Parsed::Prompt => Err(Error::from(WireError::Malformed {
            at: 0,
            expected: "the command list",
        })),
    });
    expect_core(Entry::GatewayCommands, answer)
}

fn parse_call(text: &str) -> Result<Parsed, Error> {
    let mut request = Writer::new();
    request.str(text).count(SESSION_SLASH_COMMAND_NAMES.len());
    for name in SESSION_SLASH_COMMAND_NAMES {
        request.str(name);
    }
    let reply = call(Entry::GatewayCommands, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let parsed = match reader.tag_of(3, "a message meaning")? {
        0 => Parsed::Command(match reader.tag_of(10, "a phone command")? {
            0 => PhoneCommand::Help,
            1 => PhoneCommand::Sessions,
            2 => PhoneCommand::Use(reader.str()?.to_owned()),
            3 => PhoneCommand::Latest,
            4 => PhoneCommand::New,
            5 => PhoneCommand::Stop,
            6 => PhoneCommand::Status,
            7 => PhoneCommand::Memory,
            8 => PhoneCommand::Model(maybe_str(&mut reader)?),
            9.. => PhoneCommand::Reasoning(maybe_str(&mut reader)?),
        }),
        1 => Parsed::Answer(reader.str()?.to_owned()),
        2.. => Parsed::Prompt,
    };
    reader.end()?;
    Ok(parsed)
}

/// An optional argument of the reply: `/model N`, `/reasoning <level>`.
fn maybe_str(reader: &mut Reader<'_>) -> Result<Option<String>, WireError> {
    Ok(if reader.maybe()? {
        Some(reader.str()?.to_owned())
    } else {
        None
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The meaning comes from the compiled core, with Rust's session
    /// command names: a command, a session command, `/use` with its
    /// argument, a near miss.
    #[test]
    fn the_core_parses_phone_messages() {
        assert_eq!(
            [
                parse("/help"),
                parse("/dynamic-workflow --size large review the repo"),
                parse("/compact"),
                parse("/use 3"),
                parse("/hlep"),
            ],
            [
                Parsed::Command(PhoneCommand::Help),
                Parsed::Prompt,
                Parsed::Prompt,
                Parsed::Command(PhoneCommand::Use("3".to_string())),
                Parsed::Answer(
                    "No command /hlep. Did you mean /help?\nNot sent to the agent. Send / for all commands."
                        .to_string()
                ),
            ]
        );
    }

    /// `/model` and `/reasoning` take no argument or one; a wrong argument
    /// count gets the usage line, never the agent.
    #[test]
    fn model_and_reasoning_parse_with_and_without_arguments() {
        assert_eq!(
            [
                parse("/model"),
                parse("/model 2"),
                parse("/reasoning"),
                parse("/reasoning high"),
                parse("/model 2 3"),
                parse("/reasoning low extra"),
            ],
            [
                Parsed::Command(PhoneCommand::Model(None)),
                Parsed::Command(PhoneCommand::Model(Some("2".to_string()))),
                Parsed::Command(PhoneCommand::Reasoning(None)),
                Parsed::Command(PhoneCommand::Reasoning(Some("high".to_string()))),
                Parsed::Answer(
                    "Usage: /model [N] - Show the models; N switches to one.".to_string()
                ),
                Parsed::Answer(
                    "Usage: /reasoning [level] - Show the thinking level; a level sets it."
                        .to_string()
                ),
            ]
        );
    }
}
