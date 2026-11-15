//! A principal's message and the run it begins (spec/README.md B15, B20):
//! its `/b` prefix (`/b quick cost=2 fix the parser`) read in the compiled
//! core (`eukhe_bend::rules::limits::prefix`) against the shipped presets
//! and the principal's `budget.presets`, the run it starts or joins filled
//! with what the prefix asks, and the text after the prefix, which reaches
//! the model verbatim. Every surface that sends the principal's messages
//! (the daemon's `prompt` for the TUI, ACP and the other clients, `-p`,
//! the SDK, the RPC mode) begins them here.

use eukhe_bend::rules::limits::{prefix, Key, Prefix};
use eukhe_types::budget::{BudgetDimension, RunKind, RunLimits};
use eukhe_types::budget_input::{key_dimension, parse_limit, BudgetTextError};

use super::runs::{RunError, RunStart};
use super::BudgetGate;

/// The presets every principal has: `quick` (a quarter of the limits
/// profile) and `deep` (four times it).
const SHIPPED_PRESETS: [&str; 2] = ["quick", "deep"];

/// What a message's `/b` prefix asks of its run: the presets it names, in
/// order, the limits its `key=value` pairs set, and the message after it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct RunAsk {
    presets: Vec<String>,
    set: RunLimits,
    rest: String,
}

/// Why a message's run did not begin: nothing is sent, the budget is as
/// it was.
#[derive(Debug, thiserror::Error)]
pub enum MessageError {
    /// A `/b` pair with an empty value, a key given twice, or a value that
    /// is no amount of its key: the error names the word.
    #[error(transparent)]
    Prefix(#[from] BudgetTextError),
    /// The run's limits did not fill.
    #[error(transparent)]
    Run(#[from] RunError),
}

/// The `/b` prefix of `message` read against the preset `names`; `None`
/// for a message without one. A message the compiled core does not take
/// (past its wire) has no prefix.
fn run_prefix(message: &str, names: &[&str]) -> Result<Option<RunAsk>, BudgetTextError> {
    // Only a message that starts with a slash (full-width included) can
    // carry a prefix.
    if !message.starts_with(['/', '\u{ff0f}']) {
        return Ok(None);
    }
    let (presets, pairs, rest) = match prefix(message, names) {
        Ok(Prefix::Read {
            presets,
            pairs,
            rest,
        }) => (presets, pairs, rest),
        Ok(Prefix::Refused { word }) => {
            let (key, value) = word.split_once('=').unwrap_or((&word, ""));
            return Err(match key_dimension(key) {
                Some(_) if !value.is_empty() => BudgetTextError::Repeated {
                    name: key.to_owned(),
                },
                Some(dimension) => match parse_limit(dimension, key, value) {
                    Ok(_) => BudgetTextError::Repeated {
                        name: key.to_owned(),
                    },
                    Err(error) => error,
                },
                None => BudgetTextError::UnknownWord { word },
            });
        }
        Err(_) => return Ok(None),
    };
    if presets.is_empty() && pairs.is_empty() && rest == message {
        return Ok(None);
    }
    let mut set = RunLimits::default();
    for (key, value) in pairs {
        let (dimension, name) = match key {
            Key::Cost => (BudgetDimension::Cost, "cost"),
            Key::Tokens => (BudgetDimension::Tokens, "tokens"),
            Key::Time => (BudgetDimension::Time, "time"),
            Key::Calls => (BudgetDimension::ToolCalls, "calls"),
            Key::Requests => (BudgetDimension::Requests, "requests"),
        };
        set = set.with(dimension, Some(parse_limit(dimension, name, &value)?));
    }
    Ok(Some(RunAsk {
        presets: presets
            .into_iter()
            .filter_map(|place| names.get(place).map(|name| (*name).to_owned()))
            .collect(),
        set,
        rest,
    }))
}

impl BudgetGate {
    /// The principal's message `text`: sent while the session runs
    /// nothing (`joins` false) it starts a new run of `kind`, filled with
    /// what its `/b` prefix asks; one that joins the running run (queued,
    /// steering, a later `-p` message) sets what its prefix asks on that
    /// run. Returns the text the conversation gets: the message after its
    /// prefix. Blocking file IO.
    ///
    /// # Errors
    ///
    /// A prefix that does not read, and the failures of
    /// [`Self::start_run`] and [`Self::set_asked`]: the budget is as it
    /// was and nothing is to be sent.
    pub fn begin_message(
        &self,
        kind: RunKind,
        joins: bool,
        text: &str,
    ) -> Result<String, MessageError> {
        let presets = self.facts().presets;
        let names: Vec<&str> = SHIPPED_PRESETS
            .into_iter()
            .chain(
                presets
                    .as_object()
                    .into_iter()
                    .flat_map(|own| own.keys().map(String::as_str)),
            )
            .collect();
        let Some(ask) = run_prefix(text, &names)? else {
            if !joins {
                self.start_run(RunStart {
                    kind,
                    ..RunStart::default()
                })?;
            }
            return Ok(text.to_owned());
        };
        if joins {
            self.set_asked(ask.set, ask.presets)?;
        } else {
            self.start_run(RunStart {
                kind,
                set: ask.set,
                presets: ask.presets,
                standing: None,
            })?;
        }
        Ok(ask.rest)
    }
}

#[cfg(test)]
mod tests {
    use eukhe_types::budget::{LimitValue, RunLimits};

    use super::{run_prefix, RunAsk};

    /// A message's `/b` prefix names presets and limits; a message without
    /// one has none, and a value that does not read is refused by name.
    #[test]
    fn the_b_prefix_reads_presets_and_limits() {
        let read = |text: &str| {
            run_prefix(text, &["quick", "deep", "mine"]).map_err(|error| error.to_string())
        };
        let ask = |presets: &[&str], set: RunLimits, rest: &str| {
            Ok(Some(RunAsk {
                presets: presets.iter().map(|name| (*name).to_owned()).collect(),
                set,
                rest: rest.to_owned(),
            }))
        };
        assert_eq!(
            [
                read("fix the parser"),
                read("/budget"),
                read("/b quick fix the parser"),
                read("/b mine cost=2 time=unlimited fix it"),
                read("/b cost=abc fix it"),
                read("/b cost=1 cost=2 fix it"),
            ],
            [
                Ok(None),
                Ok(None),
                ask(&["quick"], RunLimits::default(), "fix the parser"),
                ask(
                    &["mine"],
                    RunLimits {
                        cost_micros: Some(LimitValue::At(2_000_000)),
                        time_ms: Some(LimitValue::Unlimited),
                        ..RunLimits::default()
                    },
                    "fix it"
                ),
                Err("cost \"abc\": expected dollars, like 1.50 or $1.50".to_string()),
                Err("cost is given twice".to_string()),
            ]
        );
    }
}
