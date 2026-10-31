//! The session's agent in the cvar layers (`bend/cvar.bend`): which agent it is ([`CvarAgent`]: the root `main`, or
//! a subagent with the family it inherited at spawn), and its own state
//! ([`AgentState`]: the sets and aliases its commands made), kept in the
//! `eukhe.cvar.agent` document of the main conversation in its own commit.
//! The document is rewindable: a fork or a move in the tree starts from
//! the state as of its fork point, and the session re-reads it whenever
//! its main conversation changes ([`super::EukheSession::reload_main`]).

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::documents::{DocDefinition, RewindableConversationDoc};
use eukhe_durable::harness::Conversation;
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{DocumentReader, DocumentReaderExt, RewindableFork};
use eukhe_types::cvar::{parse_list, render_list, Aliases, Command, ParseError};
use serde::{Deserialize, Serialize};

use super::open::EukheSession;
use crate::settings::cvar::{registry, AgentLayer, CvarError, CvarWriteError, Flag, Set, Sets};
use crate::settings::{SettingsError, SettingsManager, SettingsScope};

/// The cfg file of every subagent's profile (Global scope).
const SUBAGENT_CFG: &str = "subagent.cfg";
/// The name of the root session's agent (`agents/main.cfg`).
const ROOT_AGENT: &str = "main";

/// Which agent a session is.
#[derive(Debug, Clone, PartialEq)]
pub enum CvarAgent {
    /// A top-level session: agent `main`, profile `agents/main.cfg`.
    Root,
    /// A spawned subagent: the family its parent had at spawn (root first),
    /// then its profile (`subagent.cfg`, then `agents/<name>.cfg` when it
    /// has a name).
    Subagent {
        inherited: Vec<AgentLayer>,
        name: Option<String>,
    },
}

impl CvarAgent {
    /// The agent's name, the stem of its `agents/<name>.cfg`. A name that
    /// is not one plain file name (a path, `.`, `..`) names no file.
    #[must_use]
    pub fn name(&self) -> Option<&str> {
        let name = match self {
            CvarAgent::Root => ROOT_AGENT,
            CvarAgent::Subagent { name, .. } => name.as_deref()?,
        };
        let plain = !name.is_empty()
            && name != "."
            && name != ".."
            && !name.contains(['/', '\\'])
            && !name.contains('\0');
        plain.then_some(name)
    }

    /// The agent's profile files, relative to the agent dir, in order.
    #[must_use]
    pub fn profile_files(&self) -> Vec<String> {
        let mut files = match self {
            CvarAgent::Root => Vec::new(),
            CvarAgent::Subagent { .. } => vec![SUBAGENT_CFG.to_string()],
        };
        if let Some(name) = self.name() {
            files.push(format!("{}/{name}.cfg", crate::settings::PROFILE_DIR));
        }
        files
    }

    /// The layers above this agent (the family it inherited).
    #[must_use]
    pub fn inherited(&self) -> &[AgentLayer] {
        match self {
            CvarAgent::Root => &[],
            CvarAgent::Subagent { inherited, .. } => inherited,
        }
    }
}

/// One alias of the agent: its name and its body as a command list.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AliasEntry {
    pub name: String,
    pub body: String,
}

/// The agent's own state: its sets (the last of each cvar) and the aliases
/// its commands defined.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct AgentState {
    #[serde(default)]
    pub sets: Sets,
    #[serde(default)]
    pub aliases: Vec<AliasEntry>,
}

impl AgentState {
    /// The state of `sets` (each cvar's last set kept, in the order of
    /// those sets) and `aliases`.
    #[must_use]
    pub fn new(sets: &Sets, aliases: &Aliases) -> Self {
        let mut kept: Vec<Set> = Vec::with_capacity(sets.0.len());
        for set in &sets.0 {
            kept.retain(|known| known.id != set.id);
            kept.push(set.clone());
        }
        Self {
            sets: Sets(kept),
            aliases: aliases
                .iter()
                .map(|(name, body)| AliasEntry {
                    name: name.to_string(),
                    body: render_list(body),
                })
                .collect(),
        }
    }

    /// The aliases as a table, and an error for each body that does not
    /// parse (a document edited by hand), which defines nothing. A body is
    /// a rendered command list, which parses back to the same commands.
    #[must_use]
    pub fn alias_table(&self) -> (Aliases, Vec<SettingsError>) {
        let mut aliases = Aliases::default();
        let mut errors = Vec::new();
        for entry in &self.aliases {
            match parse_list(&entry.body) {
                Ok(body) => aliases.define(entry.name.clone(), body),
                Err(kind) => errors.push(SettingsError {
                    scope: SettingsScope::Global,
                    message: format!(
                        "agent state: alias `{}` does not parse: {}",
                        entry.name,
                        ParseError { line: 1, kind }
                    ),
                }),
            }
        }
        (aliases, errors)
    }
}

/// `eukhe.cvar.agent`: the agent state of one conversation. A fork starts
/// from the state as of its fork point.
pub static AGENT_DOC: RewindableConversationDoc<AgentState> =
    match RewindableConversationDoc::define(
        DocDefinition {
            kind: "eukhe.cvar.agent",
            version: 1,
            initial: AgentState::default,
            migrate: None,
            checkpoint_when: Some(|_, _, _| true),
        },
        RewindableFork::AsOf,
    ) {
        Ok(token) => token,
        Err(_) => panic!("eukhe.cvar.agent has a valid version"),
    };

/// The agent state of `conversation`; the empty state when it has none.
///
/// # Errors
///
/// Document read failures, or a value that does not decode.
pub async fn read_agent_state(
    reader: &(impl DocumentReader + ?Sized),
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<AgentState> {
    match reader.snapshot(&AGENT_DOC, conversation.id(), cx).await? {
        None => Ok(AgentState::default()),
        Some(value) => Ok(from_json(&JsonValue::Object(value))?),
    }
}

/// Commit `state` as the agent state of `conversation`, in its own commit.
///
/// # Errors
///
/// Encoding or commit failures.
async fn write_agent_state(
    conversation: &Conversation,
    state: &AgentState,
    cx: &Context,
) -> SessionResult<()> {
    let id = conversation.id();
    let sets = to_json(&state.sets)?;
    let aliases = to_json(&state.aliases)?;
    conversation
        .commit(
            move |tx| async move {
                let draft = tx.doc(&AGENT_DOC, id).await?;
                draft.set("sets", sets)?;
                draft.set("aliases", aliases)?;
                Ok(())
            },
            cx,
        )
        .await
}

/// Where a cvar command line applies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CvarLineScope {
    /// This session's own sets and aliases (`/set`, `/toggle`, `/alias`).
    Session,
    /// The global config.cfg (`/set --global`): `set` and `toggle` only.
    Global,
}

/// Why a cvar command line did not apply.
#[derive(Debug, thiserror::Error)]
pub enum CvarLineError {
    /// A command was rejected (nothing of the line applied).
    #[error(transparent)]
    Cvar(CvarError),
    /// A global line with a command other than `set` or `toggle`.
    #[error("`{command}` does not apply to the global config: only `set` and `toggle` do")]
    NotGlobal { command: String },
    /// A subagent without a name has no `agents/<name>.cfg` to save to.
    #[error("this agent has no name: it has no agents/<name>.cfg to save to")]
    Unnamed,
    /// The document commit or a cfg write failed.
    #[error("{0}")]
    Io(String),
}

impl From<CvarWriteError> for CvarLineError {
    fn from(error: CvarWriteError) -> Self {
        match error {
            CvarWriteError::Cvar(error) => CvarLineError::Cvar(error),
            CvarWriteError::Io(message) => CvarLineError::Io(message),
        }
    }
}

/// Run the command list `line` for `session` (the daemon's `cvar`):
/// [`CvarLineScope::Session`] runs it into the session's own sets with
/// its aliases (config.cfg's, its profile's, its own) and commits the new
/// agent state on a change; [`CvarLineScope::Global`] writes each `set` /
/// `toggle` to the global config.cfg. A line with a rejected command
/// applies nothing. Answers the replicated values after the line.
///
/// # Errors
///
/// A line that does not parse, a rejected command, or a failed write.
#[tracing::instrument(skip(session, cx))]
pub async fn run_cvar_line(
    session: &EukheSession,
    line: &str,
    scope: CvarLineScope,
    cx: &Context,
) -> Result<Vec<Set>, CvarLineError> {
    let commands = parse_list(line)
        .map_err(|kind| CvarLineError::Cvar(CvarError::Parse(ParseError { line: 1, kind })))?;
    let settings = &session.deps().settings;
    let _gate = session.cvar_gate().lock().await;
    match scope {
        CvarLineScope::Global => {
            if let Some(command) = commands
                .iter()
                .find(|command| !matches!(command, Command::Set { .. } | Command::Toggle { .. }))
            {
                return Err(CvarLineError::NotGlobal {
                    command: command.to_string(),
                });
            }
            // Locked, fsync'd file writes and a full reload: off the
            // async worker.
            let global = std::sync::Arc::clone(settings);
            tokio::task::spawn_blocking(move || global.run_global(&commands))
                .await
                .map_err(|error| {
                    CvarLineError::Io(format!("the global write did not finish: {error}"))
                })??;
        }
        CvarLineScope::Session => {
            if let Some(state) = settings.plan(&commands).map_err(CvarLineError::Cvar)? {
                write_agent_state(&session.main(), &state, cx)
                    .await
                    .map_err(|error| CvarLineError::Io(error.to_string()))?;
                settings.set_agent_state(state);
            }
        }
    }
    Ok(settings.manager().cvars().replicated())
}

/// Write the session's own sets of `persist` cvars to its
/// `agents/<name>.cfg` (the daemon's `cvar_save`), replacing the lines of
/// the same cvars.
///
/// # Errors
///
/// An unnamed subagent, or a failed write.
#[tracing::instrument(skip(session))]
pub async fn save_agent_cfg(session: &EukheSession) -> Result<(), CvarLineError> {
    let settings = &session.deps().settings;
    let _gate = session.cvar_gate().lock().await;
    let agent = settings.agent();
    let name = agent.name().ok_or(CvarLineError::Unnamed)?;
    let sets = settings
        .agent_state()
        .sets
        .written(registry(), Flag::Persist);
    let mut manager = SettingsManager::create(settings.cwd(), settings.agent_dir());
    manager.write_agent_cfg(name, &sets)?;
    Ok(())
}

/// Re-read the agent state of the session's main conversation into its
/// settings (after open and whenever the main conversation changes).
///
/// # Errors
///
/// The document cannot be read.
pub(crate) async fn load_agent_state(session: &EukheSession, cx: &Context) -> SessionResult<()> {
    let _gate = session.cvar_gate().lock().await;
    let state = read_agent_state(session.harness(), &session.main(), cx).await?;
    session.deps().settings.set_agent_state(state);
    Ok(())
}

#[cfg(test)]
mod tests;
