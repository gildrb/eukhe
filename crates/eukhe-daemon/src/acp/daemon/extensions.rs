//! The `_eukhe/` request methods: each maps to the daemon commands of the
//! hosted session (`docs/embed/acp.md`, `docs/embed/eukhe-acp.schema.json`).

use eukhe_types::acceptance::{AcceptanceState, CheckSpec};
use eukhe_types::budget::{BudgetAmounts, RunLimits};
use eukhe_types::daemon::{BudgetReply, DaemonCommand, DaemonErrorInfo};
use eukhe_types::effects::{RanEffectsReply, UnknownEffectsReply};
use eukhe_types::undo::{DiffScope, TurnDiffReply, UndoReply};
use serde::de::DeserializeOwned;
use serde::Deserialize;
use serde_json::{json, Map, Value};

use super::error::DaemonLinkError;
use super::{jsonrpc, DaemonLink};

/// The method prefix of every eukhe extension.
pub(super) const PREFIX: &str = "_eukhe/";

/// One `_eukhe/` request, its params read.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum Extension {
    BudgetGet,
    BudgetSet { limits: RunLimits, standing: bool },
    BudgetAdd { amounts: BudgetAmounts },
    AcceptanceGet,
    AcceptanceSet(AcceptanceSetParams),
    Undo,
    Diff { scope: DiffScope },
    Effects,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct BudgetSetParams {
    limits: RunLimits,
    #[serde(default)]
    standing: bool,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
struct BudgetAddParams {
    amounts: BudgetAmounts,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct AcceptanceSetParams {
    #[serde(default)]
    checks: Vec<CheckSpec>,
    #[serde(default)]
    max_returns: Option<u64>,
    #[serde(default)]
    intent: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
struct DiffParams {
    #[serde(default)]
    scope: DiffScope,
}

/// A failed `_eukhe/` request.
#[derive(Debug, thiserror::Error)]
pub(super) enum ExtensionError {
    #[error("unknown eukhe extension method")]
    UnknownMethod,
    #[error("{0}")]
    InvalidParams(#[source] serde_json::Error),
    #[error(transparent)]
    Link(#[from] DaemonLinkError),
    /// The daemon refused: its message and typed code.
    #[error("{message}")]
    Refused {
        message: String,
        info: Option<DaemonErrorInfo>,
    },
    #[error("the daemon's answer did not read: {0}")]
    Decode(#[source] serde_json::Error),
}

/// Read one `_eukhe/` request.
pub(super) fn parse(method: &str, params: &Value) -> Result<Extension, ExtensionError> {
    let name = method.strip_prefix(PREFIX).unwrap_or(method);
    match name {
        "budget/get" => Ok(Extension::BudgetGet),
        "budget/set" => read::<BudgetSetParams>(params).map(|params| Extension::BudgetSet {
            limits: params.limits,
            standing: params.standing,
        }),
        "budget/add" => read::<BudgetAddParams>(params).map(|params| Extension::BudgetAdd {
            amounts: params.amounts,
        }),
        "acceptance/get" => Ok(Extension::AcceptanceGet),
        "acceptance/set" => read::<AcceptanceSetParams>(params).map(Extension::AcceptanceSet),
        "undo" => Ok(Extension::Undo),
        "diff" => read::<DiffParams>(params).map(|params| Extension::Diff {
            scope: params.scope,
        }),
        "effects" => Ok(Extension::Effects),
        _ => Err(ExtensionError::UnknownMethod),
    }
}

fn read<T: DeserializeOwned>(params: &Value) -> Result<T, ExtensionError> {
    T::deserialize(params).map_err(ExtensionError::InvalidParams)
}

/// Run one request on the daemon session `session`; its result.
pub(super) async fn run(
    link: &DaemonLink,
    session: &str,
    extension: Extension,
) -> Result<Value, ExtensionError> {
    let session = session.to_string();
    let rest = Map::default;
    match extension {
        Extension::BudgetGet => encode(
            reply::<BudgetReply>(
                link,
                DaemonCommand::GetBudget {
                    id: None,
                    active_session_id: session,
                    rest: rest(),
                },
            )
            .await?,
        ),
        Extension::BudgetSet { limits, standing } => encode(
            reply::<BudgetReply>(
                link,
                DaemonCommand::SetBudget {
                    id: None,
                    active_session_id: session,
                    limits,
                    standing,
                    rest: rest(),
                },
            )
            .await?,
        ),
        Extension::BudgetAdd { amounts } => encode(
            reply::<BudgetReply>(
                link,
                DaemonCommand::AddBudget {
                    id: None,
                    active_session_id: session,
                    amounts,
                    rest: rest(),
                },
            )
            .await?,
        ),
        Extension::AcceptanceGet => acceptance(
            reply::<AcceptanceState>(
                link,
                DaemonCommand::GetAcceptance {
                    id: None,
                    active_session_id: session,
                    rest: rest(),
                },
            )
            .await?,
        ),
        Extension::AcceptanceSet(params) => acceptance(
            reply::<AcceptanceState>(
                link,
                DaemonCommand::SetAcceptance {
                    id: None,
                    active_session_id: session,
                    checks: params.checks,
                    max_returns: params.max_returns,
                    intent: params.intent,
                    rest: rest(),
                },
            )
            .await?,
        ),
        Extension::Undo => encode(
            reply::<UndoReply>(
                link,
                DaemonCommand::UndoTurn {
                    id: None,
                    active_session_id: session,
                    rest: rest(),
                },
            )
            .await?,
        ),
        Extension::Diff { scope } => encode(
            reply::<TurnDiffReply>(
                link,
                DaemonCommand::GetTurnDiff {
                    id: None,
                    active_session_id: session,
                    scope,
                    rest: rest(),
                },
            )
            .await?,
        ),
        Extension::Effects => {
            let ledgers = effect_ledgers(link, &session).await?;
            Ok(json!({ "ran": ledgers.0.effects, "unknown": ledgers.1.effects }))
        }
    }
}

/// The session's two effect ledgers: the irreversible effects that ran,
/// and the steps a restart treated as not run.
pub(super) async fn effect_ledgers(
    link: &DaemonLink,
    session: &str,
) -> Result<(RanEffectsReply, UnknownEffectsReply), ExtensionError> {
    let ran = reply::<RanEffectsReply>(
        link,
        DaemonCommand::GetRanEffects {
            id: None,
            active_session_id: session.to_string(),
            rest: Map::default(),
        },
    )
    .await?;
    let unknown = reply::<UnknownEffectsReply>(
        link,
        DaemonCommand::GetUnknownEffects {
            id: None,
            active_session_id: session.to_string(),
            rest: Map::default(),
        },
    )
    .await?;
    Ok((ran, unknown))
}

/// One command's typed answer.
pub(super) async fn reply<T: DeserializeOwned>(
    link: &DaemonLink,
    command: DaemonCommand,
) -> Result<T, ExtensionError> {
    let response = link.request(command).await?;
    if !response.success {
        return Err(ExtensionError::Refused {
            message: response
                .error
                .unwrap_or_else(|| "the daemon refused the command".to_string()),
            info: response.error_info,
        });
    }
    T::deserialize(response.data.unwrap_or(Value::Null)).map_err(ExtensionError::Decode)
}

fn encode<T: serde::Serialize>(reply: T) -> Result<Value, ExtensionError> {
    serde_json::to_value(reply).map_err(ExtensionError::Decode)
}

fn acceptance(state: AcceptanceState) -> Result<Value, ExtensionError> {
    Ok(json!({ "acceptance": encode(state)? }))
}

/// The JSON-RPC error answer of a failed request.
pub(super) fn error_response(id: &Value, method: &str, error: &ExtensionError) -> Value {
    match error {
        ExtensionError::UnknownMethod => jsonrpc::method_not_found(id, method),
        ExtensionError::InvalidParams(_) => jsonrpc::error_response(
            id,
            jsonrpc::INVALID_PARAMS,
            "Invalid params",
            Some(&json!({ "reason": error.to_string() })),
        ),
        ExtensionError::Refused { info, .. } => {
            let mut data = json!({ "details": error.to_string() });
            if let Some(code) = info
                .as_ref()
                .and_then(|info| serde_json::to_value(info).ok())
                .and_then(|info| info.get("code").cloned())
            {
                data["code"] = code;
            }
            jsonrpc::error_response(id, jsonrpc::INTERNAL_ERROR, "Internal error", Some(&data))
        }
        ExtensionError::Link(_) | ExtensionError::Decode(_) => jsonrpc::error_response(
            id,
            jsonrpc::INTERNAL_ERROR,
            "Internal error",
            Some(&json!({ "details": error.to_string() })),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::budget::LimitValue;

    #[test]
    fn requests_read_their_params_and_unknown_names_are_not_found() {
        let parsed = [
            parse("_eukhe/budget/get", &json!({ "sessionId": "s" })).ok(),
            parse(
                "_eukhe/budget/set",
                &json!({ "sessionId": "s", "limits": { "tokens": 5000, "costMicros": "unlimited" } }),
            )
            .ok(),
            parse("_eukhe/diff", &json!({ "sessionId": "s", "scope": "all" })).ok(),
            parse("_eukhe/budget/add", &json!({ "sessionId": "s" })).ok(),
        ];
        assert_eq!(
            parsed,
            [
                Some(Extension::BudgetGet),
                Some(Extension::BudgetSet {
                    limits: RunLimits {
                        tokens: Some(LimitValue::At(5000)),
                        cost_micros: Some(LimitValue::Unlimited),
                        ..RunLimits::default()
                    },
                    standing: false,
                }),
                Some(Extension::Diff {
                    scope: DiffScope::All
                }),
                None,
            ]
        );
        assert!(matches!(
            parse("_eukhe/nope", &json!({})),
            Err(ExtensionError::UnknownMethod)
        ));
    }
}
