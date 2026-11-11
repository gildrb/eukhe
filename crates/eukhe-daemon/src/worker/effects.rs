//! The exactly-once effects surface: `get_unknown_effects` reads the main
//! conversation's ledger of effects whose outcome a restart could not tell
//! (the `eukhe.effects` document, `eukhe_durable::harness::effects`), and
//! `resolve_unknown_effect` settles one open effect in a session commit,
//! after a client looked at the world. Attached clients follow the ledger
//! through `unknown_effects_update` (the event bridge's effects watch) and
//! the attach snapshot's `unknownEffects`.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::effects::{read_unknown_effects, resolve_unknown};
use eukhe_types::effects::{EffectResolution, ResolvedEffectReply, UnknownEffectsReply};
use serde::Deserialize as _;
use serde_json::Value;

use super::{response_failure, response_success, Worker};
use crate::protocol::DaemonResponse;

impl Worker {
    /// `get_unknown_effects`: the ledger, oldest first, open and resolved.
    #[tracing::instrument(skip(self))]
    pub(crate) async fn handle_get_unknown_effects(&self) -> DaemonResponse {
        const COMMAND: &str = "get_unknown_effects";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let read = async {
            let main = hosted.main()?;
            read_unknown_effects(hosted.harness(), main.id(), &BACKGROUND_CONTEXT).await
        };
        match read.await {
            Ok(effects) => response_success(
                None,
                COMMAND,
                Some(serde_json::to_value(UnknownEffectsReply { effects }).unwrap_or(Value::Null)),
            ),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }

    /// `resolve_unknown_effect`: settle the open effect `effectId` as
    /// `resolution` (`ran` or `notRun`) and answer it as resolved. An id
    /// the ledger holds no open effect of (never noted, or settled
    /// already) changes nothing and fails.
    #[tracing::instrument(skip(self, payload))]
    pub(crate) async fn handle_resolve_unknown_effect(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "resolve_unknown_effect";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(effect_id) = payload
            .get("effectId")
            .and_then(Value::as_str)
            .filter(|id| !id.is_empty())
        else {
            return response_failure(
                None,
                COMMAND,
                "resolve_unknown_effect requires an effectId",
                None,
            );
        };
        let Some(resolution) = payload
            .get("resolution")
            .and_then(|resolution| EffectResolution::deserialize(resolution).ok())
        else {
            return response_failure(
                None,
                COMMAND,
                "resolve_unknown_effect requires resolution \"ran\" or \"notRun\"",
                None,
            );
        };
        let id = effect_id.to_owned();
        let resolved = async {
            let conversation_id = hosted.main()?.id();
            hosted
                .harness()
                .commit(
                    move |tx| async move {
                        resolve_unknown(&tx, conversation_id, &id, resolution).await
                    },
                    &BACKGROUND_CONTEXT,
                )
                .await
        };
        match resolved.await {
            Ok(Some(effect)) => response_success(
                None,
                COMMAND,
                Some(serde_json::to_value(ResolvedEffectReply { effect }).unwrap_or(Value::Null)),
            ),
            Ok(None) => response_failure(
                None,
                COMMAND,
                &format!("No open unknown effect: {effect_id}"),
                None,
            ),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }
}
