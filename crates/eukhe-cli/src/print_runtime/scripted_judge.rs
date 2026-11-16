//! The faux-scripted judge of a headless run's final answer (the
//! `EUKHE_FAUX_SCRIPT` verification seam; the product never sets it): the
//! script's `judge` key is an array of judge replies, served in order, one
//! per judged run. A script without the key answers every request `PASS`
//! (its scripted answers state no work left); a `judge` list that ran out
//! answers no verdict.

use std::collections::VecDeque;
use std::sync::{Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_core::durable::acceptance::{Judge, JudgeReply, JudgeRequest};
use futures::future::BoxFuture;
use futures::FutureExt;

/// The replies a faux script gives the judge.
pub(super) enum ScriptedJudge {
    /// The script has no `judge` key: every answer passes.
    Passing,
    /// The script's `judge` replies not served yet.
    Scripted(Mutex<VecDeque<String>>),
}

impl ScriptedJudge {
    /// The judge of the faux script `script` (its JSON text).
    pub(super) fn from_script(script: &str) -> Self {
        let replies = serde_json::from_str::<serde_json::Value>(script)
            .ok()
            .and_then(|script| script.get("judge").cloned());
        match replies {
            Some(serde_json::Value::Array(replies)) => Self::Scripted(Mutex::new(
                replies
                    .iter()
                    .filter_map(|reply| reply.as_str().map(str::to_owned))
                    .collect(),
            )),
            Some(_) | None => Self::Passing,
        }
    }
}

impl Judge for ScriptedJudge {
    fn judge(&self, _request: JudgeRequest, _cx: &Context) -> BoxFuture<'_, JudgeReply> {
        let reply = match self {
            Self::Passing => JudgeReply::Text("PASS".to_owned()),
            Self::Scripted(replies) => replies
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .pop_front()
                .map_or_else(
                    || {
                        JudgeReply::Unavailable(
                            "the faux script's judge replies ran out".to_owned(),
                        )
                    },
                    JudgeReply::Text,
                ),
        };
        futures::future::ready(reply).boxed()
    }
}
