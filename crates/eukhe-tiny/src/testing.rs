//! The tests' support: a fake model a worker serves. [`ECHO`] is a
//! catalog entry with no files (installed once its dir exists) and
//! [`Echo`] its engine: chat echoes the last message.

use crate::catalog::{CatalogModel, ChatTemplate, ModelKind};
use crate::engine::Engine;
use crate::protocol::{
    Audio, ChatReply, ChatRequest, SpeakRequest, StopReason, TranscribeRequest, Transcript,
    WorkerFailure,
};

/// A text model with no files: installed once its dir exists.
pub static ECHO: CatalogModel = CatalogModel {
    id: "echo",
    title: "Echo (tests)",
    kind: ModelKind::Text {
        template: ChatTemplate::ChatMl,
    },
    roles: &[],
    files: &[],
};

/// The chat message that makes [`Echo`] exit its process (a worker that
/// dies mid-request).
pub const CRASH: &str = "crash";

/// The engine of [`ECHO`]: chat answers the last message's text; the
/// message [`CRASH`] exits the process with status 3.
pub struct Echo;

impl Engine for Echo {
    fn load(&mut self) -> Result<(), WorkerFailure> {
        Ok(())
    }

    fn chat(&mut self, request: &ChatRequest) -> Result<ChatReply, WorkerFailure> {
        let text = request
            .messages
            .last()
            .map(|message| message.content.clone())
            .unwrap_or_default();
        if text == CRASH {
            std::process::exit(3);
        }
        Ok(ChatReply {
            text,
            stop: StopReason::Eos,
        })
    }

    fn transcribe(&mut self, _request: &TranscribeRequest) -> Result<Transcript, WorkerFailure> {
        Err(WorkerFailure::Unsupported {
            op: "transcribe".to_owned(),
        })
    }

    fn speak(&mut self, _request: &SpeakRequest) -> Result<Audio, WorkerFailure> {
        Err(WorkerFailure::Unsupported {
            op: "speak".to_owned(),
        })
    }
}
