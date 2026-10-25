//! Local tiny models (docs/inference.md S9; the model is bend/tiny.bend):
//! the pinned catalog, the explicit user-run download, one shared worker
//! process per model and backend with its election (start, join, replace),
//! the client, and role-based model selection.
//!
//! Nothing here downloads on its own: [`download`] runs only from
//! `eukhe tiny-models download`. The inference itself is an [`Engine`]
//! (eukhe-tiny-onnx); this crate does not link a runtime.

mod catalog;
mod client;
mod download;
mod election;
mod engine;
mod paths;
mod protocol;
mod roles;
mod tasks;
#[cfg(test)]
mod testing;
mod worker;

pub use catalog::{
    find, install_state, installed, CatalogModel, ChatTemplate, InstallState, ModelFile, ModelKind,
    RepoKind, CATALOG,
};
pub use client::{TinyClient, TinyError};
pub use download::{download, DownloadError, Downloaded, Progress, HUGGING_FACE};
pub use engine::{Engine, EngineFactory, EngineOptions};
pub use paths::{Backend, TinyHome};
pub use protocol::{
    Audio, ChatMessage, ChatReply, ChatRequest, ChatRole, Reply, Request, Response, SpeakRequest,
    StopReason, TranscribeRequest, Transcript, WorkerFailure,
};
pub use roles::{chain, pick, Candidate, FallbackChain, Pick, Role, RoleSettings, LOCAL_PREFIX};
pub use tasks::{
    judge_request, language_name, normalize_title, parse_label, remote_reply_text, title_request,
    translate_request, translation_text, TranslationError, JUDGE_SYSTEM_PROMPT,
    TITLE_SYSTEM_PROMPT,
};
pub use worker::{launch_tag, run_worker};
