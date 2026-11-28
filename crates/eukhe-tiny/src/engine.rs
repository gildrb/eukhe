//! The inference engine a worker serves its model with.

use std::path::PathBuf;

use crate::catalog::CatalogModel;
use crate::protocol::{
    Audio, ChatReply, ChatRequest, SpeakRequest, TranscribeRequest, Transcript, WorkerFailure,
};

/// The execution device a worker launches on: the backend runs on
/// [`Device::Cpu`]; any other word is carried as given so the launch tag
/// and the backend's error name it exactly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Device {
    /// The CPU.
    Cpu,
    /// A word the current backend does not implement (`cuda`, ...),
    /// carried unchanged.
    Other(String),
}

impl Device {
    /// The device's word, as spelled on the command line and in the
    /// launch tag.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::Cpu => "cpu",
            Self::Other(word) => word,
        }
    }

    /// Parses a device word; the empty word (an unset setting) is the
    /// CPU, as the backends have always treated it.
    #[must_use]
    pub fn parse(word: &str) -> Self {
        match word {
            "cpu" | "" => Self::Cpu,
            other => Self::Other(other.to_owned()),
        }
    }
}

impl std::fmt::Display for Device {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The settings a worker launches with; they are part of its launch tag.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EngineOptions {
    /// The execution device; [`Device::Cpu`] unless the setting names
    /// another word the backend may yet support.
    pub device: Device,
    /// The weight precision override; empty: the catalog's file set.
    pub dtype: String,
    /// The ONNX Runtime shared library; empty: `ORT_DYLIB_PATH`, else the
    /// loader's search path (`libonnxruntime.so`).
    pub runtime_library: PathBuf,
}

/// One model loaded (or loadable) in a worker process. The worker calls it
/// from one thread at a time, one request at a time.
///
/// An implementation loads its files lazily: [`Engine::load`] and the
/// first inference load them; later calls reuse them. A request of a kind
/// the model does not do fails with [`WorkerFailure::Unsupported`]; any
/// other failure is [`WorkerFailure::Load`] or
/// [`WorkerFailure::Inference`], never a panic.
pub trait Engine: Send + 'static {
    /// Loads the model's files now.
    ///
    /// # Errors
    ///
    /// [`WorkerFailure::Load`] when a file or the runtime fails to load.
    fn load(&mut self) -> Result<(), WorkerFailure>;

    /// A greedy chat completion.
    ///
    /// # Errors
    ///
    /// See the trait.
    fn chat(&mut self, request: &ChatRequest) -> Result<ChatReply, WorkerFailure>;

    /// Speech to text.
    ///
    /// # Errors
    ///
    /// See the trait.
    fn transcribe(&mut self, request: &TranscribeRequest) -> Result<Transcript, WorkerFailure>;

    /// Text to speech.
    ///
    /// # Errors
    ///
    /// See the trait.
    fn speak(&mut self, request: &SpeakRequest) -> Result<Audio, WorkerFailure>;
}

/// Opens the engine of one installed model: its catalog entry and the
/// directory its files are installed in.
pub type EngineFactory =
    fn(&'static CatalogModel, PathBuf, &EngineOptions) -> Result<Box<dyn Engine>, WorkerFailure>;
