//! The ONNX engine of the tiny-model worker: text
//! generation for the catalog's text models, Whisper speech to text,
//! Kokoro text to speech. ONNX Runtime is loaded at run time
//! ([`EngineOptions::runtime_library`]); nothing is downloaded or linked
//! at build time.

mod audio;
mod kokoro;
mod runtime;
mod text;
mod tokenizer;
mod whisper;

use std::path::PathBuf;

use eukhe_tiny::{CatalogModel, Engine, EngineOptions, ModelKind, WorkerFailure};

pub use audio::{read_wav, write_wav, AudioFileError};

/// Opens the engine of an installed model (an [`eukhe_tiny::EngineFactory`]).
/// Loads nothing yet: the first request (or `load`) does.
///
/// # Errors
///
/// [`WorkerFailure::Load`] when the options are invalid.
pub fn open(
    model: &'static CatalogModel,
    dir: PathBuf,
    options: &EngineOptions,
) -> Result<Box<dyn Engine>, WorkerFailure> {
    let runtime = runtime::Runtime::new(options)?;
    match model.kind {
        ModelKind::Text { template } => Ok(Box::new(text::TextEngine::new(dir, template, runtime))),
        ModelKind::SpeechToText => Ok(Box::new(whisper::WhisperEngine::new(dir, runtime))),
        ModelKind::TextToSpeech => Ok(Box::new(kokoro::KokoroEngine::new(dir, runtime))),
    }
}
