//! Whisper speech to text: the encoder over the log-mel features of each
//! 30 s window, then greedy decoding with the full-sequence decoder (no KV
//! cache) under the `<|startoftranscript|><|lang|><|transcribe|>
//! <|notimestamps|>` prompt.

mod mel;
#[cfg(test)]
mod round_trip_tests;

use std::collections::BTreeMap;
use std::fmt::Display;
use std::path::{Path, PathBuf};

use eukhe_tiny::{
    Audio, ChatReply, ChatRequest, Engine, SpeakRequest, TranscribeRequest, Transcript,
    WorkerFailure,
};
use ort::session::Session;
use ort::value::{DynValue, TensorRef};
use serde::de::DeserializeOwned;
use serde::Deserialize;

use crate::audio::resample;
use crate::runtime::Runtime;
use crate::tokenizer::Tokenizer;

/// The tokens one window may generate after the prompt.
const MAX_NEW_TOKENS: usize = 224;

/// A Whisper model: its files are loaded on first use.
pub(crate) struct WhisperEngine {
    dir: PathBuf,
    runtime: Runtime,
    model: Option<Whisper>,
}

/// The loaded model.
struct Whisper {
    encoder: Session,
    decoder: Session,
    tokenizer: Tokenizer,
    tokens: SpecialTokens,
    filters: Vec<[f32; mel::FREQUENCY_BINS]>,
}

/// The ids of `generation_config.json` decoding uses.
#[derive(Deserialize)]
struct SpecialTokens {
    decoder_start_token_id: i64,
    eos_token_id: i64,
    no_timestamps_token_id: i64,
    /// `<|en|>` → id.
    lang_to_id: BTreeMap<String, i64>,
    task_to_id: BTreeMap<String, i64>,
    #[serde(default)]
    suppress_tokens: Vec<usize>,
    #[serde(default)]
    begin_suppress_tokens: Vec<usize>,
}

/// The feature extractor settings of `preprocessor_config.json` this
/// engine's fixed spectrogram must match.
#[derive(Debug, PartialEq, Eq, Deserialize)]
struct FeatureSettings {
    feature_size: usize,
    sampling_rate: u32,
    n_samples: usize,
    nb_max_frames: usize,
}

impl WhisperEngine {
    pub(crate) fn new(dir: PathBuf, runtime: Runtime) -> WhisperEngine {
        WhisperEngine {
            dir,
            runtime,
            model: None,
        }
    }

    /// The model, loaded now when it is not yet.
    fn model(&mut self) -> Result<&mut Whisper, WorkerFailure> {
        if self.model.is_none() {
            let features: FeatureSettings = read_json(&self.dir.join("preprocessor_config.json"))?;
            let expected = FeatureSettings {
                feature_size: mel::MEL_BANDS,
                sampling_rate: mel::SAMPLE_RATE,
                n_samples: mel::WINDOW_SAMPLES,
                nb_max_frames: mel::FRAMES,
            };
            if features != expected {
                return Err(WorkerFailure::Load {
                    message: format!(
                        "{}: unsupported feature extractor {features:?} (expected {expected:?})",
                        self.dir.join("preprocessor_config.json").display()
                    ),
                });
            }
            let tokenizer_path = self.dir.join("tokenizer.json");
            let tokenizer =
                Tokenizer::from_file(&tokenizer_path).map_err(|error| WorkerFailure::Load {
                    message: format!("{}: {error}", tokenizer_path.display()),
                })?;
            let tokens = read_json(&self.dir.join("generation_config.json"))?;
            let encoder = self
                .runtime
                .session(&self.dir.join("onnx/encoder_model_quantized.onnx"))?;
            let decoder = self
                .runtime
                .session(&self.dir.join("onnx/decoder_model_quantized.onnx"))?;
            self.model = Some(Whisper {
                encoder,
                decoder,
                tokenizer,
                tokens,
                filters: mel::mel_filters(),
            });
        }
        self.model.as_mut().ok_or_else(|| WorkerFailure::Load {
            message: format!("{}: the model did not load", self.dir.display()),
        })
    }
}

impl Engine for WhisperEngine {
    fn load(&mut self) -> Result<(), WorkerFailure> {
        self.model().map(|_| ())
    }

    fn chat(&mut self, _request: &ChatRequest) -> Result<ChatReply, WorkerFailure> {
        Err(WorkerFailure::Unsupported {
            op: "chat".to_owned(),
        })
    }

    fn transcribe(&mut self, request: &TranscribeRequest) -> Result<Transcript, WorkerFailure> {
        let model = self.model()?;
        let mut language = if request.language.is_empty() {
            None
        } else {
            let token = format!("<|{}|>", request.language);
            let id = model
                .tokens
                .lang_to_id
                .get(&token)
                .copied()
                .ok_or_else(|| WorkerFailure::Inference {
                    message: format!("Whisper does not know the language `{}`", request.language),
                })?;
            Some((request.language.clone(), id))
        };
        let audio = resample(&request.audio, mel::SAMPLE_RATE);
        let mut texts = Vec::new();
        for window in audio.samples.chunks(mel::WINDOW_SAMPLES) {
            let hidden = model.encode(window)?;
            let language_id = if let Some((_, id)) = &language {
                *id
            } else {
                let detected = model.detect_language(&hidden)?;
                let id = detected.1;
                language = Some(detected);
                id
            };
            let text = model.decode(&hidden, language_id)?;
            if !text.is_empty() {
                texts.push(text);
            }
        }
        Ok(Transcript {
            text: texts.join(" "),
            language: language.map(|(code, _)| code).unwrap_or_default(),
        })
    }

    fn speak(&mut self, _request: &SpeakRequest) -> Result<Audio, WorkerFailure> {
        Err(WorkerFailure::Unsupported {
            op: "speak".to_owned(),
        })
    }
}

impl Whisper {
    /// The encoder's hidden states of one window (16 kHz, ≤ 30 s).
    fn encode(&mut self, window: &[f32]) -> Result<DynValue, WorkerFailure> {
        let features = mel::log_mel(window, &self.filters);
        let input =
            TensorRef::from_array_view(([1, mel::MEL_BANDS, mel::FRAMES], features.as_slice()))
                .map_err(inference)?;
        let mut outputs = self
            .encoder
            .run(ort::inputs!["input_features" => input])
            .map_err(inference)?;
        outputs
            .remove("last_hidden_state")
            .ok_or_else(|| inference("the encoder has no `last_hidden_state` output"))
    }

    /// The most likely language (code and token) after
    /// `<|startoftranscript|>`.
    fn detect_language(&mut self, hidden: &DynValue) -> Result<(String, i64), WorkerFailure> {
        let logits = self.next_logits(hidden, &[self.tokens.decoder_start_token_id])?;
        self.tokens
            .lang_to_id
            .iter()
            .filter_map(|(token, id)| {
                let score = logits.get(usize::try_from(*id).ok()?)?;
                Some((token, *id, *score))
            })
            .max_by(|left, right| left.2.total_cmp(&right.2))
            .map(|(token, id, _)| {
                let code = token.trim_start_matches("<|").trim_end_matches("|>");
                (code.to_owned(), id)
            })
            .ok_or_else(|| inference("generation_config.json lists no languages"))
    }

    /// The greedy transcript of one encoded window, special tokens
    /// skipped, trimmed.
    fn decode(&mut self, hidden: &DynValue, language: i64) -> Result<String, WorkerFailure> {
        let transcribe = self
            .tokens
            .task_to_id
            .get("transcribe")
            .copied()
            .ok_or_else(|| inference("generation_config.json has no `transcribe` task"))?;
        let mut ids = vec![
            self.tokens.decoder_start_token_id,
            language,
            transcribe,
            self.tokens.no_timestamps_token_id,
        ];
        let prompt = ids.len();
        // Timestamp tokens follow `<|notimestamps|>`; this prompt asks for none.
        let timestamps =
            usize::try_from(self.tokens.no_timestamps_token_id + 1).map_err(inference)?;
        while ids.len() - prompt < MAX_NEW_TOKENS {
            let mut logits = self.next_logits(hidden, &ids)?;
            let first = ids.len() == prompt;
            let begin: &[usize] = if first {
                &self.tokens.begin_suppress_tokens
            } else {
                &[]
            };
            for id in self.tokens.suppress_tokens.iter().chain(begin) {
                if let Some(logit) = logits.get_mut(*id) {
                    *logit = f32::NEG_INFINITY;
                }
            }
            for logit in logits.iter_mut().skip(timestamps) {
                *logit = f32::NEG_INFINITY;
            }
            let next = logits
                .iter()
                .enumerate()
                .max_by(|left, right| left.1.total_cmp(right.1))
                .map(|(id, _)| id)
                .ok_or_else(|| inference("the decoder returned no logits"))?;
            let next = i64::try_from(next).map_err(inference)?;
            if next == self.tokens.eos_token_id {
                break;
            }
            ids.push(next);
        }
        let generated = ids[prompt..]
            .iter()
            .map(|id| u32::try_from(*id))
            .collect::<Result<Vec<u32>, _>>()
            .map_err(inference)?;
        let text = self.tokenizer.decode(&generated);
        Ok(text.trim().to_owned())
    }

    /// The decoder's logits for the token after `ids`.
    fn next_logits(&mut self, hidden: &DynValue, ids: &[i64]) -> Result<Vec<f32>, WorkerFailure> {
        let input_ids = TensorRef::from_array_view(([1, ids.len()], ids)).map_err(inference)?;
        let outputs = self
            .decoder
            .run(ort::inputs![
                "input_ids" => input_ids,
                "encoder_hidden_states" => hidden,
            ])
            .map_err(inference)?;
        let logits = outputs
            .get("logits")
            .ok_or_else(|| inference("the decoder has no `logits` output"))?;
        let (_, logits) = logits.try_extract_tensor::<f32>().map_err(inference)?;
        let vocabulary = logits.len() / ids.len();
        Ok(logits[logits.len() - vocabulary..].to_vec())
    }
}

fn inference(error: impl Display) -> WorkerFailure {
    WorkerFailure::Inference {
        message: error.to_string(),
    }
}

fn read_json<T: DeserializeOwned>(path: &Path) -> Result<T, WorkerFailure> {
    let load = |error: &dyn Display| WorkerFailure::Load {
        message: format!("{}: {error}", path.display()),
    };
    let text = std::fs::read(path).map_err(|error| load(&error))?;
    serde_json::from_slice(&text).map_err(|error| load(&error))
}
