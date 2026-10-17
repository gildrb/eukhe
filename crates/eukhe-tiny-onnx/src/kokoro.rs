//! Kokoro text to speech, as kokoro-js runs it: English text to phonemes
//! (misaki lexicons, [`g2p`]), phonemes to vocabulary ids in chunks of at
//! most 510 on sentence boundaries, each chunk voiced with the voice's
//! style row for its length, the waveforms concatenated (24 kHz).

mod g2p;
mod numbers;

use std::collections::HashMap;
use std::fmt::Display;
use std::path::PathBuf;

use eukhe_tiny::{
    Audio, ChatReply, ChatRequest, Engine, SpeakRequest, TranscribeRequest, Transcript,
    WorkerFailure,
};
use ort::session::Session;
use ort::value::TensorRef;
use serde::Deserialize;

use crate::runtime::Runtime;
use g2p::Lexicon;

/// Kokoro's output rate.
const SAMPLE_RATE: u32 = 24_000;
/// The phoneme ids of one inference (the model's context is 512 with the
/// two pads).
const MAX_TOKENS: usize = 510;
/// The length of one style vector; a voice file holds one per token count.
const STYLE_SIZE: usize = 256;
/// The voice an empty request voice means.
const DEFAULT_VOICE: &str = "af_heart";
/// The padding id at both ends of the ids (`$`).
const PAD: i64 = 0;

/// A Kokoro model: its files are loaded on first use, each voice on its
/// first request.
pub(crate) struct KokoroEngine {
    dir: PathBuf,
    runtime: Runtime,
    model: Option<Kokoro>,
}

/// The loaded model.
struct Kokoro {
    session: Session,
    /// Phoneme → id, without the pad.
    vocabulary: HashMap<char, i64>,
    lexicon: Lexicon,
    voices: Voices,
}

/// The style tables of the voices requested so far.
struct Voices {
    dir: PathBuf,
    loaded: HashMap<String, Vec<f32>>,
}

/// The part of `tokenizer.json` Kokoro needs.
#[derive(Deserialize)]
struct TokenizerFile {
    model: TokenizerModel,
}

#[derive(Deserialize)]
struct TokenizerModel {
    vocab: HashMap<String, i64>,
}

impl KokoroEngine {
    pub(crate) fn new(dir: PathBuf, runtime: Runtime) -> KokoroEngine {
        KokoroEngine {
            dir,
            runtime,
            model: None,
        }
    }

    /// The model, loaded now when it is not yet.
    fn model(&mut self) -> Result<&mut Kokoro, WorkerFailure> {
        if self.model.is_none() {
            let tokenizer_path = self.dir.join("tokenizer.json");
            let load = |error: &dyn Display| WorkerFailure::Load {
                message: format!("{}: {error}", tokenizer_path.display()),
            };
            let bytes = std::fs::read(&tokenizer_path).map_err(|error| load(&error))?;
            let tokenizer: TokenizerFile =
                serde_json::from_slice(&bytes).map_err(|error| load(&error))?;
            let vocabulary = tokenizer
                .model
                .vocab
                .into_iter()
                .filter(|(_, id)| *id != PAD)
                .filter_map(|(symbol, id)| {
                    let mut chars = symbol.chars();
                    match (chars.next(), chars.next()) {
                        (Some(phoneme), None) => Some((phoneme, id)),
                        (Some(_), Some(_)) | (None, _) => None,
                    }
                })
                .collect();
            let lexicon = Lexicon::load(&self.dir)?;
            let session = self
                .runtime
                .session(&self.dir.join("onnx/model_quantized.onnx"))?;
            self.model = Some(Kokoro {
                session,
                vocabulary,
                lexicon,
                voices: Voices {
                    dir: self.dir.join("voices"),
                    loaded: HashMap::new(),
                },
            });
        }
        self.model.as_mut().ok_or_else(|| WorkerFailure::Load {
            message: format!("{}: the model did not load", self.dir.display()),
        })
    }
}

impl Engine for KokoroEngine {
    fn load(&mut self) -> Result<(), WorkerFailure> {
        self.model().map(|_| ())
    }

    fn chat(&mut self, _request: &ChatRequest) -> Result<ChatReply, WorkerFailure> {
        Err(WorkerFailure::Unsupported {
            op: "chat".to_owned(),
        })
    }

    fn transcribe(&mut self, _request: &TranscribeRequest) -> Result<Transcript, WorkerFailure> {
        Err(WorkerFailure::Unsupported {
            op: "transcribe".to_owned(),
        })
    }

    fn speak(&mut self, request: &SpeakRequest) -> Result<Audio, WorkerFailure> {
        if !(request.speed.is_finite() && request.speed > 0.0) {
            return Err(inference(format!(
                "speed {} is not a positive rate",
                request.speed
            )));
        }
        let voice = if request.voice.is_empty() {
            DEFAULT_VOICE
        } else {
            request.voice.as_str()
        };
        let model = self.model()?;
        let styles = model.voices.get(voice)?;
        let sentences: Vec<Vec<i64>> = model
            .lexicon
            .sentences(&request.text)
            .iter()
            .map(|sentence| {
                sentence
                    .chars()
                    .filter_map(|phoneme| model.vocabulary.get(&phoneme).copied())
                    .collect()
            })
            .collect();
        let space = model
            .vocabulary
            .get(&' ')
            .copied()
            .ok_or_else(|| WorkerFailure::Load {
                message: "tokenizer.json has no space phoneme".to_owned(),
            })?;
        let speed = [request.speed];
        let mut samples = Vec::new();
        for chunk in chunks(sentences, space) {
            let row = chunk.len().min(MAX_TOKENS - 1) * STYLE_SIZE;
            let style = &styles[row..row + STYLE_SIZE];
            let mut ids = Vec::with_capacity(chunk.len() + 2);
            ids.push(PAD);
            ids.extend(chunk);
            ids.push(PAD);
            let outputs = model
                .session
                .run(ort::inputs![
                    "input_ids" => TensorRef::from_array_view(([1, ids.len()], ids.as_slice())).map_err(inference)?,
                    "style" => TensorRef::from_array_view(([1, STYLE_SIZE], style)).map_err(inference)?,
                    "speed" => TensorRef::from_array_view(([1], &speed[..])).map_err(inference)?,
                ])
                .map_err(inference)?;
            let waveform = outputs
                .get("waveform")
                .ok_or_else(|| inference("the model has no `waveform` output"))?;
            let (_, waveform) = waveform.try_extract_tensor::<f32>().map_err(inference)?;
            samples.extend_from_slice(waveform);
        }
        Ok(Audio {
            sample_rate: SAMPLE_RATE,
            samples,
        })
    }
}

impl Voices {
    /// The `[510, 256]` style table of `voice` (`voices/<voice>.bin`, f32
    /// little-endian).
    fn get(&mut self, voice: &str) -> Result<&[f32], WorkerFailure> {
        if !self.loaded.contains_key(voice) {
            let path = self.dir.join(format!("{voice}.bin"));
            let named = !voice.is_empty()
                && voice
                    .chars()
                    .all(|letter| letter.is_ascii_alphanumeric() || letter == '_');
            if !named || !path.is_file() {
                let mut available: Vec<String> = std::fs::read_dir(&self.dir)
                    .into_iter()
                    .flatten()
                    .filter_map(|entry| {
                        let path = entry.ok()?.path();
                        match path.extension() {
                            Some(extension) if extension == "bin" => {
                                Some(path.file_stem()?.to_string_lossy().into_owned())
                            }
                            Some(_) | None => None,
                        }
                    })
                    .collect();
                available.sort();
                return Err(inference(format!(
                    "unknown voice `{voice}`; available: {}",
                    available.join(", ")
                )));
            }
            let bytes = std::fs::read(&path).map_err(|error| WorkerFailure::Load {
                message: format!("{}: {error}", path.display()),
            })?;
            let expected = MAX_TOKENS * STYLE_SIZE * size_of::<f32>();
            if bytes.len() != expected {
                return Err(WorkerFailure::Load {
                    message: format!(
                        "{}: {} bytes, expected {expected}",
                        path.display(),
                        bytes.len()
                    ),
                });
            }
            let styles = bytes
                .as_chunks::<4>()
                .0
                .iter()
                .map(|value| f32::from_le_bytes(*value))
                .collect();
            self.loaded.insert(voice.to_owned(), styles);
        }
        self.loaded
            .get(voice)
            .map(Vec::as_slice)
            .ok_or_else(|| inference(format!("voice `{voice}` did not load")))
    }
}

/// The sentences' ids grouped into chunks of at most [`MAX_TOKENS`],
/// sentences joined by `space`; a longer sentence splits at its last space
/// that fits, else at the limit.
fn chunks(sentences: Vec<Vec<i64>>, space: i64) -> Vec<Vec<i64>> {
    let mut chunks = Vec::new();
    let mut current: Vec<i64> = Vec::new();
    for mut sentence in sentences {
        while !sentence.is_empty() {
            let piece = if sentence.len() <= MAX_TOKENS {
                std::mem::take(&mut sentence)
            } else {
                match sentence[..=MAX_TOKENS].iter().rposition(|id| *id == space) {
                    Some(at) if at > 0 => {
                        let rest = sentence.split_off(at + 1);
                        sentence.pop();
                        std::mem::replace(&mut sentence, rest)
                    }
                    Some(_) | None => {
                        let rest = sentence.split_off(MAX_TOKENS);
                        std::mem::replace(&mut sentence, rest)
                    }
                }
            };
            if !current.is_empty() && current.len() + 1 + piece.len() > MAX_TOKENS {
                chunks.push(std::mem::take(&mut current));
            }
            if !current.is_empty() {
                current.push(space);
            }
            current.extend(piece);
        }
    }
    if !current.is_empty() {
        chunks.push(current);
    }
    chunks
}

fn inference(error: impl Display) -> WorkerFailure {
    WorkerFailure::Inference {
        message: error.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chunks_fill_up_to_the_limit_on_sentence_and_word_boundaries() {
        const SPACE: i64 = 16;
        let long: Vec<i64> = (0..600)
            .map(|index| if index == 300 { SPACE } else { 1 })
            .collect();
        let unbroken = vec![2; 520];
        let grouped = chunks(
            vec![vec![3; 200], vec![4; 300], vec![5; 20], long, unbroken],
            SPACE,
        );
        let mut first = vec![3; 200];
        first.push(SPACE);
        first.extend(vec![4; 300]);
        let mut second = vec![5; 20];
        second.push(SPACE);
        second.extend(vec![1; 300]);
        assert_eq!(
            grouped,
            vec![first, second, vec![1; 299], vec![2; 510], vec![2; 10]]
        );
    }

    #[test]
    fn unknown_voice_names_the_installed_ones() {
        let dir = tempfile::tempdir().expect("temp dir");
        for name in ["bf_emma.bin", "af_heart.bin", "notes.txt"] {
            std::fs::write(dir.path().join(name), b"").expect("voice file");
        }
        let mut voices = Voices {
            dir: dir.path().to_path_buf(),
            loaded: HashMap::new(),
        };
        assert_eq!(
            voices.get("af_nobody").map(<[f32]>::len),
            Err(WorkerFailure::Inference {
                message: "unknown voice `af_nobody`; available: af_heart, bf_emma".to_owned(),
            })
        );
    }
}
