//! Kokoro speaks a sentence, Whisper hears it back, through a WAV file.
//! Needs the model files: `EUKHE_TINY_TEST_MODELS` (a directory with
//! `kokoro/` and `whisper-base/`) and `ORT_DYLIB_PATH` (the ONNX Runtime
//! library); skips when either is unset.

use std::path::{Path, PathBuf};

use eukhe_tiny::{Engine, EngineOptions, SpeakRequest, TranscribeRequest};

use crate::audio::{read_wav, write_wav};
use crate::kokoro::KokoroEngine;
use crate::runtime::Runtime;
use crate::whisper::WhisperEngine;

#[test]
fn kokoro_speech_transcribes_back() {
    let (Some(models), Some(_)) = (
        std::env::var_os("EUKHE_TINY_TEST_MODELS"),
        std::env::var_os("ORT_DYLIB_PATH"),
    ) else {
        println!("skipped: set EUKHE_TINY_TEST_MODELS and ORT_DYLIB_PATH to run");
        return;
    };
    let models = PathBuf::from(models);
    let temp = tempfile::tempdir().expect("temp dir");
    let kokoro = installed_kokoro(&models.join("kokoro"), temp.path());
    let options = EngineOptions {
        device: "cpu".to_owned(),
        dtype: String::new(),
        runtime_library: PathBuf::new(),
    };

    let mut speaker = KokoroEngine::new(kokoro, Runtime::new(&options).expect("runtime"));
    let speech = speaker
        .speak(&SpeakRequest {
            text: "The quick brown fox jumps over the lazy dog.".to_owned(),
            voice: "af_heart".to_owned(),
            speed: 1.0,
        })
        .expect("speak");
    let wav = temp.path().join("fox.wav");
    write_wav(&wav, &speech).expect("write wav");

    let mut listener = WhisperEngine::new(
        models.join("whisper-base"),
        Runtime::new(&options).expect("runtime"),
    );
    let transcript = listener
        .transcribe(&TranscribeRequest {
            audio: read_wav(&wav).expect("read wav"),
            language: String::new(),
        })
        .expect("transcribe");
    println!(
        "{:.2} s of speech; transcript: {transcript:?}",
        f64::from(u32::try_from(speech.samples.len()).expect("length"))
            / f64::from(speech.sample_rate)
    );
    assert!(
        transcript.text.to_lowercase().contains("quick brown fox"),
        "{transcript:?}"
    );
    assert_eq!(transcript.language, "en");
}

/// The dev copy's layout made the installed one: misaki's lexicons at the
/// model directory root (the dev copy keeps them under `misaki/`).
fn installed_kokoro(source: &Path, temp: &Path) -> PathBuf {
    let installed = temp.join("kokoro");
    std::fs::create_dir(&installed).expect("kokoro dir");
    for name in ["config.json", "tokenizer.json", "onnx", "voices"] {
        std::os::unix::fs::symlink(source.join(name), installed.join(name)).expect("link");
    }
    for name in ["us_gold.json", "us_silver.json"] {
        let root = source.join(name);
        let file = if root.is_file() {
            root
        } else {
            source.join("misaki").join(name)
        };
        std::os::unix::fs::symlink(file, installed.join(name)).expect("link lexicon");
    }
    installed
}
