//! The pinned catalog of local models. Each file names its Hugging Face
//! repository, the commit it is pinned to, its size and its sha256; the
//! download verifies both before it installs the file. Nothing here
//! fetches: `eukhe tiny-models download` is the only path that downloads.

use std::path::Path;

use crate::paths::TinyHome;
use crate::roles::Role;

/// A Hugging Face repository kind (it changes the download URL).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RepoKind {
    Model,
    Dataset,
}

/// One pinned file of a model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModelFile {
    /// `owner/name` on Hugging Face.
    pub repo: &'static str,
    pub repo_kind: RepoKind,
    /// The full commit hash the file is pinned to.
    pub revision: &'static str,
    /// The path in the repository; also the path under the install dir.
    pub path: &'static str,
    pub size: u64,
    /// Lowercase hex.
    pub sha256: &'static str,
}

/// The text models' prompt format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChatTemplate {
    /// `<|startoftext|>` then `<|im_start|>role\n…<|im_end|>\n` turns (LFM2).
    ChatMl,
}

/// What a model does, and the engine family that runs it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModelKind {
    /// A decoder LLM in ONNX with a KV (and conv) cache.
    Text { template: ChatTemplate },
    /// Whisper: encoder + decoder ONNX, 16 kHz log-mel input.
    SpeechToText,
    /// Kokoro-82M: phonemes + voice style to 24 kHz audio.
    TextToSpeech,
}

/// One catalog entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CatalogModel {
    /// The id after `local/` in a role selector (`lfm2.5-230m`).
    pub id: &'static str,
    pub title: &'static str,
    pub kind: ModelKind,
    /// The roles the model suits, in the order of the built-in priority.
    pub roles: &'static [Role],
    pub files: &'static [ModelFile],
}

impl CatalogModel {
    /// The sum of the file sizes.
    #[must_use]
    pub fn size(&self) -> u64 {
        self.files.iter().map(|file| file.size).sum()
    }
}

/// The catalog, in built-in priority order within each role.
pub static CATALOG: &[CatalogModel] = &[
    CatalogModel {
        id: "lfm2.5-230m",
        title: "LFM2.5 230M (q4)",
        kind: ModelKind::Text {
            template: ChatTemplate::ChatMl,
        },
        roles: &[Role::Tiny, Role::Judge, Role::Translate],
        files: LFM2_5_230M_FILES,
    },
    CatalogModel {
        id: "lfm2.5-350m",
        title: "LFM2.5 350M (q4)",
        kind: ModelKind::Text {
            template: ChatTemplate::ChatMl,
        },
        roles: &[Role::Tiny, Role::Judge, Role::Translate],
        files: LFM2_5_350M_FILES,
    },
    CatalogModel {
        id: "whisper-base",
        title: "Whisper base (quantized)",
        kind: ModelKind::SpeechToText,
        roles: &[Role::Dictation],
        files: WHISPER_BASE_FILES,
    },
    CatalogModel {
        id: "whisper-small",
        title: "Whisper small (quantized)",
        kind: ModelKind::SpeechToText,
        roles: &[Role::Dictation],
        files: WHISPER_SMALL_FILES,
    },
    CatalogModel {
        id: "kokoro",
        title: "Kokoro 82M v1.0 (quantized) with the misaki US lexicon",
        kind: ModelKind::TextToSpeech,
        roles: &[Role::Speech],
        files: KOKORO_FILES,
    },
];

/// One pinned repository commit; the files below share it.
struct Source {
    repo: &'static str,
    repo_kind: RepoKind,
    revision: &'static str,
}

impl Source {
    const fn file(&self, path: &'static str, size: u64, sha256: &'static str) -> ModelFile {
        ModelFile {
            repo: self.repo,
            repo_kind: self.repo_kind,
            revision: self.revision,
            path,
            size,
            sha256,
        }
    }
}

/// LiquidAI/LFM2.5-230M-ONNX.
const LFM_230M: Source = Source {
    repo: "LiquidAI/LFM2.5-230M-ONNX",
    repo_kind: RepoKind::Model,
    revision: "c6f46e4e3f885ebcad164d14059a49f90e27eb4d",
};

/// onnx-community/LFM2.5-350M-ONNX.
const LFM_350M: Source = Source {
    repo: "onnx-community/LFM2.5-350M-ONNX",
    repo_kind: RepoKind::Model,
    revision: "7dd4999565b0342c381ba90a3d8fc467d6df19c4",
};

/// onnx-community/whisper-base.
const WHISPER_BASE: Source = Source {
    repo: "onnx-community/whisper-base",
    repo_kind: RepoKind::Model,
    revision: "1846881b6b3a3024392c1eea3ad983695bc23925",
};

/// onnx-community/whisper-small.
const WHISPER_SMALL: Source = Source {
    repo: "onnx-community/whisper-small",
    repo_kind: RepoKind::Model,
    revision: "36050c46d777d46dc4b5f43f6d90574fc38f8732",
};

/// onnx-community/Kokoro-82M-v1.0-ONNX.
const KOKORO: Source = Source {
    repo: "onnx-community/Kokoro-82M-v1.0-ONNX",
    repo_kind: RepoKind::Model,
    revision: "1939ad2a8e416c0acfeecc08a694d14ef25f2231",
};

/// hexgrad/misaki.
const MISAKI: Source = Source {
    repo: "hexgrad/misaki",
    repo_kind: RepoKind::Dataset,
    revision: "7a6093fd11124188077f2dc16397cc465466d59a",
};

static LFM2_5_230M_FILES: &[ModelFile] = &[
    LFM_230M.file(
        "config.json",
        1_668,
        "c09361ba08a21a464011710ade1bab1dbe7a9c43eadb70cae04ebb4825ff8233",
    ),
    LFM_230M.file(
        "generation_config.json",
        131,
        "85fa3172f3838eefa602843e3d97fbf532aeb585e0d7fb869dcd17c268e77f45",
    ),
    LFM_230M.file(
        "tokenizer.json",
        4_733_389,
        "df1d8d5ec5d091b460562ffd545e4a5e91d17d4a0db7ebe733be34ed374377bd",
    ),
    LFM_230M.file(
        "tokenizer_config.json",
        5_347,
        "c46e3f5715c73f7ae9beeeebad8f7187fd647d2de352c3cd01fe250c88d2f960",
    ),
    LFM_230M.file(
        "onnx/model_q4.onnx",
        154_010,
        "82a442c44d3d143432edff57984a4e7e8da65179d3a960a170d294aed8c5dd8d",
    ),
    LFM_230M.file(
        "onnx/model_q4.onnx_data",
        211_111_936,
        "b51a4580a88a2cd0486032cfdaf8694b09359abca5a97df8deb0a314ea6e5b34",
    ),
];

static LFM2_5_350M_FILES: &[ModelFile] = &[
    LFM_350M.file(
        "config.json",
        1_443,
        "544d8d604bacf4cb89383c49c9a54621afa26a6741f3f55fd8b840ca1d640419",
    ),
    LFM_350M.file(
        "generation_config.json",
        136,
        "94bfac0e1c207691baf4e172389a8efb114f8b60eb3a5c07a2f418aefa8f8bb6",
    ),
    LFM_350M.file(
        "tokenizer.json",
        3_297_793,
        "29d43b4be8e8a896fefd7cd836ca6d6b4eedd249f823866ce0453b368e646f49",
    ),
    LFM_350M.file(
        "tokenizer_config.json",
        3_825,
        "e70cd070c2696bf1b0f1ad303c34502753670cca6f844637821cb1c37e6bea8d",
    ),
    LFM_350M.file(
        "onnx/model_q4.onnx",
        183_442,
        "d1a705712e93aafaba1346b32245fa59e7857a46e2272003c0e8c524977e0de8",
    ),
    LFM_350M.file(
        "onnx/model_q4.onnx_data",
        293_629_952,
        "71ec6ad38a4c463dcb3dba671d06a1d9861be3a23e51290d818b95c0b7d2a5db",
    ),
];

static WHISPER_BASE_FILES: &[ModelFile] = &[
    WHISPER_BASE.file(
        "config.json",
        2_243,
        "f4d0608f7d918166da7edb3e188de5ef1bfe70d9802e785d271fd88111e9cf4b",
    ),
    WHISPER_BASE.file(
        "generation_config.json",
        3_832,
        "61070cf8de25b1e9256e8e102ded49d8d24a8369ed36ef84fdf21549e68125a0",
    ),
    WHISPER_BASE.file(
        "preprocessor_config.json",
        339,
        "a6a76d28c93edb273669eb9e0b0636a2bddbb1272c3261e47b7ca6dfdbac1b8d",
    ),
    WHISPER_BASE.file(
        "tokenizer.json",
        2_480_466,
        "27fc476bfe7f17299480be2273fc0608e4d5a99aba2ab5dec5374b4482d1a566",
    ),
    WHISPER_BASE.file(
        "onnx/encoder_model_quantized.onnx",
        23_201_314,
        "5862993336bf33acd23736071aae2b32261d3b1b2f37780194460d4ef974dd46",
    ),
    WHISPER_BASE.file(
        "onnx/decoder_model_quantized.onnx",
        53_310_178,
        "c859636f4463dd5a9ea752546c6c7badeb48ab3e22b340cafef08a15552fcb2e",
    ),
];

static WHISPER_SMALL_FILES: &[ModelFile] = &[
    WHISPER_SMALL.file(
        "config.json",
        2_227,
        "457854d452f17661e197d74aee12b8e74fb75ba30ebfaa7426d0d61ea1e08a18",
    ),
    WHISPER_SMALL.file(
        "generation_config.json",
        3_893,
        "f538b28220c6a6d6f1af1458d4141cacb4ef4963df3de98a19490440c412ddf0",
    ),
    WHISPER_SMALL.file(
        "preprocessor_config.json",
        339,
        "a6a76d28c93edb273669eb9e0b0636a2bddbb1272c3261e47b7ca6dfdbac1b8d",
    ),
    WHISPER_SMALL.file(
        "tokenizer.json",
        2_480_466,
        "27fc476bfe7f17299480be2273fc0608e4d5a99aba2ab5dec5374b4482d1a566",
    ),
    WHISPER_SMALL.file(
        "onnx/encoder_model_quantized.onnx",
        92_326_160,
        "a43a83f3c5361cd591cfa7c36f14b43cf7cb22f47a415cc14a8d557be800fa92",
    ),
    WHISPER_SMALL.file(
        "onnx/decoder_model_quantized.onnx",
        155_989_346,
        "0486afa8eb464bf2210d07aca0cb3f5d91d3f2f01cbe47f9f1e6ff9122abaaf6",
    ),
];

static KOKORO_FILES: &[ModelFile] = &[
    KOKORO.file(
        "config.json",
        44,
        "df34b4f930b23447cd4dc410fabfb42eb3f24e803e6c3f97d618fb359380a36f",
    ),
    KOKORO.file(
        "tokenizer.json",
        3_497,
        "77a02c8e164413299b4b4c403b14f8e0e1c1b727db4d46a09d6327b861060a34",
    ),
    KOKORO.file(
        "onnx/model_quantized.onnx",
        92_361_116,
        "fbae9257e1e05ffc727e951ef9b9c98418e6d79f1c9b6b13bd59f5c9028a1478",
    ),
    KOKORO.file(
        "voices/af_heart.bin",
        522_240,
        "d583ccff3cdca2f7fae535cb998ac07e9fcb90f09737b9a41fa2734ec44a8f0b",
    ),
    KOKORO.file(
        "voices/af_bella.bin",
        522_240,
        "f69d836209b78eb8c66e75e3cda491e26ea838a3674257e9d4e5703cbaf55c8b",
    ),
    KOKORO.file(
        "voices/af_nicole.bin",
        522_240,
        "cd2191ab31b914ed7b318416b0e4440fdf392ddad9106a060819aa600a64f59a",
    ),
    KOKORO.file(
        "voices/af_aoede.bin",
        522_240,
        "4a004c33430762e2461eedb2013fad808ef4ab3121f5300f554476caf58d8361",
    ),
    KOKORO.file(
        "voices/af_kore.bin",
        522_240,
        "9be5221b6a941c04b561959b8ff0b06e809444dcc4ab7e75a7b23606f691819e",
    ),
    KOKORO.file(
        "voices/af_sarah.bin",
        522_240,
        "4409fbc125afabacc615d94db5398d847006a737b0247d6892b7a9a0007a2f0a",
    ),
    KOKORO.file(
        "voices/am_michael.bin",
        522_240,
        "1d1f21dd8da39c30705cd4c75d039d265e9bc4a2a93ed09bc9e1b1225eb95ba1",
    ),
    KOKORO.file(
        "voices/am_fenrir.bin",
        522_240,
        "c27989f741f7ee34d273a39d8a595cc0837d35f5ced9a29b7cc162614616df43",
    ),
    KOKORO.file(
        "voices/am_puck.bin",
        522_240,
        "fcf73c989033e9233e0b98713eca600c8c74dcc1614b37009d5450ff4a2274a0",
    ),
    KOKORO.file(
        "voices/bf_emma.bin",
        522_240,
        "669fe0647f9dd04fcab92f1439a40eeb4c8b4ab1f82e4996fe3d918ce4a63b73",
    ),
    KOKORO.file(
        "voices/bm_george.bin",
        522_240,
        "c4b235a4c1f2cd3b939fed08b899ce9385638b763f7b73a59616c4fc9bd6c9bc",
    ),
    KOKORO.file(
        "voices/bm_fable.bin",
        522_240,
        "f889083196807b4adb15e9204252165f503b8d33d3982e681c52443c49d798f1",
    ),
    MISAKI.file(
        "us_gold.json",
        3_001_196,
        "8507f89840f0813b10cf584740942f58e9cc9ad3660e24088b442ab0a6b126be",
    ),
    MISAKI.file(
        "us_silver.json",
        3_105_352,
        "ea0e1abca0c9b18fb0d3402034633a337154a3153e9a9f49f97d668c908e140c",
    ),
];

/// What of a model is on disk (`eukhe tiny-models list`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstallState {
    /// Every file is present with its pinned size.
    Installed,
    /// No install dir.
    Missing,
    /// An install dir whose files do not all match the pin (an older pin or
    /// a damaged install); a download replaces it whole.
    Partial {
        /// Pinned paths that are absent (or not regular files).
        missing: Vec<&'static str>,
        /// Pinned paths present with another size.
        wrong_size: Vec<&'static str>,
    },
}

/// The install state of `model` under `home`: sizes only; the full sha256
/// check happens at download, before the install.
#[must_use]
pub fn install_state(home: &TinyHome, model: &CatalogModel) -> InstallState {
    files_state(&home.model_dir(model.id), model.files)
}

/// The install state of `files` in the install dir `dir`.
pub(crate) fn files_state(dir: &Path, files: &[ModelFile]) -> InstallState {
    if !dir.is_dir() {
        return InstallState::Missing;
    }
    let mut missing = Vec::new();
    let mut wrong_size = Vec::new();
    for file in files {
        match std::fs::metadata(dir.join(file.path)) {
            Ok(meta) if meta.is_file() && meta.len() == file.size => {}
            Ok(meta) if meta.is_file() => wrong_size.push(file.path),
            Ok(_) | Err(_) => missing.push(file.path),
        }
    }
    if missing.is_empty() && wrong_size.is_empty() {
        InstallState::Installed
    } else {
        InstallState::Partial {
            missing,
            wrong_size,
        }
    }
}

/// Whether every file of `model` is present with its pinned size.
#[must_use]
pub fn installed(home: &TinyHome, model: &CatalogModel) -> bool {
    install_state(home, model) == InstallState::Installed
}

/// The catalog entry of `id`.
#[must_use]
pub fn find(id: &str) -> Option<&'static CatalogModel> {
    CATALOG.iter().find(|model| model.id == id)
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_SOURCE: Source = Source {
        repo: "test/repo",
        repo_kind: RepoKind::Model,
        revision: "0000000000000000000000000000000000000000",
    };

    static TEST_FILES: &[ModelFile] = &[
        TEST_SOURCE.file("a.json", 2, "unused"),
        TEST_SOURCE.file("onnx/b.onnx", 3, "unused"),
    ];

    static TEST_MODEL: CatalogModel = CatalogModel {
        id: "test-model",
        title: "Test model",
        kind: ModelKind::SpeechToText,
        roles: &[Role::Dictation],
        files: TEST_FILES,
    };

    #[test]
    fn install_state_reports_missing_partial_and_installed() {
        let temp = tempfile::tempdir().unwrap();
        let home = TinyHome::under(temp.path());
        let dir = home.model_dir(TEST_MODEL.id);

        assert_eq!(install_state(&home, &TEST_MODEL), InstallState::Missing);

        std::fs::create_dir_all(dir.join("onnx")).unwrap();
        std::fs::write(dir.join("onnx/b.onnx"), b"toolong").unwrap();
        assert_eq!(
            install_state(&home, &TEST_MODEL),
            InstallState::Partial {
                missing: vec!["a.json"],
                wrong_size: vec!["onnx/b.onnx"],
            }
        );
        assert!(!installed(&home, &TEST_MODEL));

        std::fs::write(dir.join("a.json"), b"{}").unwrap();
        std::fs::write(dir.join("onnx/b.onnx"), b"abc").unwrap();
        assert_eq!(install_state(&home, &TEST_MODEL), InstallState::Installed);
        assert!(installed(&home, &TEST_MODEL));
    }
}
