//! The tokenizer against ids the reference implementation (Hugging Face
//! `tokenizers` 0.23.2) gave for the same text and file, captured once.
//! The model-file tests need `EUKHE_TINY_TEST_MODELS` (a directory with
//! `lfm2.5-230m/` and `whisper-base/`) and skip when it is unset; the
//! byte-level vocabulary tests run everywhere.

use std::path::PathBuf;
use std::sync::LazyLock;

use proptest::prelude::*;
use proptest::test_runner::RngSeed;
use serde_json::json;

use super::{Tokenizer, TokenizerError, BYTE_CHARS};

/// One captured reference result.
#[derive(Debug, PartialEq, Eq)]
struct Fixture {
    text: &'static str,
    ids: Vec<u32>,
    decoded: String,
}

impl Fixture {
    fn new(text: &'static str, ids: &[u32], decoded: &str) -> Fixture {
        Fixture {
            text,
            ids: ids.to_vec(),
            decoded: decoded.to_owned(),
        }
    }
}

/// Each fixture's text encoded, and its ids decoded, by `tokenizer`.
fn actual(tokenizer: &Tokenizer, expected: &[Fixture]) -> Vec<Fixture> {
    expected
        .iter()
        .map(|fixture| Fixture {
            text: fixture.text,
            ids: tokenizer.encode(fixture.text).expect("encode"),
            decoded: tokenizer.decode(&fixture.ids),
        })
        .collect()
}

/// The model files' tokenizers (LFM2.5, Whisper), when present.
static MODEL_TOKENIZERS: LazyLock<Option<(Tokenizer, Tokenizer)>> = LazyLock::new(|| {
    let models = PathBuf::from(std::env::var_os("EUKHE_TINY_TEST_MODELS")?);
    let load = |model: &str| {
        Tokenizer::from_file(&models.join(model).join("tokenizer.json")).expect("tokenizer")
    };
    Some((load("lfm2.5-230m"), load("whisper-base")))
});

#[test]
fn lfm_tokenizer_equals_the_reference() {
    let Some((lfm, _)) = MODEL_TOKENIZERS.as_ref() else {
        println!("skipped: set EUKHE_TINY_TEST_MODELS to run");
        return;
    };
    let expected = vec![
        Fixture::new("", &[], ""),
        Fixture::new(
            "Hello, world! How's it going?",
            &[36309, 521, 2031, 510, 2213, 1090, 936, 3529, 540],
            "Hello, world! How's it going?",
        ),
        Fixture::new(
            "The build failed because a test timed out.",
            &[1098, 2461, 9579, 1929, 768, 1927, 6535, 791, 1230, 523],
            "The build failed because a test timed out.",
        ),
        Fixture::new(
            "I'M HERE, YOU'RE THERE, WE'LL SEE",
            &[
                550, 51251, 56029, 521, 37483, 516, 3277, 12807, 20243, 521, 34621, 516, 5092, 826,
                8382,
            ],
            "I'M HERE, YOU'RE THERE, WE'LL SEE",
        ),
        Fixture::new(
            "Numbers: 1234567 and 3.14159, 2026-10-17.",
            &[
                555, 20661, 535, 730, 10293, 26178, 532, 810, 730, 528, 523, 13888, 5599, 521, 730,
                1718, 531, 522, 1155, 522, 1417, 523,
            ],
            "Numbers: 1234567 and 3.14159, 2026-10-17.",
        ),
        Fixture::new(
            "Line one\nLine two\n\n\tIndented   spaces   end  ",
            &[
                11300, 1235, 708, 11300, 1547, 509, 707, 4457, 12034, 767, 12914, 767, 1764, 767,
            ],
            "Line one\nLine two\n\n\tIndented   spaces   end  ",
        ),
        Fixture::new(
            "Grüße aus München — naïve café, 東京タワー, emoji 🦀🚀",
            &[
                10706, 1142, 7017, 2613, 16986, 2180, 2116, 6838, 1124, 35499, 521, 730, 20374,
                3028, 44908, 521, 1355, 588, 3966, 23805, 609, 732, 13421, 758, 732,
            ],
            "Grüße aus München — naïve café, 東京タワー, emoji 🦀🚀",
        ),
        Fixture::new(
            "fn main() { println!(\"{x}\"); } // code",
            &[
                20960, 2120, 1797, 1196, 4969, 13657, 510, 2328, 600, 597, 38951, 4032, 2480, 2029,
                5214,
            ],
            "fn main() { println!(\"{x}\"); } // code",
        ),
        Fixture::new(
            "   leading spaces and trailing\n\n\n",
            &[767, 5845, 12914, 810, 61940, 508],
            "   leading spaces and trailing\n\n\n",
        ),
        Fixture::new(
            "<|im_start| not quite special <|endoftext",
            &[
                537, 601, 834, 36171, 601, 1014, 5787, 3429, 1428, 601, 959, 1879, 1885,
            ],
            "<|im_start| not quite special <|endoftext",
        ),
        Fixture::new(
            "<|im_start|>user\nSummarize this.<|im_end|>\n<|im_start|>assistant\n",
            &[
                6, 6423, 708, 560, 3174, 64016, 1033, 523, 7, 708, 6, 64015, 708,
            ],
            "user\nSummarize this.\nassistant\n",
        ),
        Fixture::new(
            "<think>reasoning</think> done",
            &[64400, 782, 2245, 800, 64401, 4007],
            "<think>reasoning</think> done",
        ),
        Fixture::new(
            "I use cpython, says Mathias <image>\r\nok",
            &[
                550, 1517, 781, 64014, 521, 3498, 730, 64011, 730, 396, 52600, 1063,
            ],
            "I use cpython, says Mathias \r\nok",
        ),
    ];
    assert_eq!(actual(lfm, &expected), expected);
}

#[test]
fn token_ids_and_split_characters_equal_the_reference() {
    let Some((lfm, whisper)) = MODEL_TOKENIZERS.as_ref() else {
        println!("skipped: set EUKHE_TINY_TEST_MODELS to run");
        return;
    };
    let tokens = [
        "<|im_end|>",
        "<|endoftext|>",
        "<|notimestamps|>",
        "Hello",
        "nope-not-a-token",
    ];
    assert_eq!(
        (
            tokens.map(|token| lfm.token_to_id(token)),
            tokens.map(|token| whisper.token_to_id(token)),
            lfm.encode("🦀").expect("encode"),
            whisper.encode("🦀").expect("encode"),
            // The first of the crab's three tokens: incomplete UTF-8.
            lfm.decode(&[13421]),
            whisper.decode(&[4222]),
        ),
        (
            [Some(7), Some(2), None, Some(36309), None],
            [None, Some(50257), Some(50363), Some(15947), None],
            vec![13421, 609, 732],
            vec![4222, 99, 222],
            "\u{fffd}".to_owned(),
            "\u{fffd}".to_owned(),
        )
    );
}

#[test]
fn whisper_tokenizer_equals_the_reference() {
    let Some((_, whisper)) = MODEL_TOKENIZERS.as_ref() else {
        println!("skipped: set EUKHE_TINY_TEST_MODELS to run");
        return;
    };
    let expected =
        vec![
        Fixture::new("", &[], ""),
        Fixture::new(
            "Hello, world! How's it going?",
            &[15947, 11, 1002, 0, 1012, 311, 309, 516, 30],
            "Hello, world! How's it going?",
        ),
        Fixture::new(
            "The build failed because a test timed out.",
            &[2278, 1322, 7612, 570, 257, 1500, 44696, 484, 13],
            "The build failed because a test timed out.",
        ),
        Fixture::new(
            "I'M HERE, YOU'RE THERE, WE'LL SEE",
            &[40, 6, 44, 37438, 11, 7928, 6, 3850, 40562, 11, 15813, 6, 24010, 44712],
            "I'M HERE, YOU'RE THERE, WE'LL SEE",
        ),
        Fixture::new(
            "Numbers: 1234567 and 3.14159, 2026-10-17.",
            &[
                45, 36353, 25, 34466, 8465, 22452, 293, 805, 13, 7271, 5211, 24, 11, 945, 10880,
                12, 3279, 12, 7773, 13,
            ],
            "Numbers: 1234567 and 3.14159, 2026-10-17.",
        ),
        Fixture::new(
            "Line one\nLine two\n\n\tIndented   spaces   end  ",
            &[
                43, 533, 472, 198, 43, 533, 732, 198, 198, 197, 21790, 6003, 220, 220, 7673, 220,
                220, 917, 220, 220,
            ],
            "Line one\nLine two\n\n\tIndented   spaces   end  ",
        ),
        Fixture::new(
            "Grüße aus München — naïve café, 東京タワー, emoji 🦀🚀",
            &[
                20038, 774, 11451, 3437, 35840, 2470, 3466, 1667, 15487, 303, 25118, 11, 220,
                18413, 31375, 12144, 39613, 3384, 11, 31595, 7385, 99, 222, 4222, 248, 222,
            ],
            "Grüße aus München — naïve café, 東京タワー, emoji 🦀🚀",
        ),
        Fixture::new(
            "fn main() { println!(\"{x}\"); } // code",
            &[
                69, 77, 2135, 45191, 10929, 4482, 75, 77, 46824, 1, 90, 87, 92, 17830, 26, 49870,
                29178, 3089,
            ],
            "fn main() { println!(\"{x}\"); } // code",
        ),
        Fixture::new(
            "   leading spaces and trailing\n\n\n",
            &[220, 220, 5775, 7673, 293, 944, 4883, 198, 198, 198],
            "   leading spaces and trailing\n\n\n",
        ),
        Fixture::new(
            "<|im_start| not quite special <|endoftext",
            &[27, 91, 332, 62, 24419, 91, 406, 1596, 2121, 2627, 91, 3999, 844, 3828],
            "<|im_start| not quite special <|endoftext",
        ),
        Fixture::new(
            "<|startoftranscript|><|en|><|transcribe|><|notimestamps|> Hello world.<|endoftext|>",
            &[50258, 50259, 50359, 50363, 2425, 1002, 13, 50257],
            " Hello world.",
        ),
        Fixture::new(
            "<|0.00|> timestamped<|1.20|>",
            &[50364, 49108, 36970, 50424],
            "<|0.00|> timestamped<|1.20|>",
        ),
    ];
    assert_eq!(actual(whisper, &expected), expected);
}

/// A `tokenizer.json` with every byte-level character (id = byte), three
/// merges, and added tokens: `<s>` and `<s>x` special and matched first,
/// `xy` normalized and matched only in what is left.
fn byte_level_file() -> serde_json::Value {
    let mut vocab: serde_json::Map<String, serde_json::Value> = BYTE_CHARS
        .iter()
        .enumerate()
        .map(|(byte, c)| (c.to_string(), json!(byte)))
        .collect();
    for (token, id) in [("bc", 256), ("ab", 257), ("abc", 258), ("xy", 261)] {
        vocab.insert(token.to_owned(), json!(id));
    }
    let added = |id: u32, content: &str, normalized: bool, special: bool| {
        json!({
            "id": id, "content": content, "single_word": false, "lstrip": false,
            "rstrip": false, "normalized": normalized, "special": special,
        })
    };
    json!({
        "version": "1.0",
        "truncation": null,
        "padding": null,
        "added_tokens": [
            added(259, "<s>", false, true),
            added(260, "<s>x", false, true),
            added(261, "xy", true, false),
        ],
        "normalizer": null,
        "pre_tokenizer": {"type": "ByteLevel", "add_prefix_space": false, "trim_offsets": true, "use_regex": true},
        "post_processor": null,
        "decoder": {"type": "ByteLevel", "add_prefix_space": true, "trim_offsets": true, "use_regex": true},
        "model": {
            "type": "BPE", "dropout": null, "unk_token": null,
            "continuing_subword_prefix": "", "end_of_word_suffix": "",
            "fuse_unk": false, "byte_fallback": false,
            "vocab": vocab,
            // Both merge forms; (b, c) outranks (a, b).
            "merges": [["b", "c"], "a b", ["a", "bc"]],
        },
    })
}

fn load(file: &serde_json::Value) -> Result<Tokenizer, TokenizerError> {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("tokenizer.json");
    std::fs::write(&path, file.to_string()).expect("write tokenizer.json");
    Tokenizer::from_file(&path)
}

static BYTE_LEVEL: LazyLock<Tokenizer> =
    LazyLock::new(|| load(&byte_level_file()).expect("byte-level tokenizer"));

#[test]
fn merges_go_by_rank_and_added_tokens_split_first() {
    let tokenizer = &*BYTE_LEVEL;
    let text = "abc<s>xy abd<s>x";
    let ids = tokenizer.encode(text).expect("encode");
    // "abc": (b, c) before (a, b), then (a, bc). "<s>x" is the longest
    // added token at its position; the "xy" it cuts is not matched.
    // " abd": Ġ, ab, d.
    assert_eq!(
        (
            ids.clone(),
            tokenizer.decode(&ids),
            tokenizer.decode(&[261])
        ),
        (
            vec![258, 260, 121, 32, 257, 100, 260],
            "abcy abd".to_owned(),
            "xy".to_owned()
        )
    );
}

#[test]
fn unsupported_settings_fail_to_load() {
    let with = |pointer: &str, value: serde_json::Value| {
        let mut file = byte_level_file();
        *file.pointer_mut(pointer).expect("pointer") = value;
        load(&file).err().map(|error| error.to_string())
    };
    assert_eq!(
        [
            with("/normalizer", json!({"type": "NFC"})),
            with("/model/unk_token", json!("<unk>")),
            with("/pre_tokenizer/add_prefix_space", json!(true)),
            with("/decoder", json!(null)),
            with("/added_tokens/0/lstrip", json!(true)),
            with("/model/merges/1", json!("a q")),
        ],
        [
            Some("unsupported tokenizer setting: normalizer".to_owned()),
            Some("unsupported tokenizer setting: BPE unk_token".to_owned()),
            Some("unsupported tokenizer setting: ByteLevel add_prefix_space".to_owned()),
            Some("unsupported tokenizer setting: decoder other than one ByteLevel".to_owned()),
            Some(
                "unsupported tokenizer setting: added token \"<s>\" with lstrip, rstrip or single_word"
                    .to_owned()
            ),
            Some("merge \"a q\": not two vocabulary tokens".to_owned()),
        ]
    );
}

/// Text without `<` (every special token of these files starts with it):
/// arbitrary strings, and strings over an alphabet heavy in what the
/// pre-tokenizer regexes treat apart (spaces, newlines, digits, accents,
/// apostrophes, CJK, emoji).
fn text() -> impl Strategy<Value = String> {
    let alphabet = prop::sample::select(vec![
        ' ', ' ', '\n', '\r', '\t', '\u{a0}', '\u{3000}', 'a', 'z', 'Q', 's', 't', '\'', '0', '7',
        '9', '.', ',', '!', '-', '(', '"', 'é', 'ß', 'Ü', '\u{301}', '—', '東', 'タ', '🦀', '🚀',
    ]);
    prop_oneof![
        any::<String>(),
        prop::collection::vec(alphabet, 0..64).prop_map(|chars| chars.into_iter().collect()),
    ]
    .prop_filter("no special token", |text: &String| !text.contains('<'))
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        rng_seed: RngSeed::Fixed(0x5e9b_0d17),
        ..ProptestConfig::default()
    })]

    #[test]
    fn text_round_trips(text in text()) {
        let mut decoded = vec![BYTE_LEVEL.decode(&BYTE_LEVEL.encode(&text).expect("encode"))];
        let mut expected = vec![text.clone()];
        if let Some((lfm, whisper)) = MODEL_TOKENIZERS.as_ref() {
            decoded.extend([lfm, whisper].map(|tokenizer| {
                tokenizer.decode(&tokenizer.encode(&text).expect("encode"))
            }));
            expected.extend([text.clone(), text]);
        }
        prop_assert_eq!(decoded, expected);
    }
}
