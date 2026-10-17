//! The text models' tokenizer: the byte-level BPE of a Hugging Face
//! `tokenizer.json`, as LFM2.5 and Whisper ship it. Reads the parts those
//! files use (added tokens, `Split`/`ByteLevel` pre-tokenizers with the
//! file's own regex, BPE vocabulary and ranked merges, `ByteLevel`
//! decoder) and rejects any other setting, so a file this code would
//! tokenize differently fails at load instead of producing wrong ids.
//! Encoding never applies the file's post-processor template: the prompts
//! carry their special tokens as text.

#[cfg(test)]
mod tests;

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::path::Path;

use aho_corasick::{AhoCorasick, MatchKind};
use fancy_regex::Regex;
use serde::Deserialize;

/// The pre-tokenizer regex of `ByteLevel` with `use_regex` (GPT-2's).
const BYTE_LEVEL_PATTERN: &str =
    r"'s|'t|'re|'ve|'m|'ll|'d| ?\p{L}+| ?\p{N}+| ?[^\s\p{L}\p{N}]+|\s+(?!\S)|\s+";

/// GPT-2's byte → character map: printable bytes stand for themselves,
/// the others take the characters from U+0100 on, in byte order.
const BYTE_CHARS: [char; 256] = byte_chars();

const fn byte_chars() -> [char; 256] {
    let mut chars = ['\0'; 256];
    let mut shifted = 0_u32;
    let mut byte = 0_u32;
    while byte < 256 {
        let printable = matches!(byte, 33..=126 | 161..=172 | 174..=255);
        let code = if printable {
            byte
        } else {
            shifted += 1;
            255 + shifted
        };
        chars[byte as usize] = match char::from_u32(code) {
            Some(c) => c,
            None => panic!("byte-level characters are scalar values"),
        };
        byte += 1;
    }
    chars
}

/// The byte a byte-level character stands for (the inverse of
/// [`BYTE_CHARS`]).
fn char_byte(c: char) -> Option<u8> {
    match u32::from(c) {
        code @ (33..=126 | 161..=172 | 174..=255) => u8::try_from(code).ok(),
        code @ 256..=288 => u8::try_from(code - 256).ok(),
        code @ 289..=322 => u8::try_from(code - 289 + 127).ok(),
        323 => Some(173),
        0..=32 | 127..=160 | 173 | 324..=u32::MAX => None,
    }
}

/// Why a `tokenizer.json` did not load, or a text did not encode.
#[derive(Debug, thiserror::Error)]
pub(crate) enum TokenizerError {
    #[error("{0}")]
    Read(#[from] std::io::Error),
    #[error("{0}")]
    Parse(#[from] serde_json::Error),
    #[error("unsupported tokenizer setting: {0}")]
    Unsupported(String),
    #[error("merge {0:?}: not two vocabulary tokens")]
    Merge(String),
    /// Boxed: the regex error is large, and every result carries this type.
    #[error("pre-tokenizer regex: {0}")]
    Pattern(Box<fancy_regex::Error>),
    #[error("added tokens: {0}")]
    AddedTokens(#[from] aho_corasick::BuildError),
}

impl From<fancy_regex::Error> for TokenizerError {
    fn from(error: fancy_regex::Error) -> Self {
        TokenizerError::Pattern(Box::new(error))
    }
}

/// A loaded byte-level BPE tokenizer.
pub(crate) struct Tokenizer {
    vocab: HashMap<String, u32>,
    tokens: HashMap<u32, String>,
    /// Token pair → (rank, merged token).
    merges: HashMap<(u32, u32), (usize, u32)>,
    ignore_merges: bool,
    steps: Vec<Step>,
    added: AddedTokens,
}

/// One pre-tokenizer step.
enum Step {
    /// Splits each piece around the regex's matches, keeping them.
    Split(Regex),
    /// Optionally splits like [`Step::Split`] with [`BYTE_LEVEL_PATTERN`],
    /// then writes each byte as its byte-level character.
    ByteLevel(Option<Regex>),
}

/// The file's added tokens: matched in the raw text before anything else
/// (`normalized: false` first, then `normalized: true` in what is left, as
/// the reference implementation does), and mapped straight to their id.
struct AddedTokens {
    raw: Option<Matcher>,
    normalized: Option<Matcher>,
    ids: HashMap<String, u32>,
    contents: HashMap<u32, String>,
    special: HashSet<String>,
}

/// Leftmost-longest matching of a set of added tokens.
struct Matcher {
    automaton: AhoCorasick,
    ids: Vec<u32>,
}

/// A part of the input: an added token or text between them.
enum Segment<'a> {
    Added(u32),
    Text(&'a str),
}

impl Matcher {
    fn new(tokens: &[(&str, u32)]) -> Result<Option<Matcher>, TokenizerError> {
        if tokens.is_empty() {
            return Ok(None);
        }
        let automaton = AhoCorasick::builder()
            .match_kind(MatchKind::LeftmostLongest)
            .build(tokens.iter().map(|(content, _)| content))?;
        Ok(Some(Matcher {
            automaton,
            ids: tokens.iter().map(|(_, id)| *id).collect(),
        }))
    }
}

impl AddedTokens {
    /// The file's added tokens; empty contents are left out, as the
    /// reference implementation does.
    fn new(tokens: &[AddedTokenFile]) -> Result<AddedTokens, TokenizerError> {
        let mut raw = Vec::new();
        let mut normalized = Vec::new();
        let mut ids = HashMap::with_capacity(tokens.len());
        let mut contents = HashMap::with_capacity(tokens.len());
        let mut special = HashSet::new();
        for token in tokens {
            if token.lstrip || token.rstrip || token.single_word {
                return Err(TokenizerError::Unsupported(format!(
                    "added token {:?} with lstrip, rstrip or single_word",
                    token.content
                )));
            }
            if token.content.is_empty() {
                continue;
            }
            if token.normalized {
                normalized.push((token.content.as_str(), token.id));
            } else {
                raw.push((token.content.as_str(), token.id));
            }
            if token.special {
                special.insert(token.content.clone());
            }
            ids.insert(token.content.clone(), token.id);
            contents.insert(token.id, token.content.clone());
        }
        Ok(AddedTokens {
            raw: Matcher::new(&raw)?,
            normalized: Matcher::new(&normalized)?,
            ids,
            contents,
            special,
        })
    }
}

/// `text` split at the added tokens `matcher` finds (one text segment
/// when there is no matcher); empty text segments are left out.
fn segments<'a>(matcher: Option<&Matcher>, text: &'a str) -> Vec<Segment<'a>> {
    let mut segments = Vec::new();
    let mut last = 0;
    if let Some(matcher) = matcher {
        for found in matcher.automaton.find_iter(text) {
            if found.start() > last {
                segments.push(Segment::Text(&text[last..found.start()]));
            }
            segments.push(Segment::Added(matcher.ids[found.pattern().as_usize()]));
            last = found.end();
        }
    }
    if last < text.len() {
        segments.push(Segment::Text(&text[last..]));
    }
    segments
}

/// Each piece split around `pattern`'s matches, matches kept as pieces of
/// their own; empty pieces are left out.
fn split_isolated(pattern: &Regex, pieces: &[String]) -> Result<Vec<String>, TokenizerError> {
    let mut split = Vec::with_capacity(pieces.len());
    for piece in pieces {
        let mut last = 0;
        for found in pattern.find_iter(piece) {
            let found = found?;
            if found.start() > last {
                split.push(piece[last..found.start()].to_owned());
            }
            if found.end() > found.start() {
                split.push(found.as_str().to_owned());
            }
            last = found.end();
        }
        if last < piece.len() {
            split.push(piece[last..].to_owned());
        }
    }
    Ok(split)
}

/// One character of a word under merge.
#[derive(Clone, Copy)]
struct Symbol {
    id: u32,
    prev: Option<usize>,
    next: Option<usize>,
    merged_away: bool,
}

impl Tokenizer {
    /// Loads a `tokenizer.json`.
    ///
    /// # Errors
    ///
    /// The file does not read or parse, a merge names a token outside the
    /// vocabulary, or it uses a setting this tokenizer does not implement.
    pub(crate) fn from_file(path: &Path) -> Result<Tokenizer, TokenizerError> {
        let file: TokenizerFile = serde_json::from_slice(&std::fs::read(path)?)?;
        let unsupported = |setting: &str| Err(TokenizerError::Unsupported(setting.to_owned()));
        if file.normalizer.is_some() {
            return unsupported("normalizer");
        }
        if file.truncation.is_some() {
            return unsupported("truncation");
        }
        if file.padding.is_some() {
            return unsupported("padding");
        }
        let byte_level_decoder = match &file.decoder {
            Some(DecoderFile::ByteLevel {}) => true,
            Some(DecoderFile::Sequence { decoders }) => {
                matches!(decoders.as_slice(), [DecoderFile::ByteLevel {}])
            }
            None => false,
        };
        if !byte_level_decoder {
            return unsupported("decoder other than one ByteLevel");
        }
        let mut steps = Vec::new();
        if let Some(pre_tokenizer) = file.pre_tokenizer {
            push_steps(pre_tokenizer, &mut steps)?;
        }
        let ModelFile::Bpe {
            vocab,
            merges,
            unk_token,
            continuing_subword_prefix,
            end_of_word_suffix,
            dropout,
            byte_fallback,
            ignore_merges,
        } = file.model;
        if unk_token.is_some() {
            return unsupported("BPE unk_token");
        }
        if continuing_subword_prefix.is_some_and(|prefix| !prefix.is_empty()) {
            return unsupported("BPE continuing_subword_prefix");
        }
        if end_of_word_suffix.is_some_and(|suffix| !suffix.is_empty()) {
            return unsupported("BPE end_of_word_suffix");
        }
        if dropout.is_some() {
            return unsupported("BPE dropout");
        }
        if byte_fallback {
            return unsupported("BPE byte_fallback");
        }
        let mut merge_ids = HashMap::with_capacity(merges.len());
        for (rank, merge) in merges.iter().enumerate() {
            let (left, right) = match merge {
                MergeFile::Pair(left, right) => (left.as_str(), right.as_str()),
                MergeFile::Joined(line) => line
                    .split_once(' ')
                    .filter(|(_, right)| !right.contains(' '))
                    .ok_or_else(|| TokenizerError::Merge(line.clone()))?,
            };
            let id = |token: &str| {
                vocab
                    .get(token)
                    .copied()
                    .ok_or_else(|| TokenizerError::Merge(format!("{left} {right}")))
            };
            merge_ids.insert(
                (id(left)?, id(right)?),
                (rank, id(&format!("{left}{right}"))?),
            );
        }
        let added = AddedTokens::new(&file.added_tokens)?;
        let tokens = vocab
            .iter()
            .map(|(token, id)| (*id, token.clone()))
            .collect();
        Ok(Tokenizer {
            vocab,
            tokens,
            merges: merge_ids,
            ignore_merges,
            steps,
            added,
        })
    }

    /// The id of a token: an added token's, else the vocabulary's.
    pub(crate) fn token_to_id(&self, token: &str) -> Option<u32> {
        self.added
            .ids
            .get(token)
            .or_else(|| self.vocab.get(token))
            .copied()
    }

    /// The ids of `text`. Special tokens written in the text become their
    /// ids; no template tokens are added.
    ///
    /// # Errors
    ///
    /// [`TokenizerError::Pattern`] when a pre-tokenizer regex gives up
    /// (its backtracking limit).
    pub(crate) fn encode(&self, text: &str) -> Result<Vec<u32>, TokenizerError> {
        let mut ids = Vec::new();
        for raw in segments(self.added.raw.as_ref(), text) {
            let text = match raw {
                Segment::Added(id) => {
                    ids.push(id);
                    continue;
                }
                Segment::Text(text) => text,
            };
            for segment in segments(self.added.normalized.as_ref(), text) {
                match segment {
                    Segment::Added(id) => ids.push(id),
                    Segment::Text(text) => {
                        let mut pieces = vec![text.to_owned()];
                        for step in &self.steps {
                            pieces = match step {
                                Step::Split(pattern) => split_isolated(pattern, &pieces)?,
                                Step::ByteLevel(pattern) => {
                                    let pieces = match pattern {
                                        Some(pattern) => split_isolated(pattern, &pieces)?,
                                        None => pieces,
                                    };
                                    pieces
                                        .iter()
                                        .map(|piece| {
                                            piece
                                                .bytes()
                                                .map(|b| BYTE_CHARS[usize::from(b)])
                                                .collect()
                                        })
                                        .collect()
                                }
                            };
                        }
                        for piece in &pieces {
                            self.merge(piece, &mut ids);
                        }
                    }
                }
            }
        }
        Ok(ids)
    }

    /// Appends the BPE ids of one pre-tokenized piece: its characters,
    /// merged lowest rank first (leftmost on a tie) until no ranked pair
    /// is left.
    fn merge(&self, piece: &str, ids: &mut Vec<u32>) {
        if self.ignore_merges {
            if let Some(id) = self.vocab.get(piece) {
                ids.push(*id);
                return;
            }
        }
        let mut symbols: Vec<Symbol> = Vec::with_capacity(piece.len());
        for (start, c) in piece.char_indices() {
            // A character outside the vocabulary has no id (no unk token):
            // it is dropped, as the reference implementation does.
            if let Some(id) = self.vocab.get(&piece[start..start + c.len_utf8()]) {
                let index = symbols.len();
                let prev = index.checked_sub(1);
                if let Some(prev) = prev {
                    symbols[prev].next = Some(index);
                }
                symbols.push(Symbol {
                    id: *id,
                    prev,
                    next: None,
                    merged_away: false,
                });
            }
        }
        let mut queue: BinaryHeap<Reverse<(usize, usize, u32)>> = symbols
            .windows(2)
            .enumerate()
            .filter_map(|(pos, pair)| {
                self.merges
                    .get(&(pair[0].id, pair[1].id))
                    .map(|(rank, merged)| Reverse((*rank, pos, *merged)))
            })
            .collect();
        while let Some(Reverse((_, pos, merged))) = queue.pop() {
            let left = symbols[pos];
            if left.merged_away {
                continue;
            }
            let Some(next) = left.next else {
                continue;
            };
            let right = symbols[next];
            if self
                .merges
                .get(&(left.id, right.id))
                .is_none_or(|(_, id)| *id != merged)
            {
                continue;
            }
            symbols[pos].id = merged;
            symbols[pos].next = right.next;
            symbols[next].merged_away = true;
            if let Some(after) = right.next {
                symbols[after].prev = Some(pos);
            }
            if let Some(prev) = left.prev {
                if let Some((rank, id)) = self.merges.get(&(symbols[prev].id, merged)) {
                    queue.push(Reverse((*rank, prev, *id)));
                }
            }
            if let Some(after) = right.next {
                if let Some((rank, id)) = self.merges.get(&(merged, symbols[after].id)) {
                    queue.push(Reverse((*rank, pos, *id)));
                }
            }
        }
        ids.extend(
            symbols
                .iter()
                .filter(|symbol| !symbol.merged_away)
                .map(|symbol| symbol.id),
        );
    }

    /// The text of `ids`, special tokens left out. Unknown ids are skipped;
    /// bytes that do not form UTF-8 become U+FFFD.
    pub(crate) fn decode(&self, ids: &[u32]) -> String {
        let mut bytes = Vec::new();
        for id in ids {
            let Some(token) = self.added.contents.get(id).or_else(|| self.tokens.get(id)) else {
                continue;
            };
            if self.added.special.contains(token) {
                continue;
            }
            let start = bytes.len();
            for c in token.chars() {
                if let Some(byte) = char_byte(c) {
                    bytes.push(byte);
                } else {
                    // Not byte-level text (an added token): its own bytes.
                    bytes.truncate(start);
                    bytes.extend_from_slice(token.as_bytes());
                    break;
                }
            }
        }
        String::from_utf8_lossy(&bytes).into_owned()
    }
}

/// Appends the steps of a pre-tokenizer (a `Sequence` in order).
fn push_steps(file: PreTokenizerFile, steps: &mut Vec<Step>) -> Result<(), TokenizerError> {
    match file {
        PreTokenizerFile::Sequence { pretokenizers } => {
            for pre_tokenizer in pretokenizers {
                push_steps(pre_tokenizer, steps)?;
            }
        }
        PreTokenizerFile::Split {
            pattern: PatternFile::Regex(pattern),
            behavior: SplitBehavior::Isolated,
            invert,
        } => {
            if invert {
                return Err(TokenizerError::Unsupported("inverted Split".to_owned()));
            }
            steps.push(Step::Split(Regex::new(&pattern)?));
        }
        PreTokenizerFile::ByteLevel {
            add_prefix_space,
            use_regex,
        } => {
            if add_prefix_space {
                return Err(TokenizerError::Unsupported(
                    "ByteLevel add_prefix_space".to_owned(),
                ));
            }
            let pattern = if use_regex {
                Some(Regex::new(BYTE_LEVEL_PATTERN)?)
            } else {
                None
            };
            steps.push(Step::ByteLevel(pattern));
        }
    }
    Ok(())
}

/// The parts of `tokenizer.json` this tokenizer reads. `post_processor`
/// is not read: encoding adds no template tokens.
#[derive(Deserialize)]
struct TokenizerFile {
    added_tokens: Vec<AddedTokenFile>,
    normalizer: Option<serde_json::Value>,
    pre_tokenizer: Option<PreTokenizerFile>,
    model: ModelFile,
    decoder: Option<DecoderFile>,
    truncation: Option<serde_json::Value>,
    padding: Option<serde_json::Value>,
}

#[derive(Deserialize)]
#[allow(clippy::struct_excessive_bools)] // The file's own flags.
struct AddedTokenFile {
    id: u32,
    content: String,
    single_word: bool,
    lstrip: bool,
    rstrip: bool,
    normalized: bool,
    special: bool,
}

#[derive(Deserialize)]
#[serde(tag = "type")]
enum PreTokenizerFile {
    Sequence {
        pretokenizers: Vec<PreTokenizerFile>,
    },
    Split {
        pattern: PatternFile,
        behavior: SplitBehavior,
        invert: bool,
    },
    ByteLevel {
        add_prefix_space: bool,
        use_regex: bool,
    },
}

#[derive(Deserialize)]
enum PatternFile {
    Regex(String),
}

#[derive(Deserialize)]
enum SplitBehavior {
    Isolated,
}

#[derive(Deserialize)]
#[serde(tag = "type")]
enum ModelFile {
    #[serde(rename = "BPE")]
    Bpe {
        vocab: HashMap<String, u32>,
        merges: Vec<MergeFile>,
        unk_token: Option<String>,
        continuing_subword_prefix: Option<String>,
        end_of_word_suffix: Option<String>,
        dropout: Option<f32>,
        #[serde(default)]
        byte_fallback: bool,
        #[serde(default)]
        ignore_merges: bool,
    },
}

/// A merge: `["a", "b"]` or the older `"a b"`.
#[derive(Deserialize)]
#[serde(untagged)]
enum MergeFile {
    Pair(String, String),
    Joined(String),
}

#[derive(Deserialize)]
#[serde(tag = "type")]
enum DecoderFile {
    Sequence { decoders: Vec<DecoderFile> },
    ByteLevel {},
}
