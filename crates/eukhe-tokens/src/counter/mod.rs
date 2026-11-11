//! Model-aware token counting (port of omp `packages/agent/src/tokenizer.ts`
//! onto eukhe's message types).
//!
//! A [`Tokenizer`] is fixed to one reading model: its tokenizer family (the
//! catalog policy of [`crate::resolve_model_tokenizer`]; a model without one
//! counts in `o200k_base`, never a characters-per-token guess), its image
//! pricing rule and how it bills a replayed thinking block. Text counts are
//! exact; an image is priced by the reader's image rule from the pixel size
//! in its header. Counts measure message content, not the wire frame around
//! it: the provider-reported usage of a turn covers that, so transcript
//! sizes anchor on the newest usage and count only the messages after it.
//!
//! Counting follows what eukhe's replay (`eukhe-ai` `transform_messages`)
//! actually sends the reader: an aborted or failed turn is dropped; another
//! model's thinking becomes plain text and its redacted thinking is dropped;
//! the reader's own signed thinking is billed as the reader bills it (Claude:
//! the turn's reported output, the reasoning the signature rebuilds;
//! everyone else: the signature's own tokens, or a native `OpenAI` Responses
//! reasoning item at the turn's reported reasoning tokens).

mod view;

use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use rayon::prelude::*;

use crate::{
    Encoding, ImageTokenization, ModelRef, ModelTokenizer, ThinkingReplayTokens, base64_image_size,
    billed_image_tokens, resolve_image_tokenization, resolve_model_tokenizer,
    resolve_thinking_replay_tokens,
};

pub use view::{AssistantTurn, MessageParts, Part, ai_assistant, ai_blocks};

/// When at least this many fragments of one count miss the cache, they
/// count in parallel (omp `countTokensNat`: the native batch path takes 16
/// or more fragments).
const PARALLEL_BATCH_MIN: usize = 16;

/// Fragments one cache generation holds before it ages out (two
/// generations: a hit in the old one moves to the new one). Sized so a
/// long transcript's messages (each a few fragments) stay cached between
/// the counts of two requests: ~3 MB per generation.
const CACHE_GENERATION: usize = 65_536;

/// The model whose replayed reasoning a [`Tokenizer`] prices: a turn of
/// this exact model on this wire and host replays natively.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Reader {
    api: String,
    provider: String,
    id: String,
}

impl Reader {
    fn reads_natively(&self, turn: &AssistantTurn<'_>) -> bool {
        turn.api == self.api && turn.provider == self.provider && turn.model == self.id
    }

    /// The reader replays `OpenAI` Responses history: a reasoning item goes
    /// back as itself and bills at its reported reasoning tokens.
    fn replays_responses_items(&self) -> bool {
        matches!(
            self.api.as_str(),
            "openai-responses" | "openai-codex-responses" | "azure-openai-responses"
        )
    }
}

/// Verdict of [`Tokenizer::check_token_budget`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TokenBudgetCheck {
    /// Whether the text fits the budget.
    pub fits: bool,
    /// The count behind the verdict: the exact count when `exact`, else the
    /// UTF-8 byte length, a hard upper bound (every token consumes at least
    /// one byte).
    pub tokens: u64,
    /// Whether `tokens` is the exact tokenizer count.
    pub exact: bool,
}

/// Exact fragment counts keyed by a hash of the text, in two generations.
#[derive(Default)]
struct FragmentCache {
    current: HashMap<(u64, usize), u32>,
    previous: HashMap<(u64, usize), u32>,
}

impl FragmentCache {
    fn key(text: &str) -> (u64, usize) {
        let mut hasher = DefaultHasher::new();
        text.hash(&mut hasher);
        (hasher.finish(), text.len())
    }

    fn get(&mut self, key: (u64, usize)) -> Option<u32> {
        if let Some(tokens) = self.current.get(&key) {
            return Some(*tokens);
        }
        let tokens = self.previous.remove(&key)?;
        self.insert(key, tokens);
        Some(tokens)
    }

    fn insert(&mut self, key: (u64, usize), tokens: u32) {
        if self.current.len() >= CACHE_GENERATION {
            self.previous = std::mem::take(&mut self.current);
        }
        self.current.insert(key, tokens);
    }
}

/// Model-aware local token counter; see the module docs. Immutable apart
/// from its count cache, so one instance per reading model is shared
/// process-wide ([`Tokenizer::for_model`]).
pub struct Tokenizer {
    encoding: Encoding,
    image_rule: Option<ImageTokenization>,
    thinking_replay: ThinkingReplayTokens,
    reader: Option<Reader>,
    cache: Mutex<FragmentCache>,
}

impl std::fmt::Debug for Tokenizer {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Tokenizer")
            .field("encoding", &self.encoding)
            .field("image_rule", &self.image_rule)
            .field("thinking_replay", &self.thinking_replay)
            .field("reader", &self.reader)
            .finish_non_exhaustive()
    }
}

/// Process-wide tokenizers by reading model, so their caches are shared.
static TOKENIZERS: LazyLock<Mutex<HashMap<Reader, Arc<Tokenizer>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

impl Tokenizer {
    /// The shared tokenizer of `model`: its catalog tokenizer family
    /// (`o200k_base` when the catalog names none), image rule and thinking
    /// replay pricing.
    #[must_use]
    pub fn for_model(model: ModelRef<'_>) -> Arc<Tokenizer> {
        let reader = Reader {
            api: model.api.to_owned(),
            provider: model.provider.to_owned(),
            id: model.id.to_owned(),
        };
        let mut tokenizers = TOKENIZERS.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(tokenizer) = tokenizers.get(&reader) {
            return Arc::clone(tokenizer);
        }
        let tokenizer = Arc::new(Tokenizer {
            encoding: resolve_model_tokenizer(model.id, model.provider)
                .map_or(Encoding::O200kBase, ModelTokenizer::encoding),
            image_rule: resolve_image_tokenization(model),
            thinking_replay: resolve_thinking_replay_tokens(model),
            reader: Some(reader.clone()),
            cache: Mutex::new(FragmentCache::default()),
        });
        tokenizers.insert(reader, Arc::clone(&tokenizer));
        tokenizer
    }

    /// A tokenizer for no particular model: `o200k_base`, the generic
    /// image rule, signatures billed at their own tokens, every replayed
    /// payload charged.
    #[must_use]
    pub fn unknown_model() -> Arc<Tokenizer> {
        static UNKNOWN: LazyLock<Arc<Tokenizer>> = LazyLock::new(|| {
            Arc::new(Tokenizer {
                encoding: Encoding::O200kBase,
                image_rule: None,
                thinking_replay: ThinkingReplayTokens::Signature,
                reader: None,
                cache: Mutex::new(FragmentCache::default()),
            })
        });
        Arc::clone(&UNKNOWN)
    }

    /// The tokenizer family this counter uses.
    #[must_use]
    pub fn encoding(&self) -> Encoding {
        self.encoding
    }

    /// Exact tokens of `text`.
    #[must_use]
    pub fn count_text(&self, text: &str) -> u64 {
        self.count_fragments(&[text])
    }

    /// The sum of the exact counts of independent fragments (not of their
    /// concatenation). Every fragment goes through the count cache; when
    /// [`PARALLEL_BATCH_MIN`] or more of them miss it, the misses count in
    /// parallel.
    #[must_use]
    pub fn count_fragments<S: AsRef<str>>(&self, fragments: &[S]) -> u64 {
        let keyed: Vec<((u64, usize), &str)> = fragments
            .iter()
            .map(AsRef::as_ref)
            .filter(|text| !text.is_empty())
            .map(|text| (FragmentCache::key(text), text))
            .collect();
        let mut total = 0;
        let mut misses = Vec::new();
        {
            let mut cache = self.cache.lock().unwrap_or_else(PoisonError::into_inner);
            for (key, text) in keyed {
                match cache.get(key) {
                    Some(tokens) => total += u64::from(tokens),
                    None => misses.push((key, text)),
                }
            }
        }
        if misses.is_empty() {
            return total;
        }
        let counted: Vec<u32> = if misses.len() >= PARALLEL_BATCH_MIN {
            misses
                .par_iter()
                .map(|(_, text)| self.encoding.count(text))
                .collect()
        } else {
            misses
                .iter()
                .map(|(_, text)| self.encoding.count(text))
                .collect()
        };
        let mut cache = self.cache.lock().unwrap_or_else(PoisonError::into_inner);
        for ((key, _), tokens) in misses.iter().zip(&counted) {
            cache.insert(*key, *tokens);
            total += u64::from(*tokens);
        }
        total
    }

    /// Whether `fragments` fit `budget` tokens, cheapest first: UTF-8 bytes
    /// bound the token count from above, so fragments whose bytes fit are
    /// answered without tokenizing (upper bound); only text past that bound
    /// pays for the exact count (strict). omp `checkTokenBudget`.
    #[must_use]
    pub fn check_token_budget<S: AsRef<str>>(
        &self,
        fragments: &[S],
        budget: u64,
    ) -> TokenBudgetCheck {
        let bound: u64 = fragments
            .iter()
            .map(|fragment| fragment.as_ref().len() as u64)
            .sum();
        if bound <= budget {
            return TokenBudgetCheck {
                fits: true,
                tokens: bound,
                exact: false,
            };
        }
        let tokens = self.count_fragments(fragments);
        TokenBudgetCheck {
            fits: tokens <= budget,
            tokens,
            exact: true,
        }
    }

    /// Input tokens of one base64-encoded image under the reader's image
    /// rule (the generic one without), sized from the image header; an
    /// unreadable header charges the rule's most expensive size.
    #[must_use]
    pub fn image_tokens(&self, base64: &str) -> u64 {
        billed_image_tokens(base64_image_size(base64), None, self.image_rule.as_ref())
    }

    /// Tokens `message` adds to a request to the reading model.
    #[must_use]
    pub fn count_message(&self, message: &MessageParts<'_>) -> u64 {
        match message {
            MessageParts::Plain(parts) => self.count_parts(parts),
            MessageParts::Assistant(turn) => self.count_assistant(turn),
        }
    }

    /// Tokens of the parts of a non-assistant message (or of any content a
    /// caller assembled): text exactly, images by the reader's image rule.
    #[must_use]
    pub fn count_parts(&self, parts: &[Part<'_>]) -> u64 {
        let mut measure = Measure::default();
        for part in parts {
            measure.part(self, part);
        }
        measure.total(self)
    }

    fn count_assistant(&self, turn: &AssistantTurn<'_>) -> u64 {
        // eukhe's replay drops an aborted or failed turn whole.
        if turn.dropped {
            return 0;
        }
        let native = self
            .reader
            .as_ref()
            .is_none_or(|reader| reader.reads_natively(turn));
        let responses_items = native
            && self
                .reader
                .as_ref()
                .is_some_and(Reader::replays_responses_items);
        let signatures_priced = self.thinking_replay == ThinkingReplayTokens::Signature;
        let mut measure = Measure::default();
        let mut signed_reasoning = false;
        let mut responses_reasoning = false;
        for part in &turn.parts {
            match part {
                Part::Thinking {
                    text,
                    signature,
                    redacted,
                } => {
                    let signature = signature.filter(|signature| !signature.is_empty());
                    if !native {
                        // Another model's redacted thinking is dropped; its
                        // visible thinking replays as text.
                        if !*redacted && !text.trim().is_empty() {
                            measure.text(text);
                        }
                        continue;
                    }
                    if !*redacted && !text.is_empty() {
                        measure.text(text);
                    }
                    let Some(signature) = signature else {
                        continue;
                    };
                    signed_reasoning = true;
                    if !signatures_priced {
                        continue;
                    }
                    if responses_items && turn.reasoning.is_some() && is_reasoning_item(signature) {
                        responses_reasoning = true;
                    } else {
                        measure.text(signature);
                    }
                }
                Part::Text(_) | Part::Image(_) | Part::ToolCall { .. } => {
                    measure.part(self, part);
                }
            }
        }
        if responses_reasoning {
            measure.extra += turn.reasoning.unwrap_or(0);
        }
        let visible = measure.total(self);
        // The reader rebuilds its own signed reasoning from the signature and
        // bills it at the turn's output size.
        if signed_reasoning && !signatures_priced && self.reader.is_some() {
            return visible.max(turn.output);
        }
        visible
    }
}

/// Whether a thinking signature is a serialized `OpenAI` Responses
/// reasoning item (`{"type":"reasoning",...}`), which replays as itself.
fn is_reasoning_item(signature: &str) -> bool {
    serde_json::from_str::<serde_json::Value>(signature)
        .is_ok_and(|item| item.get("type").and_then(serde_json::Value::as_str) == Some("reasoning"))
}

/// Text fragments and fixed-price extras of one message.
#[derive(Default)]
struct Measure<'a> {
    fragments: Vec<&'a str>,
    extra: u64,
}

impl<'a> Measure<'a> {
    fn text(&mut self, text: &'a str) {
        if !text.is_empty() {
            self.fragments.push(text);
        }
    }

    fn part(&mut self, tokenizer: &Tokenizer, part: &'a Part<'_>) {
        match part {
            Part::Text(text) | Part::Thinking { text, .. } => self.text(text),
            Part::Image(data) => self.extra += tokenizer.image_tokens(data),
            Part::ToolCall { name, arguments } => {
                self.text(name);
                self.text(arguments);
            }
        }
    }

    fn total(&self, tokenizer: &Tokenizer) -> u64 {
        self.extra + tokenizer.count_fragments(&self.fragments)
    }
}

#[cfg(test)]
mod tests;
