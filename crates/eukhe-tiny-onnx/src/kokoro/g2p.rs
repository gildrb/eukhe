//! English grapheme to phoneme conversion for Kokoro, after misaki's
//! `en.py` (<https://github.com/hexgrad/misaki>) without its POS tagger and
//! neural fallback: the gold then silver lexicon, misaki's special cases of
//! function words, its `-s`/`-ed`/`-ing` stemming, numbers spelled as
//! words, and unknown words spelled letter by letter.

use std::collections::HashMap;
use std::fmt::Display;
use std::path::Path;

use eukhe_tiny::WorkerFailure;
use serde::Deserialize;

use super::numbers::{Number, NumberForm};

/// misaki's `VOWELS`: a following word that starts with one makes `the`
/// read `ði`.
const VOWELS: &str = "AIOQWYaiuæɑɒɔəɛɜɪʊʌᵻ";
/// misaki's `CONSONANTS`.
const CONSONANTS: &str = "bdfhjklmnpstvwzðŋɡɹɾʃʒʤʧθ";
/// misaki's `US_TAUS`: a `t` after one of these flaps (`ɾ`).
const TAUS: &str = "AIOWYiuæɑəɛɪɹʊʌ";
/// The punctuation Kokoro's vocabulary knows; it passes through as is.
const PUNCTUATION: &str = ";:,.!?—…\"“”()";
/// Punctuation that does not break the context a word sees after it.
const QUOTES: &str = "\"“”()";
/// Punctuation that ends a sentence.
const SENTENCE_ENDS: &str = ".!?…";
const PRIMARY_STRESS: char = 'ˈ';
const SECONDARY_STRESS: char = 'ˌ';

/// The misaki lexicons (`us_gold.json`, `us_silver.json`): word →
/// phonemes.
pub(crate) struct Lexicon {
    gold: HashMap<String, String>,
    silver: HashMap<String, String>,
}

/// One lexicon value: phonemes, or phonemes by part of speech.
#[derive(Deserialize)]
#[serde(untagged)]
enum Entry {
    Phonemes(String),
    Tagged(HashMap<String, Option<String>>),
}

/// One unit of the input text and whether whitespace followed it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Piece {
    token: Token,
    space_after: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Word(String),
    Number(Number),
    Punctuation(char),
}

impl Token {
    /// Whether the token is spoken (not punctuation).
    fn sounds(&self) -> bool {
        match self {
            Token::Word(_) | Token::Number(_) => true,
            Token::Punctuation(_) => false,
        }
    }
}

impl Lexicon {
    /// Reads `us_gold.json` and `us_silver.json` of the model directory.
    pub(crate) fn load(dir: &Path) -> Result<Lexicon, WorkerFailure> {
        Ok(Lexicon {
            gold: read_lexicon(&dir.join("us_gold.json"))?,
            silver: read_lexicon(&dir.join("us_silver.json"))?,
        })
    }

    /// The phonemes of each sentence of `text`, words separated by spaces,
    /// punctuation kept.
    pub(crate) fn sentences(&self, text: &str) -> Vec<String> {
        let pieces = pieces(text);
        let mut phonemes = vec![String::new(); pieces.len()];
        // misaki's `future_vowel`: whether the next word starts with a
        // vowel; `None` at the end or before punctuation.
        let mut next_vowel = None;
        for (piece, slot) in pieces.iter().zip(&mut phonemes).rev() {
            match &piece.token {
                Token::Word(word) => {
                    *slot = self.word(word, next_vowel);
                    next_vowel = starts_with_vowel(slot).or(next_vowel);
                }
                Token::Number(number) => {
                    let words: Vec<String> = number
                        .words()
                        .into_iter()
                        .map(|word| self.word(word, None))
                        .filter(|phonemes| !phonemes.is_empty())
                        .collect();
                    *slot = words.join(" ");
                    next_vowel = starts_with_vowel(slot).or(next_vowel);
                }
                Token::Punctuation(mark) => {
                    slot.push(*mark);
                    if !QUOTES.contains(*mark) {
                        next_vowel = None;
                    }
                }
            }
        }
        let mut sentences = Vec::new();
        let mut current = String::new();
        let last = pieces.len().saturating_sub(1);
        for (index, (piece, phonemes)) in pieces.iter().zip(&phonemes).enumerate() {
            current.push_str(phonemes);
            if piece.space_after && !current.is_empty() && !current.ends_with(' ') {
                current.push(' ');
            }
            if let Token::Punctuation(mark) = piece.token {
                if SENTENCE_ENDS.contains(mark) && (piece.space_after || index == last) {
                    push_sentence(&mut sentences, &mut current);
                }
            }
        }
        push_sentence(&mut sentences, &mut current);
        sentences
    }

    /// The phonemes of one word; empty when it has none.
    fn word(&self, word: &str, next_vowel: Option<bool>) -> String {
        let special = match word {
            "the" | "The" | "THE" => Some(if next_vowel == Some(true) {
                "ði"
            } else {
                "ðə"
            }),
            "a" | "A" => Some("ɐ"),
            "an" | "An" | "AN" => Some("ɐn"),
            "I" => Some("ˌI"),
            "to" | "To" | "TO" => match next_vowel {
                Some(true) => Some("tʊ"),
                Some(false) => Some("tə"),
                None => None,
            },
            _ => None,
        };
        if let Some(phonemes) = special {
            return phonemes.to_owned();
        }
        if let Some(phonemes) = self.lookup(word) {
            return phonemes.to_owned();
        }
        let lower = word.to_lowercase();
        self.stem_s(&lower)
            .or_else(|| self.stem_ed(&lower))
            .or_else(|| self.stem_ing(&lower))
            .unwrap_or_else(|| self.spell(word))
    }

    /// The lexicon's phonemes of `word` as written, lowercased, or
    /// capitalized: gold first, then silver.
    fn lookup(&self, word: &str) -> Option<&str> {
        let lower = word.to_lowercase();
        let mut letters = lower.chars();
        let capital: String = letters.next().map_or_else(String::new, |first| {
            first.to_uppercase().chain(letters).collect()
        });
        let keys = [word, lower.as_str(), capital.as_str()];
        [&self.gold, &self.silver]
            .into_iter()
            .find_map(|lexicon| keys.iter().find_map(|key| lexicon.get(*key)))
            .map(String::as_str)
    }

    /// misaki `stem_s`: plurals, possessives, third person.
    fn stem_s(&self, word: &str) -> Option<String> {
        if word.len() < 3 || !word.ends_with('s') {
            return None;
        }
        let without_s = &word[..word.len() - 1];
        let stem = if !word.ends_with("ss") && self.lookup(without_s).is_some() {
            without_s.to_owned()
        } else if (word.ends_with("'s")
            || (word.len() > 4 && word.ends_with("es") && !word.ends_with("ies")))
            && self.lookup(&word[..word.len() - 2]).is_some()
        {
            word[..word.len() - 2].to_owned()
        } else if word.len() > 4 && word.ends_with("ies") {
            format!("{}y", &word[..word.len() - 3])
        } else {
            return None;
        };
        let stem = self.lookup(&stem)?;
        let last = stem.chars().next_back()?;
        Some(if "ptkfθ".contains(last) {
            format!("{stem}s")
        } else if "szʃʒʧʤ".contains(last) {
            format!("{stem}ᵻz")
        } else {
            format!("{stem}z")
        })
    }

    /// misaki `stem_ed`: past tenses.
    fn stem_ed(&self, word: &str) -> Option<String> {
        if word.len() < 4 || !word.ends_with('d') {
            return None;
        }
        let without_d = &word[..word.len() - 1];
        let stem = if !word.ends_with("dd") && self.lookup(without_d).is_some() {
            without_d
        } else if word.len() > 4 && word.ends_with("ed") && !word.ends_with("eed") {
            &word[..word.len() - 2]
        } else {
            return None;
        };
        let stem = self.lookup(stem)?;
        let mut tail = stem.chars().rev();
        let last = tail.next()?;
        Some(if "pkfθʃsʧ".contains(last) {
            format!("{stem}t")
        } else if last == 'd' {
            format!("{stem}ᵻd")
        } else if last != 't' {
            format!("{stem}d")
        } else if tail.next().is_some_and(|before| TAUS.contains(before)) {
            format!("{}ɾᵻd", &stem[..stem.len() - last.len_utf8()])
        } else {
            format!("{stem}ᵻd")
        })
    }

    /// misaki `stem_ing`: present participles.
    fn stem_ing(&self, word: &str) -> Option<String> {
        if word.len() < 5 || !word.ends_with("ing") {
            return None;
        }
        let base = &word[..word.len() - 3];
        let with_e = format!("{base}e");
        let doubled = word.len() > 5 && {
            let mut tail = base.chars().rev();
            let (last, before) = (tail.next(), tail.next());
            (last == before && last.is_some_and(|letter| "bcdgklmnprstvxz".contains(letter)))
                || base.ends_with("ck")
        };
        let stem = (word.len() > 5)
            .then(|| self.lookup(base))
            .flatten()
            .or_else(|| self.lookup(&with_e))
            .or_else(|| {
                doubled
                    .then(|| self.lookup(&base[..base.len() - 1]))
                    .flatten()
            })?;
        let mut tail = stem.chars().rev();
        let last = tail.next()?;
        Some(
            if last == 't' && tail.next().is_some_and(|before| TAUS.contains(before)) {
                format!("{}ɾɪŋ", &stem[..stem.len() - last.len_utf8()])
            } else {
                format!("{stem}ɪŋ")
            },
        )
    }

    /// misaki `get_NNP`: the word spelled with the lexicon's letter names,
    /// the last one stressed.
    fn spell(&self, word: &str) -> String {
        let letters: String = word
            .chars()
            .filter(|letter| letter.is_alphabetic())
            .filter_map(|letter| self.gold.get(&letter.to_uppercase().to_string()))
            .map(String::as_str)
            .collect();
        let secondary = letters.replace(PRIMARY_STRESS, &SECONDARY_STRESS.to_string());
        match secondary.rfind(SECONDARY_STRESS) {
            Some(at) => format!(
                "{}{PRIMARY_STRESS}{}",
                &secondary[..at],
                &secondary[at + SECONDARY_STRESS.len_utf8()..]
            ),
            None => secondary,
        }
    }
}

/// Moves the trimmed sentence out of `current` when it has any phonemes.
fn push_sentence(sentences: &mut Vec<String>, current: &mut String) {
    let sentence = current.trim();
    if !sentence.is_empty() {
        sentences.push(sentence.to_owned());
    }
    current.clear();
}

/// Whether the first sounding phoneme is a vowel; `None` when there is
/// none.
fn starts_with_vowel(phonemes: &str) -> Option<bool> {
    phonemes
        .chars()
        .find(|phoneme| VOWELS.contains(*phoneme) || CONSONANTS.contains(*phoneme))
        .map(|phoneme| VOWELS.contains(phoneme))
}

/// The text split into words, numbers, and the punctuation Kokoro knows,
/// normalized like kokoro-js `normalize_text`: curly quotes and CJK
/// punctuation folded, honorifics expanded, `%`/`&`/`+`/`@`/`$` read out.
fn pieces(text: &str) -> Vec<Piece> {
    let chars: Vec<char> = text
        .chars()
        .map(|character| match character {
            '‘' | '’' => '\'',
            '«' | '»' | '“' | '”' => '"',
            '、' | '，' => ',',
            '。' => '.',
            '！' => '!',
            '：' => ':',
            '；' => ';',
            '？' => '?',
            '–' => '—',
            other => other,
        })
        .collect();
    let mut pieces: Vec<Piece> = Vec::new();
    // Words and numbers next to each other are read apart (`20%`, `$5`).
    let push = |pieces: &mut Vec<Piece>, token: Token| {
        if let Some(last) = pieces.last_mut() {
            if last.token.sounds() && token.sounds() {
                last.space_after = true;
            }
        }
        pieces.push(Piece {
            token,
            space_after: false,
        });
    };
    let word = |text: &str| Token::Word(text.to_owned());
    let mut index = 0;
    while let Some(&character) = chars.get(index) {
        let next = chars.get(index + 1).copied();
        if character.is_alphabetic() {
            let start = index;
            while chars.get(index).is_some_and(|letter| {
                letter.is_alphabetic()
                    || (*letter == '\''
                        && chars
                            .get(index + 1)
                            .is_some_and(|after| after.is_alphabetic()))
            }) {
                index += 1;
            }
            let text: String = chars[start..index].iter().collect();
            push(&mut pieces, Token::Word(text));
            continue;
        }
        let dollars = character == '$' && next.is_some_and(|after| after.is_ascii_digit());
        if character.is_ascii_digit() || dollars {
            if dollars {
                index += 1;
            }
            let number = read_number(&chars, &mut index);
            let one = number.digits == "1" && number.fraction.is_empty();
            push(&mut pieces, Token::Number(number));
            if dollars {
                push(&mut pieces, word(if one { "dollar" } else { "dollars" }));
            }
            continue;
        }
        index += 1;
        let spoken = match character {
            '%' => Some("percent"),
            '&' => Some("and"),
            '+' => Some("plus"),
            '@' => Some("at"),
            _ => None,
        };
        if let Some(spoken) = spoken {
            push(&mut pieces, word(spoken));
        } else if character == '.' && next == Some('.') && chars.get(index + 1) == Some(&'.') {
            index += 2;
            push(&mut pieces, Token::Punctuation('…'));
        } else if character == '-'
            && (next == Some('-')
                || (index >= 2
                    && chars[index - 2].is_whitespace()
                    && next.is_some_and(char::is_whitespace)))
        {
            if next == Some('-') {
                index += 1;
            }
            push(&mut pieces, Token::Punctuation('—'));
        } else if PUNCTUATION.contains(character) {
            push(&mut pieces, Token::Punctuation(character));
        } else if let Some(last) = pieces.last_mut() {
            // Whitespace, and any other mark, separates words.
            last.space_after = true;
        }
    }
    expand_honorifics(pieces)
}

/// The number at `index` (digits, group commas, a decimal part, an ordinal
/// suffix); moves `index` past it.
fn read_number(chars: &[char], index: &mut usize) -> Number {
    let digit_at = |at: usize| chars.get(at).is_some_and(char::is_ascii_digit);
    let mut digits = String::new();
    let mut form = NumberForm::Plain;
    while let Some(&character) = chars.get(*index) {
        if character.is_ascii_digit() {
            digits.push(character);
        } else if character == ',' && digit_at(*index + 1) && !digits.is_empty() {
            form = NumberForm::Grouped;
        } else {
            break;
        }
        *index += 1;
    }
    let mut fraction = String::new();
    if chars.get(*index) == Some(&'.') && digit_at(*index + 1) {
        *index += 1;
        while digit_at(*index) {
            fraction.push(chars[*index]);
            *index += 1;
        }
    }
    let suffix: String = chars.iter().skip(*index).take(2).collect();
    let after_suffix = chars
        .get(*index + 2)
        .is_some_and(|after| after.is_alphanumeric());
    if fraction.is_empty()
        && !after_suffix
        && matches!(suffix.to_lowercase().as_str(), "st" | "nd" | "rd" | "th")
    {
        *index += 2;
        form = NumberForm::Ordinal;
    }
    Number {
        digits,
        fraction,
        form,
    }
}

/// kokoro-js: `Dr.`, `Mr.`, `Ms.`, `Mrs.` read as words, their period no
/// sentence end.
fn expand_honorifics(pieces: Vec<Piece>) -> Vec<Piece> {
    let mut expanded: Vec<Piece> = Vec::with_capacity(pieces.len());
    for piece in pieces {
        let mut honorific = None;
        if let (
            Some(Piece {
                token: Token::Word(word),
                space_after: false,
            }),
            Token::Punctuation('.'),
        ) = (expanded.last(), &piece.token)
        {
            honorific = match word.as_str() {
                "Dr" | "DR" => Some("Doctor"),
                "Mr" | "MR" => Some("Mister"),
                "Ms" | "MS" => Some("Miss"),
                "Mrs" | "MRS" => Some("Mrs"),
                _ => None,
            };
        }
        match (honorific, expanded.last_mut()) {
            (Some(spoken), Some(last)) => {
                last.token = Token::Word(spoken.to_owned());
                last.space_after = piece.space_after;
            }
            (Some(_) | None, _) => expanded.push(piece),
        }
    }
    expanded
}

fn read_lexicon(path: &Path) -> Result<HashMap<String, String>, WorkerFailure> {
    let load = |error: &dyn Display| WorkerFailure::Load {
        message: format!("{}: {error}", path.display()),
    };
    let bytes = std::fs::read(path).map_err(|error| load(&error))?;
    let entries: HashMap<String, Option<Entry>> =
        serde_json::from_slice(&bytes).map_err(|error| load(&error))?;
    Ok(entries
        .into_iter()
        .filter_map(|(word, entry)| {
            let phonemes = match entry? {
                Entry::Phonemes(phonemes) => phonemes,
                Entry::Tagged(mut tagged) => tagged.remove("DEFAULT")??,
            };
            Some((word, phonemes))
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lexicon() -> Lexicon {
        let entries = |pairs: &[(&str, &str)]| {
            pairs
                .iter()
                .map(|(word, phonemes)| ((*word).to_owned(), (*phonemes).to_owned()))
                .collect()
        };
        Lexicon {
            gold: entries(&[
                ("the", "ði"),
                ("quick", "kwˈɪk"),
                ("fox", "fˈɑks"),
                ("jump", "ʤˈʌmp"),
                ("over", "ˈOvəɹ"),
                ("dog", "dˈɔɡ"),
                ("walk", "wˈɔk"),
                ("one", "wˈʌn"),
                ("twenty", "twˈɛnti"),
                ("hundred", "hˈʌndɹəd"),
                ("percent", "pəɹsˈɛnt"),
                ("Doctor", "dˈɑktəɹ"),
                ("B", "bˈi"),
                ("C", "sˈi"),
            ]),
            silver: entries(&[("brown", "bɹˈWn"), ("sit", "sˈɪt")]),
        }
    }

    #[test]
    fn sentences_follow_misaki() {
        let lexicon = lexicon();
        let spoken = [
            "The quick brown fox jumps over the dog.",
            "Walked 121 BC! The over-dog's sitting, 20% (quick)… Fox",
            "Dr. Fox jumped... to the fox.",
        ]
        .map(|text| lexicon.sentences(text));
        assert_eq!(
            spoken,
            [
                vec!["ðə kwˈɪk bɹˈWn fˈɑks ʤˈʌmps ˈOvəɹ ðə dˈɔɡ.".to_owned()],
                vec![
                    "wˈɔkt wˈʌn hˈʌndɹəd twˈɛnti wˈʌn bˌisˈi!".to_owned(),
                    "ði ˈOvəɹ dˈɔɡz sˈɪɾɪŋ, twˈɛnti pəɹsˈɛnt (kwˈɪk)…".to_owned(),
                    "fˈɑks".to_owned(),
                ],
                vec![
                    "dˈɑktəɹ fˈɑks ʤˈʌmpt…".to_owned(),
                    "tə ðə fˈɑks.".to_owned(),
                ],
            ]
        );
    }
}
