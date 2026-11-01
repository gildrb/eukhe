//! The detectors of the scrubber: one hand-written grammar per class,
//! each matching only a well-formed value between word boundaries.
//!
//! [`detect`] runs at one position of the text, where the char before
//! (in the scrubbed output) is no word char, and returns the first class
//! whose grammar matches there. Every match ends before a char that is no
//! word char (or at the end), so a token written in its place stands
//! between boundaries and [`token_at`] finds exactly it again.
//!
//! The grammars are strict on purpose: a false positive rewrites code
//! the model reads. A digit run is a card only with a network prefix, the
//! network's length and the Luhn sum, an uppercase run is an IBAN only
//! with its country's length and the mod-97 sum, a key only with its
//! vendor prefix, length and mixed characters.
//!
//! IP addresses are the compiled core's (`bend/privacy/ip.bend`, laws
//! `laws/privacy/ip.bend`): [`Ips::of`] asks it, in one call per text,
//! about every position that could start one, and [`detect`] reads the
//! answer. `::` paths and CSS pseudo-elements are no IPv6 (an IPv6 needs
//! a digit-bearing group, three explicit groups when compressed, and
//! boundaries on both sides); a version, a loopback, 0.x and 255.x are no
//! IPv4.

use eukhe_bend::rules::privacy::{
    ip_ends, Candidate, Class, BEFORE_BYTES, OTHER_MARK, REST_CHARS, WORD_MARK,
};

/// A detected value: it runs from the position [`detect`] ran at to
/// `end`; its first `keep` bytes (the `Bearer ` of a credential) stay
/// visible and the rest becomes the token.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Found {
    pub(super) class: Class,
    pub(super) keep: usize,
    pub(super) end: usize,
}

/// A word char: a letter or digit of any script, or `_`.
pub(super) fn is_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Whether the char at byte `at` of `text` is a word char.
fn word_at(text: &str, at: usize) -> bool {
    text.get(at..)
        .and_then(|rest| rest.chars().next())
        .is_some_and(is_word)
}

// IP addresses (the compiled core)
// --------------------------------

/// The IP addresses of one text, as the compiled core decides them: the
/// start and the end of each, in order.
pub(super) struct Ips {
    found: Vec<(usize, usize)>,
}

impl Ips {
    /// Ask the core, in one call, about every position of `text` that
    /// could start an address: no word char before it, and a `:` or `.`
    /// where one must come (an IPv6 starts with `::` or with a group of
    /// one to four hex digits and a `:`; an IPv4 with one to three digits
    /// and a `.`).
    pub(super) fn of(text: &str) -> Ips {
        let mut starts = Vec::new();
        let mut candidates = Vec::new();
        let mut after_word = false;
        for (at, c) in text.char_indices() {
            if !after_word && could_start_ip(text.as_bytes(), at) {
                starts.push(at);
                candidates.push(candidate(text, at));
            }
            after_word = is_word(c);
        }
        let found = starts
            .into_iter()
            .zip(ip_ends(&candidates))
            .filter_map(|(at, chars)| {
                chars.map(|chars| (at, at + chars_to_bytes(&text[at..], chars)))
            })
            .collect();
        Ips { found }
    }

    /// The end of the address that starts at `at`.
    pub(super) fn at(&self, at: usize) -> Option<usize> {
        self.found
            .binary_search_by_key(&at, |&(start, _)| start)
            .ok()
            .map(|index| self.found[index].1)
    }
}

/// Whether an address can start at `at`: `::`, one to four hex digits and
/// a `:`, or one to three digits and a `.` (every address of
/// laws/privacy/ip.bend starts so; the corpus bridge test asks the core at
/// every position without this gate and finds the same addresses).
fn could_start_ip(bytes: &[u8], at: usize) -> bool {
    let at_most = |from: usize, to: usize, want: u8| {
        bytes
            .get(at + from..bytes.len().min(at + to + 1))
            .is_some_and(|run| run.contains(&want))
    };
    match bytes.get(at) {
        Some(b':') => bytes.get(at + 1) == Some(&b':'),
        Some(b) if b.is_ascii_digit() => at_most(1, 4, b':') || at_most(1, 3, b'.'),
        Some(b) if b.is_ascii_hexdigit() => at_most(1, 4, b':'),
        Some(_) | None => false,
    }
}

/// The candidate at `at`: the line before it (at most [`BEFORE_BYTES`]),
/// the text from it (at most [`REST_CHARS`] chars), each non-ASCII char as
/// its class.
pub(super) fn candidate(text: &str, at: usize) -> Candidate {
    let mut start = at.saturating_sub(BEFORE_BYTES);
    while !text.is_char_boundary(start) {
        start += 1;
    }
    Candidate {
        before: text[start..at].chars().map(wire_char).collect(),
        rest: text[at..].chars().take(REST_CHARS).map(wire_char).collect(),
    }
}

/// A char as a candidate carries it: an ASCII char as itself, any other
/// as [`WORD_MARK`] or [`OTHER_MARK`].
fn wire_char(c: char) -> char {
    if c.is_ascii() {
        c
    } else if is_word(c) {
        WORD_MARK
    } else {
        OTHER_MARK
    }
}

/// The byte length of the first `chars` chars of `text`.
pub(super) fn chars_to_bytes(text: &str, chars: usize) -> usize {
    text.char_indices()
        .nth(chars)
        .map_or(text.len(), |(index, _)| index)
}

/// The byte at `at`, when there is one.
fn byte(text: &str, at: usize) -> Option<u8> {
    text.as_bytes().get(at).copied()
}

/// The byte before `at`, when there is one.
fn byte_before(text: &str, at: usize) -> Option<u8> {
    at.checked_sub(1).and_then(|before| byte(text, before))
}

/// The end of the run of bytes from `at` that `keep` accepts.
fn run(text: &str, at: usize, keep: impl Fn(u8) -> bool) -> usize {
    let bytes = text.as_bytes();
    let mut end = at;
    while end < bytes.len() && keep(bytes[end]) {
        end += 1;
    }
    end
}

/// [`run`], stopped after `limit` bytes: a grammar whose value is at most
/// `limit - 1` long reads no further, so text of many starts stays linear.
fn run_at_most(text: &str, at: usize, limit: usize, keep: impl Fn(u8) -> bool) -> usize {
    let bytes = text.as_bytes();
    let stop = bytes.len().min(at + limit);
    let mut end = at;
    while end < stop && keep(bytes[end]) {
        end += 1;
    }
    end
}

/// The first class whose grammar matches at `at`: a literal that reads as
/// a token of a `mapped` class, then each class's grammar; the IP
/// addresses are `ips`'s. The caller holds that `at` is a char boundary
/// and that the scrubbed output's char before it is no word char.
pub(super) fn detect(
    text: &str,
    at: usize,
    terms: &[Vec<char>],
    ips: &Ips,
    mapped: &[Class],
) -> Option<Found> {
    if let Some((class, end)) = token_at(text, at, mapped) {
        // A literal that reads as a token is itself a value of its class:
        // it gets a token of its own, so a token maps back to one value.
        return Some(Found {
            class,
            keep: 0,
            end,
        });
    }
    private_key(text, at)
        .or_else(|| term(text, at, terms))
        .or_else(|| vendor_key(text, at))
        .or_else(|| bearer(text, at))
        .or_else(|| email(text, at))
        .or_else(|| iban(text, at))
        .or_else(|| card(text, at))
        .or_else(|| ssn(text, at))
        .or_else(|| phone(text, at))
        .or_else(|| {
            ips.at(at).map(|end| Found {
                class: Class::Ip,
                keep: 0,
                end,
            })
        })
}

/// A token of a `mapped` class at `at` (`IP_12`), followed by no word
/// char: its class and end.
pub(super) fn token_at(text: &str, at: usize, mapped: &[Class]) -> Option<(Class, usize)> {
    let name_end = run(text, at, |b| b.is_ascii_uppercase());
    let name = text.get(at..name_end)?;
    let class = *mapped.iter().find(|class| class.name() == name)?;
    if byte(text, name_end) != Some(b'_') {
        return None;
    }
    let end = run(text, name_end + 1, |b| b.is_ascii_digit());
    (end > name_end + 1 && !word_at(text, end)).then_some((class, end))
}

// Credentials (one way)
// ---------------------

/// A PEM private key block, whole: `-----BEGIN <label>-----` with a label
/// that names a private key, through its `-----END <label>-----`.
/// Certificates and public keys are no secret and pass.
fn private_key(text: &str, at: usize) -> Option<Found> {
    const BEGIN: &str = "-----BEGIN ";
    let rest = text.get(at..)?.strip_prefix(BEGIN)?;
    let label_len = rest.find("-----")?;
    let label = &rest[..label_len];
    if !label.contains("PRIVATE KEY")
        || !label
            .bytes()
            .all(|b| b.is_ascii_uppercase() || b.is_ascii_digit() || b == b' ')
    {
        return None;
    }
    let close = format!("-----END {label}-----");
    let body = at + BEGIN.len() + label_len + "-----".len();
    let end = body + text[body..].find(&close)? + close.len();
    Some(Found {
        class: Class::Key,
        keep: 0,
        end,
    })
}

/// What a vendor token's body must hold besides its charset.
#[derive(Clone, Copy)]
enum Mix {
    /// Any body (a fixed-length hex body is random enough).
    Any,
    Digit,
    DigitAndLetter,
    DigitUpperAndLower,
}

/// One vendor's token shape: a case-sensitive prefix, the body's charset
/// and length bounds, and the character mix a random body shows.
struct VendorKey {
    prefix: &'static str,
    body: fn(u8) -> bool,
    min: usize,
    max: usize,
    mix: Mix,
}

fn alnum(b: u8) -> bool {
    b.is_ascii_alphanumeric()
}

fn alnum_dash_underscore(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'-' || b == b'_'
}

fn alnum_underscore(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn alnum_dash(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'-'
}

fn upper_digit(b: u8) -> bool {
    b.is_ascii_uppercase() || b.is_ascii_digit()
}

fn lower_hex(b: u8) -> bool {
    b.is_ascii_digit() || (b'a'..=b'f').contains(&b)
}

const VENDOR_KEYS: &[VendorKey] = &[
    // OpenAI (`sk-`, `sk-proj-`), Anthropic (`sk-ant-`).
    VendorKey {
        prefix: "sk-",
        body: alnum_dash_underscore,
        min: 32,
        max: 512,
        mix: Mix::DigitUpperAndLower,
    },
    // GitHub tokens.
    VendorKey {
        prefix: "ghp_",
        body: alnum,
        min: 36,
        max: 255,
        mix: Mix::DigitAndLetter,
    },
    VendorKey {
        prefix: "gho_",
        body: alnum,
        min: 36,
        max: 255,
        mix: Mix::DigitAndLetter,
    },
    VendorKey {
        prefix: "ghu_",
        body: alnum,
        min: 36,
        max: 255,
        mix: Mix::DigitAndLetter,
    },
    VendorKey {
        prefix: "ghs_",
        body: alnum,
        min: 36,
        max: 255,
        mix: Mix::DigitAndLetter,
    },
    VendorKey {
        prefix: "ghr_",
        body: alnum,
        min: 36,
        max: 255,
        mix: Mix::DigitAndLetter,
    },
    VendorKey {
        prefix: "github_pat_",
        body: alnum_underscore,
        min: 22,
        max: 255,
        mix: Mix::DigitAndLetter,
    },
    // Slack.
    VendorKey {
        prefix: "xoxa-",
        body: alnum_dash,
        min: 10,
        max: 255,
        mix: Mix::Digit,
    },
    VendorKey {
        prefix: "xoxb-",
        body: alnum_dash,
        min: 10,
        max: 255,
        mix: Mix::Digit,
    },
    VendorKey {
        prefix: "xoxp-",
        body: alnum_dash,
        min: 10,
        max: 255,
        mix: Mix::Digit,
    },
    VendorKey {
        prefix: "xoxr-",
        body: alnum_dash,
        min: 10,
        max: 255,
        mix: Mix::Digit,
    },
    VendorKey {
        prefix: "xoxs-",
        body: alnum_dash,
        min: 10,
        max: 255,
        mix: Mix::Digit,
    },
    // AWS access key ids.
    VendorKey {
        prefix: "AKIA",
        body: upper_digit,
        min: 16,
        max: 16,
        mix: Mix::Digit,
    },
    VendorKey {
        prefix: "ASIA",
        body: upper_digit,
        min: 16,
        max: 16,
        mix: Mix::Digit,
    },
    // Google API keys.
    VendorKey {
        prefix: "AIza",
        body: alnum_dash_underscore,
        min: 35,
        max: 35,
        mix: Mix::DigitAndLetter,
    },
    // GitLab.
    VendorKey {
        prefix: "glpat-",
        body: alnum_dash_underscore,
        min: 20,
        max: 255,
        mix: Mix::DigitAndLetter,
    },
    // DigitalOcean.
    VendorKey {
        prefix: "dop_v1_",
        body: lower_hex,
        min: 64,
        max: 64,
        mix: Mix::Any,
    },
    // Shopify.
    VendorKey {
        prefix: "shpat_",
        body: lower_hex,
        min: 32,
        max: 32,
        mix: Mix::Any,
    },
    VendorKey {
        prefix: "shpss_",
        body: lower_hex,
        min: 32,
        max: 32,
        mix: Mix::Any,
    },
    VendorKey {
        prefix: "shpca_",
        body: lower_hex,
        min: 32,
        max: 32,
        mix: Mix::Any,
    },
    // npm.
    VendorKey {
        prefix: "npm_",
        body: alnum,
        min: 36,
        max: 36,
        mix: Mix::DigitAndLetter,
    },
];

/// Whether `body` shows `mix`.
fn mixed(body: &[u8], mix: Mix) -> bool {
    let digit = body.iter().any(u8::is_ascii_digit);
    let upper = body.iter().any(u8::is_ascii_uppercase);
    let lower = body.iter().any(u8::is_ascii_lowercase);
    match mix {
        Mix::Any => true,
        Mix::Digit => digit,
        Mix::DigitAndLetter => digit && (upper || lower),
        Mix::DigitUpperAndLower => digit && upper && lower,
    }
}

/// A token with a known vendor prefix: the whole token.
fn vendor_key(text: &str, at: usize) -> Option<Found> {
    let rest = text.get(at..)?;
    VENDOR_KEYS.iter().find_map(|key| {
        if !rest.starts_with(key.prefix) {
            return None;
        }
        let body = at + key.prefix.len();
        let end = run_at_most(text, body, key.max + 1, key.body);
        let len = end - body;
        ((key.min..=key.max).contains(&len)
            && mixed(&text.as_bytes()[body..end], key.mix)
            && !word_at(text, end))
        .then_some(Found {
            class: Class::Key,
            keep: 0,
            end,
        })
    })
}

/// A bearer credential: `Bearer ` (or `bearer `) and a token68 of at
/// least 20 chars with a digit and a letter; `Bearer ` stays visible.
/// Prose (`Bearer authentication`) and templates (`Bearer ${token}`)
/// pass.
fn bearer(text: &str, at: usize) -> Option<Found> {
    let rest = text.get(at..)?;
    if !(rest.starts_with("Bearer ") || rest.starts_with("bearer ")) {
        return None;
    }
    let body = at + "Bearer ".len();
    let token_end = run_at_most(text, body, 4097, |b| {
        b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'~' | b'+' | b'/' | b'-')
    });
    let end = run(text, token_end, |b| b == b'=');
    let token = &text.as_bytes()[body..token_end];
    ((20..=4096).contains(&token.len()) && mixed(token, Mix::DigitAndLetter) && !word_at(text, end))
        .then_some(Found {
            class: Class::Key,
            keep: "Bearer ".len(),
            end,
        })
}

/// The IBAN length of each country of the IBAN registry.
const IBAN_LENGTHS: &[(&str, usize)] = &[
    ("AD", 24),
    ("AE", 23),
    ("AL", 28),
    ("AT", 20),
    ("AZ", 28),
    ("BA", 20),
    ("BE", 16),
    ("BG", 22),
    ("BH", 22),
    ("BI", 27),
    ("BR", 29),
    ("BY", 28),
    ("CH", 21),
    ("CR", 22),
    ("CY", 28),
    ("CZ", 24),
    ("DE", 22),
    ("DJ", 27),
    ("DK", 18),
    ("DO", 28),
    ("EE", 20),
    ("EG", 29),
    ("ES", 24),
    ("FI", 18),
    ("FK", 18),
    ("FO", 18),
    ("FR", 27),
    ("GB", 22),
    ("GE", 22),
    ("GI", 23),
    ("GL", 18),
    ("GR", 27),
    ("GT", 28),
    ("HR", 21),
    ("HU", 28),
    ("IE", 22),
    ("IL", 23),
    ("IQ", 23),
    ("IS", 26),
    ("IT", 27),
    ("JO", 30),
    ("KW", 30),
    ("KZ", 20),
    ("LB", 28),
    ("LC", 32),
    ("LI", 21),
    ("LT", 20),
    ("LU", 20),
    ("LV", 21),
    ("LY", 25),
    ("MC", 27),
    ("MD", 24),
    ("ME", 22),
    ("MK", 19),
    ("MN", 20),
    ("MR", 27),
    ("MT", 31),
    ("MU", 30),
    ("NI", 28),
    ("NL", 18),
    ("NO", 15),
    ("OM", 23),
    ("PK", 24),
    ("PL", 28),
    ("PS", 29),
    ("PT", 25),
    ("QA", 29),
    ("RO", 24),
    ("RS", 22),
    ("RU", 33),
    ("SA", 24),
    ("SC", 31),
    ("SD", 18),
    ("SE", 24),
    ("SI", 19),
    ("SK", 24),
    ("SM", 27),
    ("SO", 23),
    ("ST", 25),
    ("SV", 28),
    ("TL", 23),
    ("TN", 24),
    ("TR", 26),
    ("UA", 29),
    ("VA", 22),
    ("VG", 24),
    ("XK", 20),
    ("YE", 30),
];

/// An IBAN: a registry country, two check digits and the country's
/// length of uppercase letters and digits, written whole or in groups of
/// four, whose mod-97 sum is 1.
fn iban(text: &str, at: usize) -> Option<Found> {
    let bytes = text.as_bytes();
    let head = bytes.get(at..at + 4)?;
    if !(head[0].is_ascii_uppercase()
        && head[1].is_ascii_uppercase()
        && head[2].is_ascii_digit()
        && head[3].is_ascii_digit())
    {
        return None;
    }
    let country = &text[at..at + 2];
    let (_, length) = IBAN_LENGTHS.iter().find(|(code, _)| *code == country)?;
    let mut chars: Vec<u8> = head.to_vec();
    let mut end = at + 4;
    if byte(text, end) == Some(b' ') {
        // Groups of four, the last one shorter when the length says so.
        while chars.len() < *length && byte(text, end) == Some(b' ') {
            let group = end + 1;
            let group_end = run(text, group, upper_digit).min(group + 4);
            let size = group_end - group;
            if size == 0 || (size < 4 && chars.len() + size != *length) {
                return None;
            }
            chars.extend_from_slice(&bytes[group..group_end]);
            end = group_end;
        }
    } else {
        end = run(text, end, upper_digit);
        chars.extend_from_slice(&bytes[at + 4..end]);
    }
    (chars.len() == *length && !word_at(text, end) && iban_sum(&chars) == 1).then_some(Found {
        class: Class::Iban,
        keep: 0,
        end,
    })
}

/// The mod-97 sum of an IBAN: its first four chars moved to the end,
/// each letter read as two digits (`A` = 10).
fn iban_sum(chars: &[u8]) -> u32 {
    chars[4..].iter().chain(&chars[..4]).fold(0u32, |sum, &c| {
        if c.is_ascii_digit() {
            (sum * 10 + u32::from(c - b'0')) % 97
        } else {
            (sum * 100 + u32::from(c - b'A') + 10) % 97
        }
    })
}

/// Published test card numbers (Stripe, Visa, Mastercard, Amex,
/// Discover, JCB, Diners): payment code and its tests carry them, and
/// they pay for nothing.
const TEST_CARDS: &[&str] = &[
    "4242424242424242",
    "4111111111111111",
    "4012888888881881",
    "4000056655665556",
    "4000000000000002",
    "5555555555554444",
    "5105105105105100",
    "2223003122003222",
    "5200828282828210",
    "378282246310005",
    "371449635398431",
    "6011111111111117",
    "6011000990139424",
    "3566002020360505",
    "30569309025904",
    "38520000023237",
];

/// A card number: 13 to 19 digits, whole or in groups (fours, the last
/// one shorter; or the 4-6-5 and 4-6-4 forms) split by one kind of
/// separator (a space or a dash), with a network's prefix and length,
/// a valid Luhn sum, and no published test number.
fn card(text: &str, at: usize) -> Option<Found> {
    if !byte(text, at)?.is_ascii_digit() || byte_before(text, at) == Some(b'.') {
        return None;
    }
    // Every card shape opens with four digits or with the whole number.
    let first = run(text, at, |b| b.is_ascii_digit()) - at;
    if !(first == 4 || (13..=19).contains(&first)) {
        return None;
    }
    // The digit groups (at most five) and where each ends.
    let mut groups = [(0usize, 0usize); 5];
    let mut count = 0;
    let mut separator = None;
    let mut start = at;
    loop {
        let end = run(text, start, |b| b.is_ascii_digit());
        groups[count] = (start, end);
        count += 1;
        let Some(next) = byte(text, end).filter(|b| matches!(b, b' ' | b'-')) else {
            break;
        };
        if separator.is_some_and(|kind| kind != next)
            || !byte(text, end + 1).is_some_and(|b| b.is_ascii_digit())
            || count == groups.len()
        {
            break;
        }
        separator = Some(next);
        start = end + 1;
    }
    let bytes = text.as_bytes();
    // The longest run of leading groups that is a card.
    (1..=count).rev().find_map(|taken| {
        let mut sizes = [0usize; 5];
        let mut digits = [0u8; 19];
        let mut len = 0;
        for (index, (start, end)) in groups[..taken].iter().enumerate() {
            sizes[index] = end - start;
            if len + sizes[index] > digits.len() {
                return None;
            }
            digits[len..len + sizes[index]].copy_from_slice(&bytes[*start..*end]);
            len += sizes[index];
        }
        let digits = &digits[..len];
        let end = groups[taken - 1].1;
        let shaped = match &sizes[..taken] {
            [whole] => (13..=19).contains(whole),
            [4, 6, 4 | 5] => true,
            [init @ .., last] => init.iter().all(|size| *size == 4) && (1..=4).contains(last),
            [] => false,
        };
        let after_ok = !number_goes_on(text, end);
        (shaped
            && after_ok
            && network(digits)
            && luhn(digits)
            && !TEST_CARDS.iter().any(|test| test.as_bytes() == digits))
        .then_some(Found {
            class: Class::Card,
            keep: 0,
            end,
        })
    })
}

/// Whether the digits carry a card network's prefix and length.
fn network(digits: &[u8]) -> bool {
    let len = digits.len();
    let prefix = |count: usize| {
        digits[..count]
            .iter()
            .fold(0u32, |value, digit| value * 10 + u32::from(digit - b'0'))
    };
    if len < 4 {
        return false;
    }
    let (one, two, three, four) = (prefix(1), prefix(2), prefix(3), prefix(4));
    // Visa.
    (one == 4 && matches!(len, 13 | 16 | 19))
        // Mastercard.
        || (((51..=55).contains(&two) || (2221..=2720).contains(&four)) && len == 16)
        // American Express.
        || (matches!(two, 34 | 37) && len == 15)
        // Discover.
        || ((four == 6011 || (644..=649).contains(&three) || two == 65) && (16..=19).contains(&len))
        // Diners Club.
        || (((300..=305).contains(&three) || matches!(two, 36 | 38 | 39)) && (14..=19).contains(&len))
        // JCB.
        || ((3528..=3589).contains(&four) && (16..=19).contains(&len))
        // UnionPay.
        || (two == 62 && (16..=19).contains(&len))
}

/// The Luhn check of a digit run.
fn luhn(digits: &[u8]) -> bool {
    let sum: u32 = digits
        .iter()
        .rev()
        .enumerate()
        .map(|(index, &b)| {
            let digit = u32::from(b - b'0');
            if index % 2 == 1 {
                let doubled = digit * 2;
                doubled / 10 + doubled % 10
            } else {
                digit
            }
        })
        .sum();
    sum.is_multiple_of(10)
}

// Personal values (mapped back)
// -----------------------------

/// A phrase of `privacy.terms` (longest first), compared char by char
/// case-insensitively, followed by no word char.
fn term(text: &str, at: usize, terms: &[Vec<char>]) -> Option<Found> {
    let rest = text.get(at..)?;
    terms.iter().find_map(|term| {
        let mut chars = rest.char_indices();
        let mut end = at;
        for &wanted in term {
            let (index, seen) = chars.next()?;
            if !(seen == wanted || seen.to_lowercase().eq(wanted.to_lowercase())) {
                return None;
            }
            end = at + index + seen.len_utf8();
        }
        (!word_at(text, end)).then_some(Found {
            class: Class::Person,
            keep: 0,
            end,
        })
    })
}

/// A char of an email's local part.
fn local_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'%' | b'+' | b'-')
}

/// An email: a local part that starts with a letter or digit, `@`, and
/// two or more dot-separated labels whose last is 2 to 24 letters. Not an
/// email: an scp-style remote (`git@github.com:org/repo`) and a
/// resolution suffix (`icon@2x.png`).
fn email(text: &str, at: usize) -> Option<Found> {
    let bytes = text.as_bytes();
    if !byte(text, at)?.is_ascii_alphanumeric() || byte_before(text, at).is_some_and(local_char) {
        return None;
    }
    let at_sign = run(text, at, local_char);
    let local = &bytes[at..at_sign];
    if byte(text, at_sign) != Some(b'@')
        || local.len() > 64
        || local.ends_with(b".")
        || local.windows(2).any(|pair| pair == b"..")
    {
        return None;
    }
    let mut labels: Vec<(usize, usize)> = Vec::new();
    let mut start = at_sign + 1;
    loop {
        let end = run(text, start, |b| b.is_ascii_alphanumeric() || b == b'-');
        if end == start || end - start > 63 || bytes[start] == b'-' || bytes[end - 1] == b'-' {
            return None;
        }
        labels.push((start, end));
        if byte(text, end) == Some(b'.')
            && byte(text, end + 1).is_some_and(|b| b.is_ascii_alphanumeric())
        {
            start = end + 1;
        } else {
            break;
        }
    }
    let (first_start, first_end) = labels[0];
    let (last_start, end) = labels[labels.len() - 1];
    let tld = &bytes[last_start..end];
    let first = &bytes[first_start..first_end];
    let resolution = first.len() >= 2
        && first.ends_with(b"x")
        && first[..first.len() - 1].iter().all(u8::is_ascii_digit);
    let scp_remote = byte(text, end) == Some(b':')
        && byte(text, end + 1).is_some_and(|b| !b.is_ascii_whitespace());
    (labels.len() >= 2
        && (2..=24).contains(&tld.len())
        && tld.iter().all(u8::is_ascii_alphabetic)
        && !resolution
        && !scp_remote
        && !word_at(text, end)
        && !matches!(byte(text, end), Some(b'-' | b'@')))
    .then_some(Found {
        class: Class::Email,
        keep: 0,
        end,
    })
}

/// Whether the digits at `at..at + count` are all digits.
fn digits_at(text: &str, at: usize, count: usize) -> bool {
    text.as_bytes()
        .get(at..at + count)
        .is_some_and(|run| run.iter().all(u8::is_ascii_digit))
}

/// Whether a dashed number goes on at `end` (a word char, or a dash and
/// a digit).
fn continues(text: &str, end: usize) -> bool {
    word_at(text, end)
        || (byte(text, end) == Some(b'-')
            && byte(text, end + 1).is_some_and(|b| b.is_ascii_digit()))
}

/// Whether a number goes on at `end` (a word char, or a decimal point
/// and a digit).
fn number_goes_on(text: &str, end: usize) -> bool {
    word_at(text, end)
        || (byte(text, end) == Some(b'.')
            && byte(text, end + 1).is_some_and(|b| b.is_ascii_digit()))
}

/// A US social security number `AAA-GG-SSSS` with an area that is
/// assigned (not 000, 666 or 9xx), a group that is not 00 and a serial
/// that is not 0000.
fn ssn(text: &str, at: usize) -> Option<Found> {
    let end = at + 11;
    let shaped = digits_at(text, at, 3)
        && byte(text, at + 3) == Some(b'-')
        && digits_at(text, at + 4, 2)
        && byte(text, at + 6) == Some(b'-')
        && digits_at(text, at + 7, 4);
    if !shaped || byte_before(text, at) == Some(b'-') || continues(text, end) {
        return None;
    }
    let area = &text[at..at + 3];
    (area != "000"
        && area != "666"
        && !area.starts_with('9')
        && &text[at + 4..at + 6] != "00"
        && &text[at + 7..at + 11] != "0000")
        .then_some(Found {
            class: Class::Id,
            keep: 0,
            end,
        })
}

/// A phone number: `+`, a country code and digits split by single
/// spaces, dashes or parentheses, 8 to 15 digits in all (E.164), where
/// the `+` is no operator; or a North American `NXX-NXX-XXXX`.
fn phone(text: &str, at: usize) -> Option<Found> {
    match byte(text, at)? {
        b'+' => international_phone(text, at),
        b'2'..=b'9' => north_american_phone(text, at),
        _ => None,
    }
}

fn international_phone(text: &str, at: usize) -> Option<Found> {
    if matches!(byte_before(text, at), Some(b')' | b']' | b'.')) {
        return None;
    }
    let bytes = text.as_bytes();
    let mut index = at + 1;
    let mut end = at + 1;
    let mut digits = 0;
    while let Some(b) = byte(text, index) {
        match b {
            b'0'..=b'9' => {
                digits += 1;
                end = index + 1;
            }
            b' ' | b'-' | b'(' | b')' if index > at + 1 => {
                // One separator at a time, and only between digits and
                // parentheses.
                let next = bytes.get(index + 1).copied();
                if !next
                    .is_some_and(|n| n.is_ascii_digit() || n == b'(' || (b == b')' && n == b' '))
                {
                    break;
                }
            }
            _ => break,
        }
        index += 1;
        if index - at > 24 {
            return None;
        }
    }
    ((8..=15).contains(&digits)
        && byte(text, at + 1).is_some_and(|b| b.is_ascii_digit())
        && !number_goes_on(text, end))
    .then_some(Found {
        class: Class::Phone,
        keep: 0,
        end,
    })
}

fn north_american_phone(text: &str, at: usize) -> Option<Found> {
    let end = at + 12;
    let shaped = digits_at(text, at, 3)
        && byte(text, at + 3) == Some(b'-')
        && byte(text, at + 4).is_some_and(|b| (b'2'..=b'9').contains(&b))
        && digits_at(text, at + 4, 3)
        && byte(text, at + 7) == Some(b'-')
        && digits_at(text, at + 8, 4);
    (shaped && byte_before(text, at) != Some(b'-') && !continues(text, end)).then_some(Found {
        class: Class::Phone,
        keep: 0,
        end,
    })
}
