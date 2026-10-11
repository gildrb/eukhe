//! `TypeBox`'s IDNA hostname checks (`format/idna`): the `hostname` and
//! `idn-hostname` formats, with its own Punycode codec and Bidi rule.

use unicode_normalization::UnicodeNormalization;

use super::js_value::usize_to_f64;
use super::regexp::{static_regexp, JsRegExp};
use crate::utils::js::utf16_len;

static_regexp!(RE_RULE_HYPHEN_PLACEMENT, r"^(?!-).*(?<!-)$", "");
static_regexp!(RE_RULE_NOT_RESERVED_ACE, r"^(?!..--)", "");
static_regexp!(RE_ASCII_LDH, r"^[a-zA-Z0-9-]*$", "");
static_regexp!(RE_NON_ASCII, r"[^\p{ASCII}]", "u");
static_regexp!(RE_ARABIC_INDIC_DIGIT, r"[\u{0660}-\u{0669}]", "u");
static_regexp!(RE_MARK_NONSPACING, r"\p{Mn}", "u");
static_regexp!(RE_COMBINING_MARK, r"[\p{Mn}\p{Mc}\p{Me}]", "u");
static_regexp!(RE_LETTER, r"\p{L}", "u");
static_regexp!(RE_SCRIPT_GREEK, r"\p{Script=Greek}", "u");
static_regexp!(RE_SCRIPT_HEBREW, r"\p{Script=Hebrew}", "u");
static_regexp!(
    RE_SCRIPT_JAPANESE,
    r"[\p{Script=Hiragana}\p{Script=Katakana}\p{Script=Han}]",
    "u"
);
static_regexp!(
    RE_SCRIPT_ARABIC_LETTER,
    r"[\p{Script=Arabic}\p{Script=Syriac}\p{Script=Thaana}\p{Script=Mandaic}]",
    "u"
);
static_regexp!(
    RE_VIRAMA,
    r"[\u{094d}\u{09cd}\u{0a4d}\u{0acd}\u{0b4d}\u{0bcd}\u{0c4d}\u{0ccd}\u{0d3b}\u{0d3c}\u{0d4d}\u{0dca}\u{1b44}\u{1baa}\u{1bab}\u{a9c0}\u{11046}\u{1107f}\u{110b9}\u{11133}\u{11134}\u{111c0}\u{11235}\u{1134d}\u{11442}\u{114c2}\u{115bf}\u{1163f}\u{116b6}\u{11c3f}\u{11d44}\u{11d45}]",
    "u"
);
static_regexp!(
    RE_RFC5892_DISALLOWED,
    r"[\u{0640}\u{07fa}\u{302e}\u{302f}\u{3031}\u{3032}\u{3033}\u{3034}\u{3035}\u{303b}]",
    "u"
);
static_regexp!(RE_EUROPEAN_NUMBER, r"[0-9]|[\u{06f0}-\u{06f9}]", "u");
static_regexp!(
    RE_PERMITTED_CATEGORY,
    r"\p{L}|[\u{002d}\u{002b}]|[\u{002e}\u{002c}\u{003a}\u{002f}]|\p{Nd}|\p{Mn}|\p{Mc}|[\u{00b7}\u{0375}\u{05f3}\u{05f4}\u{200c}\u{200d}\u{30fb}]|[\u{00df}\u{03c2}\u{06fd}\u{06fe}\u{0f0b}\u{3007}]",
    "u"
);

/// `Idna.IsHostname`: RFC 1123 hostnames, allowing valid Punycode labels.
pub(crate) fn is_hostname(value: &str) -> bool {
    let length = utf16_len(value);
    if length == 0 || length > 253 {
        return false;
    }
    if value.ends_with('.') {
        return false;
    }
    value.split('.').all(|label| {
        is_valid_label_length(label) && (is_puny_label(label) || is_ascii_label(label))
    })
}

/// `Idna.IsIdnHostname`: internationalized hostnames after the UTS #46-style
/// mappings `TypeBox` applies.
pub(crate) fn is_idn_hostname(value: &str) -> bool {
    if value.is_empty() || value.contains(' ') {
        return false;
    }
    let normalized = normalize_hostname(value);
    if utf16_len(&normalized) > 253 {
        return false;
    }
    let labels: Vec<&str> = normalized.split('.').collect();
    let has_bidi_chars = labels.iter().any(|label| has_bidi_chars(label));
    labels.iter().all(|label| {
        is_valid_label_length(label)
            && (is_puny_label(label) || is_unicode_label(label))
            && (!has_bidi_chars || satisfies_bidi_rule(label.chars().map(Some)))
    })
}

fn is_valid_label_length(label: &str) -> bool {
    let length = utf16_len(label);
    length > 0 && length <= 63
}

fn normalize_hostname(value: &str) -> String {
    let widened: String = value
        .chars()
        .map(|c| match c {
            '\u{FF01}'..='\u{FF5E}' => char::from_u32(u32::from(c) - 0xFEE0).unwrap_or(c),
            _ => c,
        })
        .collect();
    widened
        .nfc()
        .filter(|c| {
            !matches!(
                c,
                '\u{00AD}' | '\u{034F}' | '\u{180B}'..='\u{180D}' | '\u{200B}' | '\u{FE00}'..='\u{FE0F}' | '\u{E0100}'..='\u{E01EF}'
            )
        })
        .map(|c| if matches!(c, '\u{002E}' | '\u{3002}' | '\u{FF0E}' | '\u{FF61}') { '.' } else { c })
        .collect()
}

fn is_ascii_label(value: &str) -> bool {
    RE_RULE_HYPHEN_PLACEMENT.test(value)
        && RE_RULE_NOT_RESERVED_ACE.test(value)
        && RE_ASCII_LDH.test(value)
}

/// `value.toLowerCase().startsWith('xn--')`. Only `X`/`x` and `N`/`n` lower
/// to `x`/`n`, so a match implies the first four bytes are ASCII.
fn is_ace_prefixed(value: &str) -> bool {
    value.len() >= 4 && value.is_char_boundary(4) && value[..4].eq_ignore_ascii_case("xn--")
}

fn is_puny_label(value: &str) -> bool {
    if !is_ace_prefixed(value) {
        return false;
    }
    let body = value[4..].to_lowercase();
    if body.rfind('-') == Some(0) {
        return false;
    }
    // A decode error or a surrogate code point (which no later check permits)
    // makes the label invalid.
    let Some(decoded) = decode(&body).and_then(|points| code_points_to_string(&points)) else {
        return false;
    };
    if !RE_NON_ASCII.test(&decoded) {
        return false;
    }
    is_unicode_label(&decoded)
}

fn is_unicode_label(value: &str) -> bool {
    if exceeds_max_a_label_length(value) {
        return false;
    }
    if has_right_to_left_characters(value.chars().map(Some))
        && !satisfies_bidi_rule(value.chars().map(Some))
    {
        return false;
    }
    let chars: Vec<char> = value.chars().collect();
    if has_invalid_hyphens(&chars) {
        return false;
    }
    if chars
        .first()
        .is_some_and(|first| test_char(&RE_COMBINING_MARK, *first))
    {
        return false;
    }
    let mut has_japanese = false;
    for (index, &current) in chars.iter().enumerate() {
        if test_char(&RE_RFC5892_DISALLOWED, current) {
            return false;
        }
        if !test_char(&RE_PERMITTED_CATEGORY, current) {
            return false;
        }
        if test_char(&RE_SCRIPT_JAPANESE, current) {
            has_japanese = true;
        }
        // `!prev` / `!next`: absent or U+0000.
        let previous = index
            .checked_sub(1)
            .map(|position| chars[position])
            .filter(|c| *c != '\0');
        let next = chars.get(index + 1).copied().filter(|c| *c != '\0');
        let allowed = match current {
            // MIDDLE DOT (Catalan)
            '\u{00B7}' => previous == Some('l') && next == Some('l'),
            // Greek KERAIA
            '\u{0375}' => next.is_some_and(|c| test_char(&RE_SCRIPT_GREEK, c)),
            // Hebrew GERESH / GERSHAYIM
            '\u{05F3}' | '\u{05F4}' => previous.is_some_and(|c| test_char(&RE_SCRIPT_HEBREW, c)),
            // ZWNJ: RFC 5892 Appendix A.1
            '\u{200C}' => previous.is_some_and(|c| !c.is_ascii() || test_char(&RE_VIRAMA, c)),
            // ZWJ: RFC 5892 Appendix A.2
            '\u{200D}' => previous.is_some_and(|c| test_char(&RE_VIRAMA, c)),
            _ => true,
        };
        if !allowed {
            return false;
        }
    }
    !value.contains('\u{30FB}') || has_japanese
}

fn has_invalid_hyphens(chars: &[char]) -> bool {
    if chars.first() == Some(&'-') || chars.last() == Some(&'-') {
        return true;
    }
    chars.get(2) == Some(&'-') && chars.get(3) == Some(&'-')
}

fn exceeds_max_a_label_length(value: &str) -> bool {
    RE_NON_ASCII.test(value) && utf16_len(&encode(value)) + 4 > 63
}

fn has_bidi_chars(value: &str) -> bool {
    if is_ace_prefixed(value) {
        return decode(&value[4..].to_lowercase()).is_some_and(|points| {
            has_right_to_left_characters(points.iter().map(|point| char::from_u32(*point)))
        });
    }
    has_right_to_left_characters(value.chars().map(Some))
}

/// Bidi class of a code point; `None` is a lone surrogate, which no class
/// pattern matches (`ON`).
fn bidi_class(c: Option<char>) -> &'static str {
    let Some(c) = c else {
        return "ON";
    };
    if test_char(&RE_EUROPEAN_NUMBER, c) {
        "EN"
    } else if test_char(&RE_ARABIC_INDIC_DIGIT, c) {
        "AN"
    } else if test_char(&RE_MARK_NONSPACING, c) {
        "NSM"
    } else if test_char(&RE_SCRIPT_HEBREW, c) {
        "R"
    } else if test_char(&RE_SCRIPT_ARABIC_LETTER, c) {
        "AL"
    } else if test_char(&RE_LETTER, c) {
        "L"
    } else {
        "ON"
    }
}

fn has_right_to_left_characters(chars: impl Iterator<Item = Option<char>>) -> bool {
    chars
        .map(bidi_class)
        .any(|class| matches!(class, "R" | "AL" | "AN"))
}

fn satisfies_bidi_rule(chars: impl Iterator<Item = Option<char>>) -> bool {
    let mut is_rtl = false;
    let mut saw_european_number = false;
    let mut saw_arabic_number = false;
    let mut is_first = true;
    for c in chars {
        let class = bidi_class(c);
        if is_first {
            if !matches!(class, "L" | "R" | "AL") {
                return false;
            }
            is_rtl = matches!(class, "R" | "AL");
            is_first = false;
        }
        let allowed = if is_rtl {
            matches!(
                class,
                "R" | "AL" | "AN" | "EN" | "ES" | "CS" | "ET" | "ON" | "BN" | "NSM"
            )
        } else {
            matches!(class, "L" | "EN" | "ES" | "CS" | "ET" | "ON" | "BN" | "NSM")
        };
        if !allowed {
            return false;
        }
        if class == "EN" {
            saw_european_number = true;
        } else if class == "AN" {
            saw_arabic_number = true;
        }
    }
    !(is_rtl && saw_european_number && saw_arabic_number)
}

fn test_char(regexp: &JsRegExp, c: char) -> bool {
    let mut buffer = [0_u8; 4];
    regexp.test(c.encode_utf8(&mut buffer))
}

const PUNYCODE_BASE: f64 = 36.0;
const PUNYCODE_TMIN: f64 = 1.0;
const PUNYCODE_TMAX: f64 = 26.0;
const PUNYCODE_SKEW: f64 = 38.0;
const PUNYCODE_DAMP: f64 = 700.0;
const PUNYCODE_INITIAL_BIAS: f64 = 72.0;
const PUNYCODE_INITIAL_N: f64 = 128.0;

/// The Punycode threshold for digit position `position` (JS number arithmetic).
fn threshold(position: f64, bias: f64) -> f64 {
    if position <= bias {
        PUNYCODE_TMIN
    } else if position >= bias + PUNYCODE_TMAX {
        PUNYCODE_TMAX
    } else {
        position - bias
    }
}

fn adapt(delta: f64, num_points: f64, first_time: bool) -> f64 {
    let mut delta = if first_time {
        (delta / PUNYCODE_DAMP).floor()
    } else {
        f64::from(to_int32(delta) >> 1)
    };
    delta += (delta / num_points).floor();
    let mut scaled = 0.0;
    while delta > (((PUNYCODE_BASE - PUNYCODE_TMIN) * PUNYCODE_TMAX) / 2.0).floor() {
        delta = (delta / (PUNYCODE_BASE - PUNYCODE_TMIN)).floor();
        scaled += PUNYCODE_BASE;
    }
    scaled + (((PUNYCODE_BASE - PUNYCODE_TMIN + 1.0) * delta) / (delta + PUNYCODE_SKEW)).floor()
}

/// ECMAScript `ToInt32` (the operand conversion of `>>`).
fn to_int32(value: f64) -> i32 {
    if !value.is_finite() {
        return 0;
    }
    let wrapped = value.trunc().rem_euclid(4_294_967_296.0);
    let signed = if wrapped >= 2_147_483_648.0 {
        wrapped - 4_294_967_296.0
    } else {
        wrapped
    };
    // `signed` is integral and within the i32 range by construction.
    #[allow(clippy::cast_possible_truncation)]
    let result = signed as i32;
    result
}

/// `TypeBox`'s Punycode `Decode`: the decoded code points, or `None` where the
/// TS throws (bad input, or `String.fromCodePoint` rejecting a value).
#[allow(clippy::float_cmp)] // JS `===` on numbers: exact comparison is the semantics.
fn decode(value: &str) -> Option<Vec<u32>> {
    let units: Vec<u16> = value.encode_utf16().collect();
    let delimiter = units.iter().rposition(|unit| *unit == u16::from(b'-'));
    let mut output: Vec<f64> = Vec::new();
    if let Some(delimiter) = delimiter.filter(|delimiter| *delimiter > 0) {
        for unit in &units[..delimiter] {
            if *unit >= 128 {
                return None;
            }
            output.push(f64::from(*unit));
        }
    }
    let mut input_index = delimiter.map_or(0, |delimiter| delimiter + 1);
    let mut code = PUNYCODE_INITIAL_N;
    let mut insertion = 0.0_f64;
    let mut bias = PUNYCODE_INITIAL_BIAS;
    while input_index < units.len() {
        let old_insertion = insertion;
        let mut weight = 1.0;
        let mut position = PUNYCODE_BASE;
        loop {
            let unit = *units.get(input_index)?;
            input_index += 1;
            let digit = match unit {
                0x61..=0x7A => unit - 0x61,
                0x30..=0x39 => unit - 0x30 + 26,
                _ => return None,
            };
            let digit = f64::from(digit);
            insertion += digit * weight;
            let limit = threshold(position, bias);
            if digit < limit {
                break;
            }
            weight *= PUNYCODE_BASE - limit;
            position += PUNYCODE_BASE;
        }
        let output_length = usize_to_f64(output.len() + 1);
        bias = adapt(
            insertion - old_insertion,
            output_length,
            old_insertion == 0.0,
        );
        code += (insertion / output_length).floor();
        insertion %= output_length;
        output.insert(splice_index(insertion, output.len()), code);
        insertion += 1.0;
    }
    output.into_iter().map(code_point).collect()
}

/// `Array.prototype.splice` start: `ToIntegerOrInfinity`, clamped to the length.
fn splice_index(start: f64, length: usize) -> usize {
    if start.is_nan() || start <= 0.0 {
        return 0;
    }
    let length_f64 = usize_to_f64(length);
    if start >= length_f64 {
        return length;
    }
    // `start` is in (0, length): the truncation is the spec's ToIntegerOrInfinity.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let index = start.trunc() as usize;
    index
}

/// `String.fromCodePoint` argument validation.
#[allow(clippy::float_cmp)] // `Number.isInteger`-style exact check.
fn code_point(value: f64) -> Option<u32> {
    if !(0.0..=1_114_111.0).contains(&value) || value.trunc() != value {
        return None;
    }
    // Checked integral and within the code point range above.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let point = value as u32;
    Some(point)
}

/// The decoded string, unless it contains a lone surrogate.
fn code_points_to_string(points: &[u32]) -> Option<String> {
    points.iter().map(|point| char::from_u32(*point)).collect()
}

fn digit_to_char(digit: f64) -> char {
    let (offset, digit) = if digit < 26.0 {
        (0x61, digit)
    } else {
        (0x30, digit - 26.0)
    };
    // Punycode digits are integers in 0..36 by construction.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let value = digit as u32;
    char::from_u32(offset + value).unwrap_or('?')
}

/// `TypeBox`'s Punycode `Encode` (used only for the A-label length limit).
#[allow(clippy::float_cmp)] // JS `===` on code points: exact comparison is the semantics.
fn encode(input: &str) -> String {
    let basic: String = input.chars().filter(char::is_ascii).collect();
    let basic_length = basic.len();
    let mut result = String::new();
    if basic_length > 0 {
        result.push_str(&basic);
        result.push('-');
    }
    let code_points: Vec<f64> = input.chars().map(|c| f64::from(u32::from(c))).collect();
    let mut code = PUNYCODE_INITIAL_N;
    let mut delta = 0.0;
    let mut bias = PUNYCODE_INITIAL_BIAS;
    let mut handled = basic_length;
    while handled < code_points.len() {
        let next_code = code_points
            .iter()
            .copied()
            .filter(|point| *point >= code)
            .fold(f64::INFINITY, f64::min);
        if next_code.is_infinite() {
            break;
        }
        delta += (next_code - code) * usize_to_f64(handled + 1);
        code = next_code;
        for point in &code_points {
            if *point < code {
                delta += 1.0;
            }
            if *point == code {
                let mut remainder = delta;
                let mut position = PUNYCODE_BASE;
                loop {
                    let limit = threshold(position, bias);
                    if remainder < limit {
                        break;
                    }
                    result.push(digit_to_char(
                        limit + ((remainder - limit) % (PUNYCODE_BASE - limit)),
                    ));
                    remainder = ((remainder - limit) / (PUNYCODE_BASE - limit)).floor();
                    position += PUNYCODE_BASE;
                }
                result.push(digit_to_char(remainder));
                bias = adapt(delta, usize_to_f64(handled + 1), handled == basic_length);
                delta = 0.0;
                handled += 1;
            }
        }
        delta += 1.0;
        code += 1.0;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn punycode_round_trips() {
        assert_eq!(encode("münchen"), "mnchen-3ya");
        assert_eq!(
            decode("mnchen-3ya")
                .and_then(|points| code_points_to_string(&points))
                .as_deref(),
            Some("münchen")
        );
        assert_eq!(decode("mnchen-3y!"), None);
    }

    #[test]
    fn hostnames_follow_typebox() {
        assert!(is_hostname("example.com"));
        assert!(is_hostname("xn--mnchen-3ya.de"));
        assert!(!is_hostname("example.com."));
        assert!(!is_hostname("-bad.com"));
        assert!(!is_hostname("ab--c.com"));
        assert!(is_idn_hostname("münchen.de"));
        assert!(is_idn_hostname("例え.テスト"));
        assert!(!is_idn_hostname("a b"));
        assert!(!is_idn_hostname("l·a"));
        assert!(is_idn_hostname("l·l"));
    }
}
