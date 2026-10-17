//! Numbers spelled as English words for the G2P, the way kokoro-js
//! normalizes them: years in pairs (`1984` → nineteen eighty-four),
//! cardinals, decimals digit by digit, ordinals (`21st`).

/// A number as written: its digits, its decimal digits, and how it was
/// written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Number {
    /// The integer digits, group commas removed.
    pub(crate) digits: String,
    /// The digits after the decimal point; empty: none.
    pub(crate) fraction: String,
    pub(crate) form: NumberForm,
}

/// How a number was written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NumberForm {
    /// Plain digits (`1984`): four of them read as a year.
    Plain,
    /// With group commas (`1,984`): never a year.
    Grouped,
    /// With an ordinal suffix (`21st`).
    Ordinal,
}

const ONES: [&str; 20] = [
    "zero",
    "one",
    "two",
    "three",
    "four",
    "five",
    "six",
    "seven",
    "eight",
    "nine",
    "ten",
    "eleven",
    "twelve",
    "thirteen",
    "fourteen",
    "fifteen",
    "sixteen",
    "seventeen",
    "eighteen",
    "nineteen",
];
const TENS: [&str; 10] = [
    "", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety",
];
const SCALES: [(u64, &str); 4] = [
    (1_000_000_000_000, "trillion"),
    (1_000_000_000, "billion"),
    (1_000_000, "million"),
    (1_000, "thousand"),
];
/// Cardinal words → their ordinals (the last word of an ordinal number).
const ORDINALS: [(&str, &str); 33] = [
    ("zero", "zeroth"),
    ("one", "first"),
    ("two", "second"),
    ("three", "third"),
    ("four", "fourth"),
    ("five", "fifth"),
    ("six", "sixth"),
    ("seven", "seventh"),
    ("eight", "eighth"),
    ("nine", "ninth"),
    ("ten", "tenth"),
    ("eleven", "eleventh"),
    ("twelve", "twelfth"),
    ("thirteen", "thirteenth"),
    ("fourteen", "fourteenth"),
    ("fifteen", "fifteenth"),
    ("sixteen", "sixteenth"),
    ("seventeen", "seventeenth"),
    ("eighteen", "eighteenth"),
    ("nineteen", "nineteenth"),
    ("twenty", "twentieth"),
    ("thirty", "thirtieth"),
    ("forty", "fortieth"),
    ("fifty", "fiftieth"),
    ("sixty", "sixtieth"),
    ("seventy", "seventieth"),
    ("eighty", "eightieth"),
    ("ninety", "ninetieth"),
    ("hundred", "hundredth"),
    ("thousand", "thousandth"),
    ("million", "millionth"),
    ("billion", "billionth"),
    ("trillion", "trillionth"),
];

impl Number {
    /// The words of the number.
    pub(crate) fn words(&self) -> Vec<&'static str> {
        let mut words = Vec::new();
        match self.digits.parse::<u64>() {
            Ok(value) if self.digits.len() <= 15 => match self.form {
                NumberForm::Plain if self.digits.len() == 4 && self.fraction.is_empty() => {
                    year(value, &mut words);
                }
                NumberForm::Plain | NumberForm::Grouped | NumberForm::Ordinal => {
                    cardinal(value, &mut words);
                }
            },
            Ok(_) | Err(_) => words.extend(digit_words(&self.digits)),
        }
        if !self.fraction.is_empty() {
            words.push("point");
            words.extend(digit_words(&self.fraction));
        }
        match self.form {
            NumberForm::Ordinal => {
                if let Some(last) = words.last_mut() {
                    if let Some((_, ordinal)) = ORDINALS.iter().find(|(word, _)| *word == *last) {
                        *last = ordinal;
                    }
                }
            }
            NumberForm::Plain | NumberForm::Grouped => {}
        }
        words
    }
}

fn digit_words(digits: &str) -> impl Iterator<Item = &'static str> + '_ {
    digits
        .bytes()
        .filter(u8::is_ascii_digit)
        .map(|digit| ONES[usize::from(digit - b'0')])
}

/// A four-digit number read as a year (kokoro-js `split_num`): `1984` →
/// nineteen eighty-four, `1900` → nineteen hundred, `1905` → nineteen oh
/// five; below 1100 or within ten of a millennium, a cardinal.
fn year(value: u64, words: &mut Vec<&'static str>) {
    if value < 1_100 || value % 1_000 < 10 {
        cardinal(value, words);
        return;
    }
    let (high, low) = (value / 100, value % 100);
    below_hundred(high, words);
    if (100..=999).contains(&(value % 1_000)) && low < 10 {
        if low == 0 {
            words.push("hundred");
        } else {
            words.push("oh");
            below_hundred(low, words);
        }
    } else {
        below_hundred(low, words);
    }
}

fn cardinal(value: u64, words: &mut Vec<&'static str>) {
    if value == 0 {
        words.push(ONES[0]);
        return;
    }
    let mut rest = value;
    for (scale, name) in SCALES {
        if rest >= scale {
            below_thousand(rest / scale, words);
            words.push(name);
            rest %= scale;
        }
    }
    if rest > 0 {
        below_thousand(rest, words);
    }
}

fn below_thousand(value: u64, words: &mut Vec<&'static str>) {
    if value >= 100 {
        below_hundred(value / 100, words);
        words.push("hundred");
    }
    if !value.is_multiple_of(100) {
        below_hundred(value % 100, words);
    }
}

fn below_hundred(value: u64, words: &mut Vec<&'static str>) {
    let Ok(value) = usize::try_from(value % 100) else {
        return;
    };
    if value < 20 {
        words.push(ONES[value]);
    } else {
        words.push(TENS[value / 10]);
        if !value.is_multiple_of(10) {
            words.push(ONES[value % 10]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spell(digits: &str, fraction: &str, form: NumberForm) -> String {
        Number {
            digits: digits.to_owned(),
            fraction: fraction.to_owned(),
            form,
        }
        .words()
        .join(" ")
    }

    #[test]
    fn numbers_read_like_kokoro_js() {
        let spelled = [
            spell("1984", "", NumberForm::Plain),
            spell("1900", "", NumberForm::Plain),
            spell("1905", "", NumberForm::Plain),
            spell("2005", "", NumberForm::Plain),
            spell("2010", "", NumberForm::Plain),
            spell("1984", "", NumberForm::Grouped),
            spell("3", "14", NumberForm::Plain),
            spell("21", "", NumberForm::Ordinal),
            spell("1000000", "", NumberForm::Grouped),
            spell("0", "", NumberForm::Plain),
        ];
        assert_eq!(
            spelled,
            [
                "nineteen eighty four",
                "nineteen hundred",
                "nineteen oh five",
                "two thousand five",
                "twenty ten",
                "one thousand nine hundred eighty four",
                "three point one four",
                "twenty first",
                "one million",
                "zero",
            ]
            .map(str::to_owned)
        );
    }
}
