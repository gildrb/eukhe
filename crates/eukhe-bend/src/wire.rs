//! The wire format of the compiled Bend core, Rust side: `Writer` encodes
//! a request, `Reader` decodes a reply. It mirrors `bend/wire.bend` (the
//! grammar is `crates/eukhe-bend/WIRE.md`; LAWS.bend section `wire` pins
//! the Bend side). Decoding is total: every input that is not an encoding
//! is a `WireError`, never a default.

use std::fmt;

/// The largest Nat the wire carries: 14 decimal digits.
pub const NAT_MAX: u64 = 99_999_999_999_999;

/// The longest String the wire carries, in chars: Bend's String codec is a
/// flat loop, but a model that recurses over a String takes one stack frame
/// per char, and the shim's 256 MiB evaluation stack holds about 16M of them
/// (a deeper run faults and ends the process), so `Writer::str` refuses more
/// than half of that.
pub const STR_MAX: usize = 8 << 20;

/// Why a value could not be written or read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WireError {
    /// `Writer::nat` (or a count) got a value above [`NAT_MAX`].
    NatTooLarge(u64),
    /// `Writer::str` got a string of more than [`STR_MAX`] chars.
    StrTooLong(usize),
    /// The reply is the error form: the text after `E `.
    Rejected(String),
    /// The reply does not hold the expected value at byte offset `at`.
    Malformed { at: usize, expected: &'static str },
    /// `Reader::end`: input is left at byte offset `at`.
    Trailing { at: usize },
}

impl fmt::Display for WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WireError::NatTooLarge(n) => write!(f, "wire: {n} is above the largest Nat {NAT_MAX}"),
            WireError::StrTooLong(n) => {
                write!(
                    f,
                    "wire: a string of {n} chars is above the longest {STR_MAX}"
                )
            }
            WireError::Rejected(text) => write!(f, "bend core rejected the request: {text}"),
            WireError::Malformed { at, expected } => {
                write!(f, "wire: expected {expected} at byte {at}")
            }
            WireError::Trailing { at } => write!(f, "wire: input left over at byte {at}"),
        }
    }
}

impl std::error::Error for WireError {}

/// Encodes one request: each method appends one value.
#[derive(Debug, Default)]
pub struct Writer {
    buf: String,
    error: Option<WireError>,
}

impl Writer {
    #[must_use]
    pub fn new() -> Writer {
        Writer::default()
    }

    /// A Nat: canonical decimal, then `,`. Above [`NAT_MAX`] the writer
    /// records `NatTooLarge` and `finish` answers it.
    pub fn nat(&mut self, n: u64) -> &mut Writer {
        if n > NAT_MAX {
            if self.error.is_none() {
                self.error = Some(WireError::NatTooLarge(n));
            }
            return self;
        }
        self.digits(n)
    }

    fn digits(&mut self, mut n: u64) -> &mut Writer {
        let mut buf = [0u8; 20];
        let mut i = buf.len();
        loop {
            i -= 1;
            // n % 10 < 10, so the digit is ASCII.
            buf[i] = b'0' + (n % 10) as u8;
            n /= 10;
            if n == 0 {
                break;
            }
        }
        for &b in &buf[i..] {
            self.buf.push(char::from(b));
        }
        self.buf.push(',');
        self
    }

    pub fn u32(&mut self, n: u32) -> &mut Writer {
        self.digits(u64::from(n))
    }

    pub fn bool(&mut self, b: bool) -> &mut Writer {
        self.buf.push(if b { 'T' } else { 'F' });
        self
    }

    /// A string: its length in chars, then its chars.
    /// Above [`STR_MAX`] chars the writer records `StrTooLong`.
    pub fn str(&mut self, s: &str) -> &mut Writer {
        let n = s.chars().count();
        if n > STR_MAX {
            if self.error.is_none() {
                self.error = Some(WireError::StrTooLong(n));
            }
            return self;
        }
        self.count(n);
        self.buf.push_str(s);
        self
    }

    /// A constructor's tag: its index in its type, from 0.
    pub fn tag(&mut self, t: u32) -> &mut Writer {
        self.u32(t)
    }

    /// A list's length; the items follow.
    pub fn count(&mut self, n: usize) -> &mut Writer {
        if let Ok(n) = u64::try_from(n) {
            self.nat(n)
        } else {
            if self.error.is_none() {
                self.error = Some(WireError::NatTooLarge(u64::MAX));
            }
            self
        }
    }

    /// `Maybe`: None.
    pub fn none(&mut self) -> &mut Writer {
        self.tag(0)
    }

    /// `Maybe`: Some; the value follows.
    pub fn some(&mut self) -> &mut Writer {
        self.tag(1)
    }

    /// The request, and the writer emptied for the next one.
    ///
    /// # Errors
    ///
    /// The first error a method recorded ([`WireError::NatTooLarge`],
    /// [`WireError::StrTooLong`]).
    pub fn finish(&mut self) -> Result<String, WireError> {
        if let Some(e) = self.error.take() {
            return Err(e);
        }
        Ok(std::mem::take(&mut self.buf))
    }
}

/// Decodes one reply: each method reads one value.
#[derive(Debug)]
pub struct Reader<'a> {
    src: &'a str,
    at: usize,
}

/// Every `Reader` method that reads a value fails with
/// [`WireError::Malformed`] (at the value's byte offset, the offset
/// unchanged) when the input there is not an encoding of that value.
impl<'a> Reader<'a> {
    /// A reader over a reply.
    ///
    /// # Errors
    ///
    /// [`WireError::Rejected`] with the text when the reply is the error
    /// form `E <text>`.
    pub fn reply(reply: &'a str) -> Result<Reader<'a>, WireError> {
        if let Some(text) = reply.strip_prefix("E ") {
            return Err(WireError::Rejected(text.to_string()));
        }
        Ok(Reader { src: reply, at: 0 })
    }

    /// A reader over a request (tests, and a stepper's event echo).
    #[must_use]
    pub fn new(src: &'a str) -> Reader<'a> {
        Reader { src, at: 0 }
    }

    fn malformed_at(at: usize, expected: &'static str) -> WireError {
        WireError::Malformed { at, expected }
    }

    /// A Nat: 1 to 14 digits, no leading zero, then `,`.
    ///
    /// # Errors
    ///
    /// [`WireError::Malformed`] (see the impl docs).
    pub fn nat(&mut self) -> Result<u64, WireError> {
        let rest = &self.src.as_bytes()[self.at..];
        let digits = rest.iter().take_while(|b| b.is_ascii_digit()).count();
        let canonical = digits == 1 || (digits > 1 && rest[0] != b'0');
        if digits == 0 || digits > 14 || !canonical || rest.get(digits) != Some(&b',') {
            return Err(Self::malformed_at(self.at, "a Nat"));
        }
        let n = rest[..digits]
            .iter()
            .fold(0u64, |acc, b| acc * 10 + u64::from(b - b'0'));
        self.at += digits + 1;
        Ok(n)
    }

    /// A U32: a Nat that is at most `u32::MAX`.
    ///
    /// # Errors
    ///
    /// [`WireError::Malformed`] (see the impl docs).
    pub fn u32(&mut self) -> Result<u32, WireError> {
        let at = self.at;
        let n = self.nat()?;
        u32::try_from(n).map_err(|_| {
            self.at = at;
            Self::malformed_at(at, "a U32")
        })
    }

    /// A Bool: `T` or `F`.
    ///
    /// # Errors
    ///
    /// [`WireError::Malformed`] (see the impl docs).
    pub fn bool(&mut self) -> Result<bool, WireError> {
        let b = match self.src.as_bytes().get(self.at) {
            Some(b'T') => true,
            Some(b'F') => false,
            Some(_) | None => return Err(Self::malformed_at(self.at, "a Bool")),
        };
        self.at += 1;
        Ok(b)
    }

    /// A string: its length in chars, then its chars.
    ///
    /// # Errors
    ///
    /// [`WireError::Malformed`] (see the impl docs), also when fewer chars
    /// follow than the length says.
    pub fn str(&mut self) -> Result<&'a str, WireError> {
        let start = self.at;
        let n = self.nat()?;
        let body = &self.src[self.at..];
        let end = usize::try_from(n).ok().and_then(|k| {
            if k == 0 {
                Some(0)
            } else {
                body.char_indices()
                    .nth(k - 1)
                    .map(|(i, c)| i + c.len_utf8())
            }
        });
        let Some(len) = end else {
            self.at = start;
            return Err(Self::malformed_at(start, "a String"));
        };
        self.at += len;
        Ok(&body[..len])
    }

    /// A constructor's tag.
    ///
    /// # Errors
    ///
    /// [`WireError::Malformed`] (see the impl docs).
    pub fn tag(&mut self) -> Result<u32, WireError> {
        self.u32()
    }

    /// The tag of a type with `ctors` constructors.
    ///
    /// # Errors
    ///
    /// [`WireError::Malformed`] at the tag's offset, `expected` naming the
    /// type, for a tag at or past `ctors` (and as in the impl docs).
    pub fn tag_of(&mut self, ctors: u32, expected: &'static str) -> Result<u32, WireError> {
        let at = self.at;
        let t = self.u32()?;
        if t < ctors {
            Ok(t)
        } else {
            self.at = at;
            Err(Self::malformed_at(at, expected))
        }
    }

    /// A list's length; the items follow.
    ///
    /// # Errors
    ///
    /// [`WireError::Malformed`] (see the impl docs).
    pub fn count(&mut self) -> Result<usize, WireError> {
        let at = self.at;
        let n = self.nat()?;
        usize::try_from(n).map_err(|_| {
            self.at = at;
            Self::malformed_at(at, "a count")
        })
    }

    /// `Maybe`: true for Some (the value follows), false for None.
    ///
    /// # Errors
    ///
    /// [`WireError::Malformed`] for a tag other than 0 and 1.
    pub fn maybe(&mut self) -> Result<bool, WireError> {
        Ok(self.tag_of(2, "a Maybe tag")? == 1)
    }

    /// Nothing is left.
    ///
    /// # Errors
    ///
    /// [`WireError::Trailing`] when input is left.
    pub fn end(self) -> Result<(), WireError> {
        if self.at == self.src.len() {
            Ok(())
        } else {
            Err(WireError::Trailing { at: self.at })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn writes_the_grammar_examples() {
        let s = Writer::new()
            .str("héllo")
            .nat(3)
            .count(2)
            .str("a")
            .str("bc")
            .some()
            .u32(7)
            .bool(true)
            .finish();
        assert_eq!(s, Ok("5,héllo3,2,1,a2,bc1,7,T".to_string()));
        assert_eq!(Writer::new().nat(0).finish(), Ok("0,".to_string()));
    }

    #[test]
    fn reads_what_it_writes() {
        let s = Writer::new()
            .nat(NAT_MAX)
            .u32(u32::MAX)
            .bool(false)
            .str("日本 🦀")
            .str("")
            .none()
            .finish()
            .unwrap_or_default();
        let mut r = Reader::new(&s);
        assert_eq!(r.nat(), Ok(NAT_MAX));
        assert_eq!(r.u32(), Ok(u32::MAX));
        assert_eq!(r.bool(), Ok(false));
        assert_eq!(r.str(), Ok("日本 🦀"));
        assert_eq!(r.str(), Ok(""));
        assert_eq!(r.maybe(), Ok(false));
        assert_eq!(r.end(), Ok(()));
    }

    #[test]
    fn refuses_a_nat_above_the_bound() {
        assert_eq!(
            Writer::new().nat(NAT_MAX + 1).str("x").finish(),
            Err(WireError::NatTooLarge(NAT_MAX + 1))
        );
        let long = "x".repeat(STR_MAX + 1);
        assert_eq!(
            Writer::new().str(&long).finish(),
            Err(WireError::StrTooLong(STR_MAX + 1))
        );
    }

    #[test]
    fn every_malformed_value_is_an_error() {
        for bad in ["", "01,", "12", ",", "100000000000000,", "x,", "-1,"] {
            assert!(Reader::new(bad).nat().is_err(), "{bad:?}");
        }
        assert!(Reader::new("4294967296,").u32().is_err());
        assert!(Reader::new("t").bool().is_err());
        assert!(Reader::new("3,ab").str().is_err());
        assert!(Reader::new("2,").maybe().is_err());
        assert_eq!(Reader::new("0,x").str().map(str::len), Ok(0));
        let mut r = Reader::new("1,x");
        assert_eq!(r.nat(), Ok(1));
        assert_eq!(r.end(), Err(WireError::Trailing { at: 2 }));
    }

    #[test]
    fn the_error_form_is_rejected() {
        assert_eq!(
            Reader::reply("E unknown entry").map(|_| ()),
            Err(WireError::Rejected("unknown entry".to_string()))
        );
        assert!(Reader::reply("5,hello").is_ok());
    }

    /// Rust-written values cross the real call and Bend writes them back
    /// byte for byte (`bend/ffi_wire.bend`): the two sides read one grammar.
    #[test]
    fn bend_reads_back_what_rust_writes() {
        let cases: [(u64, u32, bool, &str, &[u64]); 4] = [
            (0, 0, false, "", &[]),
            (42, 7, true, "héllo", &[1, 22, 333]),
            (NAT_MAX, u32::MAX, false, "日本 🦀 \"q\",E", &[NAT_MAX, 0]),
            (10, 4_000_000_000, true, "0,1,", &[9; 20]),
        ];
        for (n, x, b, s, xs) in cases {
            let mut w = Writer::new();
            w.nat(n).u32(x).bool(b).str(s).count(xs.len());
            for &item in xs {
                w.nat(item);
            }
            let request = w.finish().expect("every value fits");
            let reply = crate::call(crate::Entry::Wire, &request).expect("the core answers");
            assert_eq!(reply, request);
            let mut r = Reader::reply(&reply).expect("a value, not the error form");
            assert_eq!(
                (r.nat(), r.u32(), r.bool(), r.str()),
                (Ok(n), Ok(x), Ok(b), Ok(s))
            );
        }
    }

    /// Bend refuses what the grammar refuses: every malformed request
    /// answers the error form, never a value.
    #[test]
    fn bend_refuses_malformed_requests() {
        for bad in [
            "",
            "01,0,T0,0,",
            "1,4294967296,T0,0,",
            "1,1,X0,0,",
            "1,1,T3,ab0,",
            "1,1,T0,2,1,",
            "1,1,T0,0,x",
            "100000000000000,1,T0,0,",
        ] {
            let reply = crate::call(crate::Entry::Wire, bad).expect("the core answers");
            assert_eq!(
                Reader::reply(&reply).map(|_| ()),
                Err(WireError::Rejected("malformed wire request".to_string())),
                "{bad:?}"
            );
        }
    }
}
