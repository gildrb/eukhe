//! Text shapes: the explicit rules (`bend/shape.bend`) the tui asks of the
//! compiled core where it used to run decision regexes. Each consumer names
//! its shapes in an id enum over its own table (`bend/image_marker_shapes.bend`
//! ids 100-109, `arg_token_shapes.bend` 110-119, `autolink_shapes.bend`
//! 120-129, `preview_shapes.bend` 130-199; entry `bend/ffi_shape.bend`), and
//! a shape answers the regex methods its callers used, one core call each:
//! the core finds the spans and the captures (in chars), Rust only slices
//! and splices.

use eukhe_bend::rules::shape::{all, first, Fit};

/// A shape of a tui table, named by its global id.
///
/// Role: lets a consumer's id enum answer the regex methods of its shapes
/// through the compiled core. An implementation only returns the shape's
/// global id (its table's base plus its index in the table); every method
/// is provided and makes exactly one core call.
pub(crate) trait TextShape: Copy {
    /// The shape's global id (`bend/ffi_shape.bend`).
    fn id(self) -> u32;

    /// Whether the shape fits somewhere in `text` (an `AtStart` shape: at
    /// its start).
    fn is_match(self, text: &str) -> bool {
        first(&[self.id()], text).is_some()
    }

    /// The leftmost fit and its captures.
    fn captures(self, text: &str) -> Option<Caps<'_>> {
        let (_, fit) = first(&[self.id()], text)?;
        let mut bytes = ByteCursor::new(text);
        Some(Caps::new(text, &mut bytes, fit))
    }

    /// Every fit left to right, none overlapping, with its captures.
    fn captures_iter(self, text: &str) -> Vec<Caps<'_>> {
        let mut bytes = ByteCursor::new(text);
        all(self.id(), text)
            .into_iter()
            .map(|fit| Caps::new(text, &mut bytes, fit))
            .collect()
    }

    /// The leftmost fit.
    fn find(self, text: &str) -> Option<Match<'_>> {
        let (_, fit) = first(&[self.id()], text)?;
        let mut bytes = ByteCursor::new(text);
        Some(Match::new(text, &mut bytes, &fit))
    }

    /// Every fit left to right in chars (start, end), none overlapping.
    fn char_spans(self, text: &str) -> Vec<(usize, usize)> {
        all(self.id(), text)
            .into_iter()
            .map(|fit| (fit.start, fit.end))
            .collect()
    }

    /// `text` with the leftmost fit replaced by `template` (`$N`: the text
    /// of capture N, empty when it took no part; `$$`: a `$`).
    fn replace(self, text: &str, template: &str) -> String {
        let Some((_, fit)) = first(&[self.id()], text) else {
            return text.to_string();
        };
        splice(text, vec![fit], template)
    }

    /// `text` with every fit replaced by `template` (as [`Self::replace`]).
    fn replace_all(self, text: &str, template: &str) -> String {
        splice(text, all(self.id(), text), template)
    }

    /// The parts of `text` between the fits.
    fn split(self, text: &str) -> Vec<&str> {
        let mut bytes = ByteCursor::new(text);
        let mut parts = Vec::new();
        let mut last = 0;
        for fit in all(self.id(), text) {
            parts.push(&text[last..bytes.at(fit.start)]);
            last = bytes.at(fit.end);
        }
        parts.push(&text[last..]);
        parts
    }
}

/// The first of `shapes` that fits `text` (in one core call), and its
/// captures.
pub(crate) fn first_of<'t, S: TextShape>(shapes: &[S], text: &'t str) -> Option<(S, Caps<'t>)> {
    let ids: Vec<u32> = shapes.iter().map(|shape| shape.id()).collect();
    let (index, fit) = first(&ids, text)?;
    let mut bytes = ByteCursor::new(text);
    Some((shapes[index], Caps::new(text, &mut bytes, fit)))
}

/// One fit: the text it covers and its byte span.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Match<'t> {
    text: &'t str,
    start: usize,
    end: usize,
}

impl<'t> Match<'t> {
    fn new(text: &'t str, bytes: &mut ByteCursor<'t>, fit: &Fit) -> Self {
        let start = bytes.at(fit.start);
        let end = bytes.at(fit.end);
        Match {
            text: &text[start..end],
            start,
            end,
        }
    }

    pub(crate) fn as_str(&self) -> &'t str {
        self.text
    }

    pub(crate) fn start(&self) -> usize {
        self.start
    }

    pub(crate) fn end(&self) -> usize {
        self.end
    }
}

/// One fit with its captures.
#[derive(Clone, Debug)]
pub(crate) struct Caps<'t> {
    whole: Match<'t>,
    groups: Vec<Option<String>>,
}

impl<'t> Caps<'t> {
    fn new(text: &'t str, bytes: &mut ByteCursor<'t>, fit: Fit) -> Self {
        Caps {
            whole: Match::new(text, bytes, &fit),
            groups: fit.captures,
        }
    }

    /// Capture `index` (0: the whole fit); `None` when it took no part.
    pub(crate) fn get(&self, index: usize) -> Option<&str> {
        match index.checked_sub(1) {
            None => Some(self.whole.as_str()),
            Some(group) => self.groups.get(group)?.as_deref(),
        }
    }

    /// The byte offset in the text where the whole fit ends.
    pub(crate) fn end(&self) -> usize {
        self.whole.end()
    }
}

/// Char offsets to byte offsets over one text, for offsets that never go
/// back (the fits of one text come left to right).
struct ByteCursor<'t> {
    text: &'t str,
    chars: usize,
    byte: usize,
}

impl<'t> ByteCursor<'t> {
    fn new(text: &'t str) -> Self {
        ByteCursor {
            text,
            chars: 0,
            byte: 0,
        }
    }

    /// The byte offset of char `index` (the text's length past its end).
    fn at(&mut self, index: usize) -> usize {
        if index < self.chars {
            self.chars = 0;
            self.byte = 0;
        }
        for ch in self.text[self.byte..].chars() {
            if self.chars == index {
                break;
            }
            self.byte += ch.len_utf8();
            self.chars += 1;
        }
        self.byte
    }
}

/// `text` with each fit replaced by `template` expanded with its captures.
fn splice(text: &str, fits: Vec<Fit>, template: &str) -> String {
    let mut bytes = ByteCursor::new(text);
    let mut out = String::with_capacity(text.len());
    let mut last = 0;
    for fit in fits {
        let caps = Caps::new(text, &mut bytes, fit);
        out.push_str(&text[last..caps.whole.start()]);
        expand(template, &caps, &mut out);
        last = caps.whole.end();
    }
    out.push_str(&text[last..]);
    out
}

/// `template` with `$N` replaced by capture N's text (empty when it took no
/// part) and `$$` by `$`, as a regex replacement reads them: the name after
/// `$` is its longest run of ASCII letters, digits and `_`, and a name that
/// is no number names no capture.
fn expand(template: &str, caps: &Caps<'_>, out: &mut String) {
    let mut rest = template;
    while let Some(dollar) = rest.find('$') {
        out.push_str(&rest[..dollar]);
        rest = &rest[dollar + 1..];
        if let Some(after) = rest.strip_prefix('$') {
            out.push('$');
            rest = after;
            continue;
        }
        let name_len = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        if name_len == 0 {
            out.push('$');
            continue;
        }
        if let Ok(index) = rest[..name_len].parse::<usize>() {
            out.push_str(caps.get(index).unwrap_or(""));
        }
        rest = &rest[name_len..];
    }
    out.push_str(rest);
}
