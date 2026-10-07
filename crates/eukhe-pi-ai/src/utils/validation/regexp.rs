//! ECMAScript regular expressions (`new RegExp(pattern, flags)` + `test`).

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::js_value::{JsError, JsErrorKind};

/// A compiled ECMAScript regular expression.
#[derive(Debug)]
pub(crate) struct JsRegExp {
    regex: regress::Regex,
    /// Non-Unicode case-insensitive mode (`i` without `u`).
    legacy_ignore_case: bool,
}

impl JsRegExp {
    /// `new RegExp(pattern, flags)`. The `SyntaxError` message keeps V8's
    /// `Invalid regular expression: /<pattern>/<flags>: ` prefix; the reason
    /// is the regress engine's wording.
    pub(crate) fn new(pattern: &str, flags: &str) -> Result<Self, JsError> {
        let legacy_ignore_case = flags.contains('i') && !flags.contains('u');
        regress::Regex::with_flags(pattern, flags)
            .map(|regex| Self {
                regex,
                legacy_ignore_case,
            })
            .map_err(|error| {
                JsError::new(
                    JsErrorKind::SyntaxError,
                    format!("Invalid regular expression: /{pattern}/{flags}: {error}"),
                )
            })
    }

    /// `TypeBox` `UnicodeRegExp(pattern)`: `new RegExp(pattern, 'u')`.
    pub(crate) fn unicode(pattern: &str) -> Result<Self, JsError> {
        Self::new(pattern, "u")
    }

    /// `regexp.test(text)` (no `g`/`y` flag: searches from the start).
    ///
    /// Without `u`, ECMAScript's `Canonicalize` never maps a non-ASCII
    /// character to ASCII, while regress folds U+017F (ſ) to `s` and U+212A
    /// (Kelvin sign) to `k`. The case-insensitive patterns here (`TypeBox`'s
    /// formats) are ASCII-only, so those two characters are tested as a
    /// non-ASCII stand-in that folds nowhere near ASCII.
    pub(crate) fn test(&self, text: &str) -> bool {
        if self.legacy_ignore_case && text.contains(['\u{017F}', '\u{212A}']) {
            let guarded = text.replace(['\u{017F}', '\u{212A}'], "\u{00FF}");
            return self.regex.find(&guarded).is_some();
        }
        self.regex.find(text).is_some()
    }

    /// The byte range of the first match (`text.replace(regexp, ...)` without `g`).
    pub(crate) fn find_range(&self, text: &str) -> Option<std::ops::Range<usize>> {
        self.regex.find(text).map(|found| found.range())
    }

    /// `regexp.exec(text)` capture groups (`None` for unmatched groups).
    pub(crate) fn captures<'t>(&self, text: &'t str) -> Option<Vec<Option<&'t str>>> {
        let found = self.regex.find(text)?;
        Some(
            found
                .groups()
                .map(|range| range.map(|range| &text[range]))
                .collect(),
        )
    }
}

/// Compiled `UnicodeRegExp` patterns shared by one validator's checks.
#[derive(Debug, Default)]
pub(crate) struct RegExpCache {
    compiled: RefCell<HashMap<String, Rc<JsRegExp>>>,
}

impl RegExpCache {
    /// `UnicodeRegExp(pattern)`, compiled once per pattern.
    pub(crate) fn unicode(&self, pattern: &str) -> Result<Rc<JsRegExp>, JsError> {
        if let Some(regexp) = self.compiled.borrow().get(pattern) {
            return Ok(Rc::clone(regexp));
        }
        let regexp = Rc::new(JsRegExp::unicode(pattern)?);
        self.compiled
            .borrow_mut()
            .insert(pattern.to_owned(), Rc::clone(&regexp));
        Ok(regexp)
    }
}
/// A fixed `TypeBox` pattern as a lazily compiled static. Panics only if the
/// constant pattern itself is invalid, which the tests rule out.
macro_rules! static_regexp {
    ($name:ident, $pattern:expr, $flags:expr) => {
        static $name: std::sync::LazyLock<$crate::utils::validation::regexp::JsRegExp> =
            std::sync::LazyLock::new(|| {
                $crate::utils::validation::regexp::JsRegExp::new($pattern, $flags)
                    .unwrap_or_else(|error| panic!("invalid built-in pattern: {}", error.message))
            });
    };
}
pub(crate) use static_regexp;
