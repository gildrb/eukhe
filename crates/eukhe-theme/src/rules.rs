//! The theme rules this crate asks for: a theme file read and completed,
//! and what a name resolves to over the files the sources reach. They run
//! in the compiled Bend core (`bend/theme/`, entry `bend/ffi_theme.bend`;
//! `laws/theme.bend`). This crate depends on nothing, so a crate that may
//! call the core (eukhe-core, eukhe-tui) passes them in as a
//! [`ThemeRules`], as eukhe-types takes its `PeerRule`. This crate reads
//! the files, decodes their JSON ([`RawTheme`]) and words the warnings.

use crate::palette::Palette;
use crate::token::Token;

/// A JSON value of a theme file, as the rules read it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawValue {
    /// A string, with the index of the file's variable of that name.
    Str { text: String, var: Option<usize> },
    /// A number, as JSON writes it.
    Num(String),
    /// Any other value (null, a bool, an array, an object), as written.
    Other(String),
}

/// A theme object decoded: its name, its variables and colors in key
/// order (each color with the token its key names), and its export page,
/// card and info backgrounds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawTheme {
    pub name: String,
    pub vars: Vec<(String, RawValue)>,
    pub colors: Vec<(String, Option<Token>, RawValue)>,
    pub export: [Option<RawValue>; 3],
}

/// A file the sources reach: from the custom directory or not, its stem
/// when that is text, and its theme object (`None`: unreadable, or no
/// theme object).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RawSource<'a> {
    pub custom: bool,
    pub stem: Option<&'a str>,
    pub theme: Option<&'a RawTheme>,
}

/// The theme a name picks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Choice {
    /// The builtin at this index of [`crate::BUILTIN_THEME_NAMES`].
    Builtin(usize),
    /// The source at this index, and its palette.
    File(usize, Box<Palette>),
}

/// Why a name picks no theme.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cause {
    /// The source at this index did not load and blames the name.
    Failed(usize),
    NotFound,
}

/// How a source read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Loaded,
    /// A theme object that is not valid, and why.
    Invalid(String),
    NoTheme,
}

/// What a name resolves to over the sources.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Picked {
    pub theme: Choice,
    /// Why the name picks no theme (it then warns).
    pub cause: Option<Cause>,
    /// Each source whose name an earlier source took and whose palette
    /// differs, with that earlier source.
    pub clashes: Vec<(usize, usize)>,
    /// The other sources that did not load.
    pub broken: Vec<usize>,
    /// How each source read.
    pub outcomes: Vec<Outcome>,
}

/// The theme rules: the compiled core's, passed in by a crate that may
/// call it. Each rule is a pure decision over what this crate read.
#[derive(Debug, Clone, Copy)]
pub struct ThemeRules {
    /// The palette a theme object completes to, or why it is invalid.
    pub load: fn(&RawTheme) -> Result<Palette, String>,
    /// What a name (empty: the default theme) resolves to over the
    /// sources, in load order.
    pub resolve: fn(&str, &[RawSource<'_>]) -> Picked,
}
