//! A theme file decoded ([`RawTheme`]) and the complete [`Palette`] the
//! theme rules ([`ThemeRules`]) give it: every token defined, the color
//! each token paints, light or dark.

use std::collections::BTreeMap;
use std::path::Path;

use serde::Deserialize;
use serde_json::Value;

use crate::color::{Mode, Rgb};
use crate::rules::{RawTheme, RawValue, ThemeRules};
use crate::token::Token;

/// The theme an empty name and every failed lookup resolve to.
pub const DEFAULT_THEME_NAME: &str = "eukhe";

/// The builtin theme of the light mode.
pub const LIGHT_THEME_NAME: &str = "light";

/// The bundled theme names, in lookup order (the rules' builtins 0, 1, 2).
pub const BUILTIN_THEME_NAMES: [&str; 3] = [DEFAULT_THEME_NAME, "dark", LIGHT_THEME_NAME];

/// The bundled theme file of `name`.
fn builtin_json(name: &str) -> Option<&'static str> {
    match name {
        DEFAULT_THEME_NAME => Some(include_str!("../themes/eukhe.json")),
        "dark" => Some(include_str!("../themes/dark.json")),
        LIGHT_THEME_NAME => Some(include_str!("../themes/light.json")),
        _ => None,
    }
}

/// A token's color after variable resolution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ColorValue {
    /// `""`: the terminal's default color for the token's layer.
    Default,
    /// `0`-`255`: an xterm-256 palette index.
    Indexed(u8),
    /// `#rrggbb`.
    Rgb(Rgb),
}

/// The HTML export's three backgrounds a theme may set in its `export`
/// section.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportSurface {
    Page,
    Card,
    Info,
}

/// Why theme text did not become a palette.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ThemeError {
    /// Not a theme object: bad JSON, a wrong shape or an unknown key.
    Parse(String),
    /// A theme object named `name` whose colors are not valid.
    Invalid { name: String, reason: String },
}

/// A theme file (the `theme-schema.json` shape); `$schema` rides along.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ThemeFile {
    #[serde(rename = "$schema")]
    _schema: Option<String>,
    name: String,
    #[serde(default)]
    vars: BTreeMap<String, Value>,
    colors: BTreeMap<String, Value>,
    #[serde(default)]
    export: ExportSection,
}

#[derive(Deserialize, Default)]
#[serde(deny_unknown_fields)]
struct ExportSection {
    #[serde(rename = "pageBg")]
    page: Option<Value>,
    #[serde(rename = "cardBg")]
    card: Option<Value>,
    #[serde(rename = "infoBg")]
    info: Option<Value>,
}

impl RawTheme {
    /// Decode theme file text: its keys in order, each string with the
    /// index of the variable it names, other values as JSON writes them.
    ///
    /// # Errors
    ///
    /// The decoder's message when the text is not a theme object (bad
    /// JSON, a wrong shape, an unknown top-level or export key).
    pub fn decode(raw: &str) -> Result<RawTheme, String> {
        let file: ThemeFile = serde_json::from_str(raw).map_err(|error| error.to_string())?;
        let names: Vec<&str> = file.vars.keys().map(String::as_str).collect();
        let value = |value: &Value| match value {
            Value::String(text) => RawValue::Str {
                text: text.clone(),
                var: names.iter().position(|name| name == text),
            },
            Value::Number(number) => RawValue::Num(number.to_string()),
            Value::Null | Value::Bool(_) | Value::Array(_) | Value::Object(_) => {
                RawValue::Other(value.to_string())
            }
        };
        Ok(RawTheme {
            vars: file
                .vars
                .iter()
                .map(|(name, v)| (name.clone(), value(v)))
                .collect(),
            colors: file
                .colors
                .iter()
                .map(|(key, v)| (key.clone(), Token::from_name(key), value(v)))
                .collect(),
            export: [
                file.export.page.as_ref().map(value),
                file.export.card.as_ref().map(value),
                file.export.info.as_ref().map(value),
            ],
            name: file.name,
        })
    }
}

/// A complete theme: a value for every token and the color it paints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Palette {
    name: String,
    colors: [ColorValue; Token::ALL.len()],
    paints: [Rgb; Token::ALL.len()],
    /// The file's own `background`, when it is `#rrggbb`.
    declared_background: Option<Rgb>,
    export: [Option<Rgb>; 3],
    mode: Mode,
}

/// The parts of a [`Palette`], as the theme rules complete them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PaletteParts {
    pub name: String,
    /// The value of each token, in [`Token::ALL`] order.
    pub colors: [ColorValue; Token::ALL.len()],
    /// The color each token paints where the terminal cannot be asked.
    pub paints: [Rgb; Token::ALL.len()],
    /// The file's own `background`, when it is `#rrggbb`.
    pub declared_background: Option<Rgb>,
    /// The export page, card and info backgrounds the file sets.
    pub export: [Option<Rgb>; 3],
    pub mode: Mode,
}

impl Palette {
    /// The palette the theme rules completed.
    #[must_use]
    pub fn new(parts: PaletteParts) -> Palette {
        let PaletteParts {
            name,
            colors,
            paints,
            declared_background,
            export,
            mode,
        } = parts;
        Palette {
            name,
            colors,
            paints,
            declared_background,
            export,
            mode,
        }
    }

    /// Decode and complete theme file text.
    ///
    /// # Errors
    ///
    /// [`ThemeError::Parse`] when the text is not a theme object;
    /// [`ThemeError::Invalid`] when the rules find its colors invalid.
    pub fn parse(raw: &str, rules: ThemeRules) -> Result<Palette, ThemeError> {
        let theme = RawTheme::decode(raw).map_err(ThemeError::Parse)?;
        (rules.load)(&theme).map_err(|reason| ThemeError::Invalid {
            name: theme.name,
            reason,
        })
    }

    /// Read, decode and complete the theme file at `path`.
    ///
    /// # Errors
    ///
    /// A [`LoadFailure`] naming the path and, when the file is a theme
    /// object, the name it advertises.
    pub fn load(path: &Path, rules: ThemeRules) -> Result<Palette, LoadFailure> {
        let raw = std::fs::read_to_string(path).map_err(|error| LoadFailure {
            name: None,
            message: format!("Failed to read theme {}: {error}", path.display()),
        })?;
        Palette::parse(&raw, rules).map_err(|error| LoadFailure::of(path, error))
    }

    /// The builtin theme `name` ([`BUILTIN_THEME_NAMES`]).
    ///
    /// # Panics
    ///
    /// Panics when a bundled file is invalid: the bundled files are
    /// build-time data, and a test loads each one.
    #[must_use]
    pub fn builtin(name: &str, rules: ThemeRules) -> Option<Palette> {
        let raw = builtin_json(name)?;
        Some(
            Palette::parse(raw, rules)
                .unwrap_or_else(|error| panic!("builtin theme {name} is valid: {error:?}")),
        )
    }

    /// The default theme ([`DEFAULT_THEME_NAME`]).
    ///
    /// # Panics
    ///
    /// Never: the default theme is a builtin, and the builtins are valid.
    #[must_use]
    pub fn default_theme(rules: ThemeRules) -> Palette {
        Palette::builtin(DEFAULT_THEME_NAME, rules).expect("the default theme is a builtin")
    }

    /// The name the theme advertises.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The token's value as the file set it (or as it fell back).
    #[must_use]
    pub fn value(&self, token: Token) -> ColorValue {
        self.colors[token as usize]
    }

    /// The color the token paints where the terminal cannot be asked.
    #[must_use]
    pub fn rgb(&self, token: Token) -> Rgb {
        self.paints[token as usize]
    }

    /// The theme's mode, from its background's luminance.
    #[must_use]
    pub fn mode(&self) -> Mode {
        self.mode
    }

    /// The file's own `background` key, when it is `#rrggbb` (the
    /// terminal UI's onboarding canvas); `None` when the background fell
    /// back.
    #[must_use]
    pub fn declared_background(&self) -> Option<Rgb> {
        self.declared_background
    }

    /// The export background the file sets for `surface`, if any.
    #[must_use]
    pub fn export_surface(&self, surface: ExportSurface) -> Option<Rgb> {
        self.export[surface as usize]
    }
}

/// A theme file that did not load.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadFailure {
    /// The name the file advertises, when it is a theme object.
    pub name: Option<String>,
    /// The reason, naming the file.
    pub message: String,
}

impl LoadFailure {
    fn of(path: &Path, error: ThemeError) -> LoadFailure {
        match error {
            ThemeError::Parse(reason) => LoadFailure {
                name: None,
                message: format!("Failed to parse theme {}: {reason}", path.display()),
            },
            ThemeError::Invalid { name, reason } => LoadFailure {
                name: Some(name),
                message: format!("Invalid theme {}: {reason}", path.display()),
            },
        }
    }

    /// An invalid theme object at `path`.
    pub(crate) fn invalid(path: &Path, name: &str, reason: &str) -> LoadFailure {
        LoadFailure::of(
            path,
            ThemeError::Invalid {
                name: name.to_string(),
                reason: reason.to_string(),
            },
        )
    }
}
