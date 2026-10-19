//! A theme file read, validated and completed into a [`Palette`]: every
//! token defined, every variable reference resolved once, the light or
//! dark mode decided by the background's luminance.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::LazyLock;

use serde::Deserialize;
use serde_json::Value;

use crate::color::{ansi256, Mode, Rgb};
use crate::token::{Layer, Presence, Token};

/// The theme an empty name and every failed lookup resolve to. It is also
/// the dark theme whose values fill the optional tokens of a dark file.
pub const DEFAULT_THEME_NAME: &str = "eukhe";

/// The builtin theme whose values fill the optional tokens of a light file.
pub const LIGHT_THEME_NAME: &str = "light";

/// The bundled theme names, in lookup order.
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

impl ColorValue {
    /// The color this value paints when it names one: an index paints its
    /// palette color, the terminal default names none.
    fn concrete(self) -> Option<Rgb> {
        match self {
            ColorValue::Default => None,
            ColorValue::Indexed(index) => Some(ansi256(index)),
            ColorValue::Rgb(rgb) => Some(rgb),
        }
    }
}

/// The HTML export's three backgrounds a theme may set in its `export`
/// section.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportSurface {
    Page,
    Card,
    Info,
}

impl ExportSurface {
    const ALL: [ExportSurface; 3] = [
        ExportSurface::Page,
        ExportSurface::Card,
        ExportSurface::Info,
    ];

    fn key(self) -> &'static str {
        match self {
            ExportSurface::Page => "pageBg",
            ExportSurface::Card => "cardBg",
            ExportSurface::Info => "infoBg",
        }
    }
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

impl ExportSection {
    fn get(&self, surface: ExportSurface) -> Option<&Value> {
        match surface {
            ExportSurface::Page => self.page.as_ref(),
            ExportSurface::Card => self.card.as_ref(),
            ExportSurface::Info => self.info.as_ref(),
        }
    }
}

/// Follow `value` through `vars` to its terminal value: a number, `""` or
/// a `#` string ends the chain; any other string names a variable.
fn resolve_var_refs<'a>(
    value: &'a Value,
    vars: &'a BTreeMap<String, Value>,
) -> Result<&'a Value, String> {
    let mut current = value;
    let mut visited: Vec<&str> = Vec::new();
    loop {
        let Some(name) = current.as_str() else {
            return Ok(current);
        };
        if name.is_empty() || name.starts_with('#') {
            return Ok(current);
        }
        if visited.contains(&name) {
            return Err(format!("Circular variable reference detected: {name}"));
        }
        visited.push(name);
        current = vars
            .get(name)
            .ok_or_else(|| format!("Variable reference not found: {name}"))?;
    }
}

/// A terminal value as a color: `""`, an integer 0-255 or `#rrggbb`.
fn color_value(value: &Value) -> Result<ColorValue, String> {
    match value {
        Value::String(text) if text.is_empty() => Ok(ColorValue::Default),
        Value::String(text) => Rgb::parse_hex(text)
            .map(ColorValue::Rgb)
            .ok_or_else(|| format!("Invalid hex color: {text}")),
        Value::Number(number) => number
            .as_u64()
            .and_then(|index| u8::try_from(index).ok())
            .map(ColorValue::Indexed)
            .ok_or_else(|| format!("Invalid color value: {number}")),
        Value::Null | Value::Bool(_) | Value::Array(_) | Value::Object(_) => {
            Err(format!("Invalid color value: {value}"))
        }
    }
}

/// A theme file's own values: every color it declares, resolved.
struct Declared {
    name: String,
    colors: BTreeMap<Token, ColorValue>,
    export: BTreeMap<ExportSurfaceKey, Rgb>,
}

/// [`ExportSurface`] as a map key.
type ExportSurfaceKey = usize;

impl Declared {
    fn parse(raw: &str) -> Result<Declared, ThemeError> {
        let file: ThemeFile =
            serde_json::from_str(raw).map_err(|error| ThemeError::Parse(error.to_string()))?;
        let invalid = |reason: String| ThemeError::Invalid {
            name: file.name.clone(),
            reason,
        };
        let mut colors = BTreeMap::new();
        for (key, value) in &file.colors {
            let token = Token::from_name(key)
                .ok_or_else(|| invalid(format!("unknown color token: {key}")))?;
            let color = resolve_var_refs(value, &file.vars)
                .and_then(color_value)
                .map_err(|error| invalid(format!("color \"{key}\": {error}")))?;
            colors.insert(token, color);
        }
        let missing: Vec<&str> = Token::ALL
            .into_iter()
            .filter(|token| token.presence() == Presence::Required && !colors.contains_key(token))
            .map(Token::name)
            .collect();
        if !missing.is_empty() {
            return Err(invalid(format!(
                "missing required color tokens: {}",
                missing.join(", ")
            )));
        }
        let mut export = BTreeMap::new();
        for surface in ExportSurface::ALL {
            let Some(value) = file.export.get(surface) else {
                continue;
            };
            let color = resolve_var_refs(value, &file.vars)
                .and_then(color_value)
                .map_err(|error| invalid(format!("export \"{}\": {error}", surface.key())))?;
            // An explicit `""` sets nothing, like a missing key.
            if let Some(rgb) = color.concrete() {
                export.insert(surface as ExportSurfaceKey, rgb);
            }
        }
        Ok(Declared {
            name: file.name,
            colors,
            export,
        })
    }

    fn concrete(&self, token: Token) -> Option<Rgb> {
        self.colors
            .get(&token)
            .copied()
            .and_then(ColorValue::concrete)
    }

    /// The background the file sets: its `background`, else its export
    /// page, else its user-message surface.
    fn background(&self) -> Option<Rgb> {
        self.concrete(Token::Background)
            .or_else(|| {
                self.export
                    .get(&(ExportSurface::Page as ExportSurfaceKey))
                    .copied()
            })
            .or_else(|| self.concrete(Token::UserMessageBg))
    }
}

/// The values the optional tokens of a file of one mode fall back to.
struct ModeDefaults {
    foreground: Rgb,
    refinement_header: ColorValue,
    refinement_summary: ColorValue,
}

impl ModeDefaults {
    fn of(builtin: &Declared) -> ModeDefaults {
        let value = |token: Token| {
            builtin
                .colors
                .get(&token)
                .copied()
                .unwrap_or_else(|| panic!("builtin {} sets {}", builtin.name, token.name()))
        };
        ModeDefaults {
            foreground: builtin
                .concrete(Token::Foreground)
                .unwrap_or_else(|| panic!("builtin {} sets a foreground", builtin.name)),
            refinement_header: value(Token::RefinementHeader),
            refinement_summary: value(Token::RefinementSummary),
        }
    }
}

/// The fallbacks of the optional tokens, all from the builtin files.
struct Fallbacks {
    /// The default theme's background: the background of a file that
    /// sets none of `background`, an export page or a user-message surface.
    background: Rgb,
    dark: ModeDefaults,
    light: ModeDefaults,
}

/// The fallbacks, built once from the builtin files.
static FALLBACKS: LazyLock<Fallbacks> = LazyLock::new(|| {
    let builtin = |name: &str| {
        Declared::parse(builtin_json(name).expect("a builtin name"))
            .unwrap_or_else(|error| panic!("builtin {name} is valid: {error:?}"))
    };
    let (dark, light) = (builtin(DEFAULT_THEME_NAME), builtin(LIGHT_THEME_NAME));
    Fallbacks {
        background: dark
            .background()
            .expect("the default theme sets a background"),
        dark: ModeDefaults::of(&dark),
        light: ModeDefaults::of(&light),
    }
});

impl Fallbacks {
    fn for_mode(&self, mode: Mode) -> &ModeDefaults {
        match mode {
            Mode::Dark => &self.dark,
            Mode::Light => &self.light,
        }
    }
}

/// A complete theme: a color for every token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Palette {
    name: String,
    colors: [ColorValue; Token::ALL.len()],
    /// The file's own `background`, when it is `#rrggbb`.
    declared_background: Option<Rgb>,
    export: [Option<Rgb>; ExportSurface::ALL.len()],
    mode: Mode,
}

impl Palette {
    /// Complete a file's values. A token the file leaves out falls back:
    /// `background` to the export page, else the user-message surface,
    /// else the default theme's background; `mdBody` to `text`;
    /// `foreground` and the refinement pair to the builtin theme of the
    /// file's mode (the default theme when dark, `light` when light). The
    /// mode is light when the background's luminance is above one half.
    fn complete(declared: Declared) -> Palette {
        let fallbacks = &*FALLBACKS;
        let background = declared.background().unwrap_or(fallbacks.background);
        let mode = Mode::of_background(background);
        let defaults = fallbacks.for_mode(mode);
        let declared_value = |token: Token| declared.colors.get(&token).copied();
        let colors = Token::ALL.map(|token| match token {
            Token::Background => ColorValue::Rgb(background),
            Token::Foreground => ColorValue::Rgb(
                declared
                    .concrete(Token::Foreground)
                    .unwrap_or(defaults.foreground),
            ),
            Token::MdBody => declared_value(Token::MdBody)
                .or_else(|| declared_value(Token::Text))
                .expect("text is required"),
            Token::RefinementHeader => declared_value(token).unwrap_or(defaults.refinement_header),
            Token::RefinementSummary => {
                declared_value(token).unwrap_or(defaults.refinement_summary)
            }
            _ => declared_value(token).expect("required tokens are present"),
        });
        let declared_background = match declared.colors.get(&Token::Background) {
            Some(ColorValue::Rgb(rgb)) => Some(*rgb),
            Some(ColorValue::Default | ColorValue::Indexed(_)) | None => None,
        };
        Palette {
            declared_background,
            export: ExportSurface::ALL
                .map(|surface| declared.export.get(&(surface as ExportSurfaceKey)).copied()),
            name: declared.name,
            colors,
            mode,
        }
    }

    /// Parse and complete theme file text.
    ///
    /// # Errors
    ///
    /// [`ThemeError::Parse`] when the text is not a theme object (bad
    /// JSON, a wrong shape, an unknown top-level or export key);
    /// [`ThemeError::Invalid`] when a color key is unknown, a required
    /// token is missing, a variable reference is missing or circular, or a
    /// value is not `""`, an integer 0-255 or `#rrggbb`.
    pub fn parse(raw: &str) -> Result<Palette, ThemeError> {
        Declared::parse(raw).map(Palette::complete)
    }

    /// Read, parse and complete the theme file at `path`.
    ///
    /// # Errors
    ///
    /// A [`LoadFailure`] naming the path and, when the file is a theme
    /// object, the name it advertises.
    pub fn load(path: &Path) -> Result<Palette, LoadFailure> {
        let raw = std::fs::read_to_string(path).map_err(|error| LoadFailure {
            name: None,
            message: format!("Failed to read theme {}: {error}", path.display()),
        })?;
        Palette::parse(&raw).map_err(|error| match error {
            ThemeError::Parse(reason) => LoadFailure {
                name: None,
                message: format!("Failed to parse theme {}: {reason}", path.display()),
            },
            ThemeError::Invalid { name, reason } => LoadFailure {
                name: Some(name),
                message: format!("Invalid theme {}: {reason}", path.display()),
            },
        })
    }

    /// The builtin theme `name` ([`BUILTIN_THEME_NAMES`]).
    ///
    /// # Panics
    ///
    /// Panics when a bundled file is invalid: the bundled files are
    /// build-time data, and a test loads each one.
    #[must_use]
    pub fn builtin(name: &str) -> Option<Palette> {
        let raw = builtin_json(name)?;
        Some(
            Palette::parse(raw)
                .unwrap_or_else(|error| panic!("builtin theme {name} is valid: {error:?}")),
        )
    }

    /// The default theme ([`DEFAULT_THEME_NAME`]).
    ///
    /// # Panics
    ///
    /// Never: the default theme is a builtin, and the builtins are valid.
    #[must_use]
    pub fn default_theme() -> Palette {
        Palette::builtin(DEFAULT_THEME_NAME).expect("the default theme is a builtin")
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

    /// The color the token paints where the terminal cannot be asked: the
    /// terminal default is the foreground for ink and the background for a
    /// surface; an index is its palette color.
    #[must_use]
    pub fn rgb(&self, token: Token) -> Rgb {
        match self.value(token) {
            ColorValue::Rgb(rgb) => rgb,
            ColorValue::Indexed(index) => ansi256(index),
            ColorValue::Default => match token.layer() {
                Layer::Ink => self.rgb(Token::Foreground),
                Layer::Surface => self.rgb(Token::Background),
            },
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The builtins load, set every optional token themselves except
    /// `background` (their export page is their background), and their
    /// modes follow their backgrounds.
    #[test]
    fn builtins_load_with_their_modes() {
        let modes: Vec<(String, Mode, Rgb)> = BUILTIN_THEME_NAMES
            .iter()
            .map(|name| {
                let palette = Palette::builtin(name).expect("builtin");
                (
                    palette.name().to_string(),
                    palette.mode(),
                    palette.rgb(Token::Background),
                )
            })
            .collect();
        assert_eq!(
            modes,
            [
                ("eukhe".to_string(), Mode::Dark, Rgb::new(0x05, 0x05, 0x06)),
                ("dark".to_string(), Mode::Dark, Rgb::new(0x18, 0x18, 0x1e)),
                ("light".to_string(), Mode::Light, Rgb::new(0xf8, 0xf8, 0xf8)),
            ]
        );
    }

    /// The mode follows the background, never the name: a file named
    /// `light` with a dark background is dark and takes the dark
    /// fallbacks; a light background under any name is light.
    #[test]
    fn the_mode_follows_the_background_not_the_name() {
        let file = |name: &str, background: &str| {
            let mut value: Value =
                serde_json::from_str(builtin_json("dark").expect("dark")).expect("json");
            value["name"] = Value::from(name);
            let colors = value["colors"].as_object_mut().expect("colors");
            colors.insert("background".to_string(), Value::from(background));
            for optional in ["refinementHeader", "refinementSummary"] {
                colors.remove(optional);
            }
            let palette = Palette::parse(&value.to_string()).expect("valid");
            (palette.mode(), palette.value(Token::RefinementHeader))
        };
        let dark_header = ColorValue::Rgb(Rgb::new(0x95, 0x75, 0xcd));
        let light_header = ColorValue::Rgb(Rgb::new(0x71, 0x46, 0xab));
        assert_eq!(
            [file("light", "#101010"), file("anything", "#fafafa")],
            [(Mode::Dark, dark_header), (Mode::Light, light_header)]
        );
    }
}
