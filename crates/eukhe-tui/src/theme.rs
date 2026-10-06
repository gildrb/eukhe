//! Theme engine ported from `coding-agent/src/modes/interactive/theme`.
//!
//! Ships the `eukhe`, `dark`, and `light` built-in palettes and loads theme
//! files in the same variable/color layout (name resolution lives in
//! [`crate::theme_catalog`]). Colors resolve to truecolor or 256-color ANSI
//! depending on `COLORTERM`/`TERM`.

use crate::style::{Color, Modifier, Style};
use anyhow::{anyhow, bail, Context, Result};
use serde::Deserialize;
use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ThemeColor {
    Accent,
    Border,
    BorderAccent,
    BorderMuted,
    Success,
    Error,
    Warning,
    Muted,
    Dim,
    Text,
    ThinkingText,
    UserMessageText,
    CustomMessageText,
    CustomMessageLabel,
    RefinementHeader,
    RefinementSummary,
    ToolTitle,
    ToolOutput,
    MdBody,
    MdHeading,
    MdLink,
    MdLinkUrl,
    MdCode,
    MdCodeBlock,
    MdCodeBlockBorder,
    MdQuote,
    MdQuoteBorder,
    MdHr,
    MdListBullet,
    ToolDiffAdded,
    ToolDiffRemoved,
    ToolDiffText,
    ToolDiffContext,
    SyntaxComment,
    SyntaxKeyword,
    SyntaxFunction,
    SyntaxVariable,
    SyntaxString,
    SyntaxNumber,
    SyntaxType,
    SyntaxOperator,
    SyntaxPunctuation,
    ThinkingOff,
    ThinkingMinimal,
    ThinkingLow,
    ThinkingMedium,
    ThinkingHigh,
    ThinkingXhigh,
    BashMode,
}

impl ThemeColor {
    fn name(self) -> &'static str {
        match self {
            ThemeColor::Accent => "accent",
            ThemeColor::Border => "border",
            ThemeColor::BorderAccent => "borderAccent",
            ThemeColor::BorderMuted => "borderMuted",
            ThemeColor::Success => "success",
            ThemeColor::Error => "error",
            ThemeColor::Warning => "warning",
            ThemeColor::Muted => "muted",
            ThemeColor::Dim => "dim",
            ThemeColor::Text => "text",
            ThemeColor::ThinkingText => "thinkingText",
            ThemeColor::UserMessageText => "userMessageText",
            ThemeColor::CustomMessageText => "customMessageText",
            ThemeColor::CustomMessageLabel => "customMessageLabel",
            ThemeColor::RefinementHeader => "refinementHeader",
            ThemeColor::RefinementSummary => "refinementSummary",
            ThemeColor::ToolTitle => "toolTitle",
            ThemeColor::ToolOutput => "toolOutput",
            ThemeColor::MdBody => "mdBody",
            ThemeColor::MdHeading => "mdHeading",
            ThemeColor::MdLink => "mdLink",
            ThemeColor::MdLinkUrl => "mdLinkUrl",
            ThemeColor::MdCode => "mdCode",
            ThemeColor::MdCodeBlock => "mdCodeBlock",
            ThemeColor::MdCodeBlockBorder => "mdCodeBlockBorder",
            ThemeColor::MdQuote => "mdQuote",
            ThemeColor::MdQuoteBorder => "mdQuoteBorder",
            ThemeColor::MdHr => "mdHr",
            ThemeColor::MdListBullet => "mdListBullet",
            ThemeColor::ToolDiffAdded => "toolDiffAdded",
            ThemeColor::ToolDiffRemoved => "toolDiffRemoved",
            ThemeColor::ToolDiffText => "toolDiffText",
            ThemeColor::ToolDiffContext => "toolDiffContext",
            ThemeColor::SyntaxComment => "syntaxComment",
            ThemeColor::SyntaxKeyword => "syntaxKeyword",
            ThemeColor::SyntaxFunction => "syntaxFunction",
            ThemeColor::SyntaxVariable => "syntaxVariable",
            ThemeColor::SyntaxString => "syntaxString",
            ThemeColor::SyntaxNumber => "syntaxNumber",
            ThemeColor::SyntaxType => "syntaxType",
            ThemeColor::SyntaxOperator => "syntaxOperator",
            ThemeColor::SyntaxPunctuation => "syntaxPunctuation",
            ThemeColor::ThinkingOff => "thinkingOff",
            ThemeColor::ThinkingMinimal => "thinkingMinimal",
            ThemeColor::ThinkingLow => "thinkingLow",
            ThemeColor::ThinkingMedium => "thinkingMedium",
            ThemeColor::ThinkingHigh => "thinkingHigh",
            ThemeColor::ThinkingXhigh => "thinkingXhigh",
            ThemeColor::BashMode => "bashMode",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ThemeBg {
    SelectedBg,
    UserMessageBg,
    CustomMessageBg,
    ToolPendingBg,
    ToolSuccessBg,
    ToolErrorBg,
    ToolDiffAddedBg,
    ToolDiffRemovedBg,
    ToolPanelBg,
}

impl ThemeBg {
    fn name(self) -> &'static str {
        match self {
            ThemeBg::SelectedBg => "selectedBg",
            ThemeBg::UserMessageBg => "userMessageBg",
            ThemeBg::CustomMessageBg => "customMessageBg",
            ThemeBg::ToolPendingBg => "toolPendingBg",
            ThemeBg::ToolSuccessBg => "toolSuccessBg",
            ThemeBg::ToolErrorBg => "toolErrorBg",
            ThemeBg::ToolDiffAddedBg => "toolDiffAddedBg",
            ThemeBg::ToolDiffRemovedBg => "toolDiffRemovedBg",
            ThemeBg::ToolPanelBg => "toolPanelBg",
        }
    }
}

/// A theme file (TS `ThemeJsonSchema`): `$schema` and the HTML `export`
/// section ride along unread.
#[derive(Debug, Clone, Deserialize)]
pub struct ThemeJson {
    name: String,
    #[serde(default)]
    vars: BTreeMap<String, serde_json::Value>,
    colors: BTreeMap<String, serde_json::Value>,
}

impl ThemeJson {
    /// The name the theme registers under (TS `theme.name`).
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// The color tokens a theme file must define (TS `ThemeJsonSchema`'s
/// required `colors` keys; `mdBody` and the refinement pair are optional).
const REQUIRED_COLOR_TOKENS: [&str; 55] = [
    "accent",
    "border",
    "borderAccent",
    "borderMuted",
    "success",
    "error",
    "warning",
    "muted",
    "dim",
    "text",
    "thinkingText",
    "selectedBg",
    "userMessageBg",
    "userMessageText",
    "customMessageBg",
    "customMessageText",
    "customMessageLabel",
    "toolPendingBg",
    "toolSuccessBg",
    "toolErrorBg",
    "toolDiffAddedBg",
    "toolDiffRemovedBg",
    "toolPanelBg",
    "toolTitle",
    "toolOutput",
    "mdHeading",
    "mdLink",
    "mdLinkUrl",
    "mdCode",
    "mdCodeBlock",
    "mdCodeBlockBorder",
    "mdQuote",
    "mdQuoteBorder",
    "mdHr",
    "mdListBullet",
    "toolDiffAdded",
    "toolDiffRemoved",
    "toolDiffText",
    "toolDiffContext",
    "syntaxComment",
    "syntaxKeyword",
    "syntaxFunction",
    "syntaxVariable",
    "syntaxString",
    "syntaxNumber",
    "syntaxType",
    "syntaxOperator",
    "syntaxPunctuation",
    "thinkingOff",
    "thinkingMinimal",
    "thinkingLow",
    "thinkingMedium",
    "thinkingHigh",
    "thinkingXhigh",
    "bashMode",
];

/// TS `resolveVarRefs`: numbers, `""`, and `#` values are terminal; any
/// other string names a var, followed until a terminal value.
fn resolve_var_refs<'a>(
    value: &'a serde_json::Value,
    vars: &'a BTreeMap<String, serde_json::Value>,
) -> Result<&'a serde_json::Value> {
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
            bail!("Circular variable reference detected: {name}");
        }
        visited.push(name);
        current = vars
            .get(name)
            .ok_or_else(|| anyhow!("Variable reference not found: {name}"))?;
    }
}

/// TS `fgAnsi`/`bgAnsi` on a resolved value: `""` is the terminal
/// default, an integer a 256-color index, `#rrggbb` a truecolor value.
fn parse_color(value: &serde_json::Value) -> Result<Color> {
    match value {
        serde_json::Value::String(text) if text.is_empty() => Ok(Color::Reset),
        serde_json::Value::String(text) => parse_hex6(text)
            .map(|(r, g, b)| Color::Rgb(r, g, b))
            .ok_or_else(|| anyhow!("Invalid hex color: {text}")),
        serde_json::Value::Number(number) => number
            .as_u64()
            .and_then(|index| u8::try_from(index).ok())
            .map(Color::Indexed)
            .ok_or_else(|| anyhow!("Invalid color value: {number}")),
        serde_json::Value::Null
        | serde_json::Value::Bool(_)
        | serde_json::Value::Array(_)
        | serde_json::Value::Object(_) => bail!("Invalid color value: {value}"),
    }
}

/// `#rrggbb` (TS `hexToRgb`: exactly six hex digits after the `#`).
fn parse_hex6(text: &str) -> Option<(u8, u8, u8)> {
    let hex = text.strip_prefix('#')?;
    if hex.len() != 6 || !hex.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    let channel = |range: std::ops::Range<usize>| u8::from_str_radix(&hex[range], 16).ok();
    Some((channel(0..2)?, channel(2..4)?, channel(4..6)?))
}

/// TS `parseHexColor` on the theme record's `background` (the onboarding
/// wash canvas): `^#?([0-9a-f]{6})$` case-insensitive on the trimmed value,
/// after one var lookup -- only the 6-hex shape parses; anything else
/// (empty, 3-hex shorthand, an ANSI index, a var miss) stays `None` so
/// callers fall back to their hardcoded canvases.
fn parse_theme_background(
    value: &serde_json::Value,
    vars: &BTreeMap<String, serde_json::Value>,
) -> Option<(u8, u8, u8)> {
    let raw = value.as_str()?;
    let resolved = vars
        .get(raw)
        .map_or(Some(raw), serde_json::Value::as_str)?
        .trim();
    parse_hex6(&format!(
        "#{}",
        resolved.strip_prefix('#').unwrap_or(resolved)
    ))
}

/// Quantize RGB to the xterm 256-color palette (TS `rgbTo256`): nearest cube
/// level per channel, gray chosen by luma, gray wins only for near-neutral
/// colors where it is the closer weighted distance.
#[must_use]
pub fn rgb_to_256(rgb: (u8, u8, u8)) -> u8 {
    const CUBE_VALUES: [u8; 6] = [0, 95, 135, 175, 215, 255];
    const GRAY_VALUES: [u8; 24] = {
        let mut values = [0u8; 24];
        let mut index = 0;
        while index < 24 {
            values[index] = (8 + index * 10) as u8;
            index += 1;
        }
        values
    };
    let (r, g, b) = (f64::from(rgb.0), f64::from(rgb.1), f64::from(rgb.2));
    let find_closest = |value: f64, values: &[u8]| -> usize {
        values
            .iter()
            .enumerate()
            .min_by(|(_, candidate), (index, _)| {
                (value - f64::from(**candidate))
                    .abs()
                    .partial_cmp(&(value - f64::from(values[*index])).abs())
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .map_or(0, |(index, _)| index)
    };
    let distance = |other: (u8, u8, u8)| -> f64 {
        let (dr, dg, db) = (
            r - f64::from(other.0),
            g - f64::from(other.1),
            b - f64::from(other.2),
        );
        dr * dr * 0.299 + dg * dg * 0.587 + db * db * 0.114
    };
    let (r_index, g_index, b_index) = (
        find_closest(r, &CUBE_VALUES),
        find_closest(g, &CUBE_VALUES),
        find_closest(b, &CUBE_VALUES),
    );
    let cube_rgb = (
        CUBE_VALUES[r_index],
        CUBE_VALUES[g_index],
        CUBE_VALUES[b_index],
    );
    let cube_index = 16 + 36 * r_index + 6 * g_index + b_index;
    let cube_dist = distance(cube_rgb);
    let gray = 0.299 * r + 0.587 * g + 0.114 * b;
    let gray_slot = find_closest(gray, &GRAY_VALUES);
    let gray_value = GRAY_VALUES[gray_slot];
    let gray_index = 232 + gray_slot;
    let gray_dist = distance((gray_value, gray_value, gray_value));
    let max_channel = r.max(g).max(b);
    let min_channel = r.min(g).min(b);
    if max_channel - min_channel < 10.0 && gray_dist < cube_dist {
        u8::try_from(gray_index).unwrap_or(16)
    } else {
        u8::try_from(cube_index).unwrap_or(16)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ColorMode {
    TrueColor,
    Color256,
}

/// TS `detectColorMode`: truecolor unless the terminal is truly limited.
/// tmux reports `screen*` but forwards 24-bit color, so it stays truecolor;
/// only genuine GNU screen (no `$TMUX`) falls back to the 256-color cube.
#[must_use]
pub fn detect_color_mode() -> ColorMode {
    let colorterm = std::env::var("COLORTERM").unwrap_or_default();
    if colorterm == "truecolor" || colorterm == "24bit" {
        return ColorMode::TrueColor;
    }
    if std::env::var_os("WT_SESSION").is_some() {
        return ColorMode::TrueColor;
    }
    let term = std::env::var("TERM").unwrap_or_default();
    if term == "dumb" || term.is_empty() || term == "linux" {
        return ColorMode::Color256;
    }
    if std::env::var("TERM_PROGRAM").as_deref() == Ok("Apple_Terminal") {
        return ColorMode::Color256;
    }
    let in_tmux = std::env::var_os("TMUX").is_some() || term.starts_with("tmux");
    let genuine_screen =
        term == "screen" || term.starts_with("screen-") || term.starts_with("screen.");
    if !in_tmux && genuine_screen {
        return ColorMode::Color256;
    }
    ColorMode::TrueColor
}

fn to_terminal_color(color: Color, mode: ColorMode) -> Color {
    match (color, mode) {
        (Color::Rgb(r, g, b), ColorMode::Color256) => Color::Indexed(rgb_to_256((r, g, b))),
        (c, _) => c,
    }
}

/// How far a selection wash must stand off the surface it renders on:
/// TS `SELECTION_MIN_LUMINANCE_DELTA` -- "Selection rows must stand out
/// clearly, much more than passive surfaces" (TS theme.ts). The operator's
/// 2026-09-26 directive makes the bar binding for the panel redesign's
/// selection: a wash within a few luminance points of the surface reads as
/// no selection at all.
pub(crate) const SELECTION_MIN_LUMINANCE_DELTA: f64 = 28.0;

/// The contrast lift's blend cap (TS `SELECTION_MAX_BLEND_ALPHA`): the
/// wash never lifts further than halfway toward the endpoint.
const SELECTION_MAX_BLEND_ALPHA: f32 = 0.5;

/// The contrast lift's step (TS `SELECTION_BLEND_STEP`).
const SELECTION_BLEND_STEP: f32 = 0.05;

/// The perceived-lightness blend TS weighs every color decision with
/// (TS `luminance`).
fn luminance(rgb: (u16, u16, u16)) -> f64 {
    0.299 * f64::from(rgb.0) + 0.587 * f64::from(rgb.1) + 0.114 * f64::from(rgb.2)
}

/// The xterm-256 palette slot's RGB (TS `ansi256ToRgb`): the 6x6x6 cube
/// and the gray ramp. The base ANSI slots (0-15) are terminal-defined, so
/// their rendered color is unknown.
fn indexed_to_rgb(index: u8) -> Option<(u16, u16, u16)> {
    const CUBE_VALUES: [u16; 6] = [0, 95, 135, 175, 215, 255];
    match index {
        16..=231 => {
            let slot = u16::from(index) - 16;
            let (red, rest) = (slot / 36, slot % 36);
            let (green, blue) = (rest / 6, rest % 6);
            Some((
                CUBE_VALUES[red as usize],
                CUBE_VALUES[green as usize],
                CUBE_VALUES[blue as usize],
            ))
        }
        232..=255 => {
            let gray = u16::from(index) * 10 - 2312;
            Some((gray, gray, gray))
        }
        _ => None,
    }
}

/// The luminance of what actually renders: a 256-color terminal paints the
/// palette slot, not the configured RGB (the quantized candidate evaluates
/// through this; base ANSI slots stay unknown).
pub(crate) fn quantized_luminance(color: Color) -> Option<f64> {
    match color {
        Color::Rgb(r, g, b) => Some(luminance((u16::from(r), u16::from(g), u16::from(b)))),
        Color::Indexed(index) => indexed_to_rgb(index).map(luminance),
        Color::Reset => None,
    }
}

/// The active theme: resolved styles per color slot.
#[derive(Debug, Clone, PartialEq)]
pub struct Theme {
    pub name: String,
    fg: BTreeMap<&'static str, Style>,
    bg: BTreeMap<&'static str, Style>,
    bg_colors: BTreeMap<&'static str, Color>,
    /// The theme record's parseable `background` key, raw RGB: blends that
    /// use it (TS `onboardingHighlightBackground`) mix against the true
    /// colour and quantize their result per [`Theme::mode`], not this.
    background: Option<(u8, u8, u8)>,
    pub mode: ColorMode,
}

impl Theme {
    /// TS `createTheme`: the refinement pair defaults by theme name,
    /// `mdBody` falls back to `text`, and every slot resolves through the
    /// vars to a terminal color.
    ///
    /// # Errors
    ///
    /// Returns `Err` naming the slot when its value references a missing
    /// or circular var, or is not `""`, a 0-255 index, or `#rrggbb`.
    pub(crate) fn from_json(json: &ThemeJson, mode: ColorMode) -> Result<Theme> {
        let refinement: Vec<(&str, serde_json::Value)> =
            eukhe_types::themes::refinement_colors(&json.name)
                .into_iter()
                .map(|(slot, value)| (slot, serde_json::Value::from(value)))
                .collect();
        let mut slots: BTreeMap<&str, &serde_json::Value> = refinement
            .iter()
            .map(|(slot, value)| (*slot, value))
            .collect();
        slots.extend(
            json.colors
                .iter()
                .map(|(slot, value)| (slot.as_str(), value)),
        );
        if let (None, Some(text)) = (json.colors.get("mdBody"), json.colors.get("text")) {
            slots.insert("mdBody", text);
        }
        let mut fg = BTreeMap::new();
        let mut bg = BTreeMap::new();
        let mut bg_colors = BTreeMap::new();
        for (slot, value) in slots {
            // Background slots end with "Bg" (camel case); the rest are
            // foreground. Keys naming no slot (`background`) render nothing.
            let (fg_key, bg_key) = if slot.ends_with("Bg") {
                (None, bg_name_lookup(slot))
            } else {
                (fg_name_lookup(slot), None)
            };
            if fg_key.is_none() && bg_key.is_none() {
                continue;
            }
            let color = resolve_var_refs(value, &json.vars)
                .and_then(parse_color)
                .with_context(|| format!("color \"{slot}\""))?;
            let color = to_terminal_color(color, mode);
            if let Some(key) = bg_key {
                bg_colors.insert(key, color);
                bg.insert(key, Style::default().bg(color));
            }
            if let Some(key) = fg_key {
                fg.insert(key, Style::default().fg(color));
            }
        }
        Ok(Theme {
            name: json.name.clone(),
            fg,
            bg,
            bg_colors,
            // `background` is not a fg/bg slot, so the loop above skips it;
            // the wash reads it as its canvas (TS `parseHexColor`).
            background: json
                .colors
                .get("background")
                .and_then(|value| parse_theme_background(value, &json.vars)),
            mode,
        })
    }

    /// A bundled theme ([`eukhe_types::themes::BUILTIN_THEME_NAMES`]).
    /// User-facing names resolve through
    /// [`crate::theme_catalog::ThemeSources::resolve`], which reports
    /// unknown names.
    ///
    /// # Panics
    ///
    /// Panics when `name` is not a builtin or a bundled file is invalid:
    /// callers name builtins statically, and the bundled files are
    /// build-time data.
    #[must_use]
    pub fn builtin(name: &str, mode: ColorMode) -> Theme {
        let raw = eukhe_types::themes::builtin_theme_json(name)
            .unwrap_or_else(|| panic!("{name} is not a builtin theme"));
        let json: ThemeJson = serde_json::from_str(raw).expect("bundled theme JSON parses");
        Theme::from_json(&json, mode).expect("bundled theme colors resolve")
    }

    #[must_use]
    pub fn fg_style(&self, color: ThemeColor) -> Style {
        self.fg.get(color.name()).copied().unwrap_or_default()
    }

    #[must_use]
    pub fn bg_style(&self, color: ThemeBg) -> Style {
        self.bg.get(color.name()).copied().unwrap_or_default()
    }

    #[must_use]
    pub fn bg_color(&self, color: ThemeBg) -> Option<Color> {
        self.bg_colors.get(color.name()).copied()
    }

    /// The theme record's parseable `background` (strict 6-hex shape after
    /// var resolution, TS `parseHexColor`), raw RGB; `None` when the theme
    /// carries no such value, so callers fall back to their own canvases.
    pub(crate) fn background_rgb(&self) -> Option<(u8, u8, u8)> {
        self.background
    }

    /// `theme.fg("muted", text)` equivalent.
    pub fn fg(&self, color: ThemeColor, text: impl Into<String>) -> crate::Span {
        crate::Span::styled(text.into(), self.fg_style(color))
    }

    pub fn fg_span(&self, color: ThemeColor, text: impl Into<String>) -> crate::Span {
        self.fg(color, text)
    }

    /// Bold helper (chalk.bold equivalent).
    #[must_use]
    pub fn bold(&self, span: crate::Span) -> crate::Span {
        span_with(span, Modifier::BOLD)
    }

    #[must_use]
    pub fn italic(&self, span: crate::Span) -> crate::Span {
        span_with(span, Modifier::ITALIC)
    }

    #[must_use]
    pub fn underline(&self, span: crate::Span) -> crate::Span {
        span_with(span, Modifier::UNDERLINED)
    }

    #[must_use]
    pub fn strikethrough(&self, span: crate::Span) -> crate::Span {
        span_with(span, Modifier::CROSSED_OUT)
    }

    /// Background-paint helper: apply a bg style to whole line content.
    #[must_use]
    pub fn bg_paint(&self, color: ThemeBg, line: crate::Line) -> crate::Line {
        let style = self.bg_style(color);
        line.into_iter()
            .map(|mut span| {
                span.style = span.style.patch(style);
                span
            })
            .collect()
    }

    /// Filled effort squares: a pastel purple that reads softer than the
    /// theme accent (TS `getEffortSquareColor`). The TS theme picks a light
    /// pastel on light terminal backgrounds; the Rust theme does not yet
    /// detect the terminal background kind, so the dark pastel is the
    /// default-terminal match.
    #[must_use]
    pub fn effort_square_style(&self) -> Style {
        const EFFORT_SQUARE_DARK_COLOR: Color = Color::Rgb(0xa7, 0x8b, 0xfa);
        Style::default().fg(to_terminal_color(EFFORT_SQUARE_DARK_COLOR, self.mode))
    }

    /// Row-selection highlight for menu rows (TS
    /// `getSoftSelectionBackgroundColor`): the selection color blended
    /// halfway toward the editor surface -- a softer band than the full
    /// selection block. Non-RGB palettes have no reliable blend base, so
    /// they keep the plain selection background.
    ///
    /// The halfway blend is kept only when it still READS against the
    /// surface: every built-in theme's selection sits a few luminance
    /// points off the editor surface, so the blend used to paint as a
    /// near-invisible wash -- the operator could not tell which row was
    /// selected (the operator's 2026-09-26 directive: the panel redesign's
    /// selection must be unmistakable). When the blend cannot clear
    /// [`SELECTION_MIN_LUMINANCE_DELTA`] over the surface, the wash steps
    /// toward the contrast endpoint -- white when the selection reads
    /// lighter than the surface, black when it reads darker -- until it
    /// clears the bar (TS `getSelectionBackgroundColor`'s endpoint ladder,
    /// anchored to the editor surface because the TUI cannot query the
    /// terminal's own background the way TS's `getDefaultTerminalColors`
    /// does; the endpoint machinery is TS's own, TS `theme.ts`:207-209
    /// "Selection rows must stand out clearly, much more than passive
    /// surfaces"). Candidates evaluate after [`Theme::mode`]
    /// quantization, so a 256-color terminal keeps a wash the palette
    /// actually separates from the surface.
    #[must_use]
    pub fn soft_selection_style(&self) -> Style {
        let blend = |top: (u16, u16, u16), bottom: (u16, u16, u16), alpha: f32| {
            Color::Rgb(
                (f32::from(top.0) * alpha + f32::from(bottom.0) * (1.0 - alpha)).round() as u8,
                (f32::from(top.1) * alpha + f32::from(bottom.1) * (1.0 - alpha)).round() as u8,
                (f32::from(top.2) * alpha + f32::from(bottom.2) * (1.0 - alpha)).round() as u8,
            )
        };
        // The blend needs real RGB. A truecolor theme carries its
        // configured RGB directly; a 256-color theme stores the
        // quantized slot, whose palette RGB is what the terminal
        // actually renders there. The base ANSI slots (0-15) are
        // terminal-defined, so those keep the plain selection (TS's
        // ANSI guard: no reliable blend base exists).
        let slot_rgb = |color: Option<Color>| -> Option<(u16, u16, u16)> {
            match color? {
                Color::Rgb(r, g, b) => Some((u16::from(r), u16::from(g), u16::from(b))),
                Color::Indexed(index) => indexed_to_rgb(index),
                Color::Reset => None,
            }
        };
        let (Some(selection), Some(editor_surface)) = (
            slot_rgb(self.bg_color(ThemeBg::SelectedBg)),
            slot_rgb(self.bg_color(ThemeBg::UserMessageBg)),
        ) else {
            return self.bg_style(ThemeBg::SelectedBg);
        };
        let surface_color = Color::Rgb(
            editor_surface.0 as u8,
            editor_surface.1 as u8,
            editor_surface.2 as u8,
        );
        let surface_ansi = to_terminal_color(surface_color, self.mode);
        // The selection also evaluates through the palette: a 256-color
        // terminal paints the quantized slot, so the ladder aims from
        // what actually renders (TS's `renderedSelection`).
        let selection_render_luminance = quantized_luminance(to_terminal_color(
            Color::Rgb(selection.0 as u8, selection.1 as u8, selection.2 as u8),
            self.mode,
        ))
        .unwrap_or(luminance(selection));
        let surface_render_luminance =
            quantized_luminance(surface_ansi).unwrap_or(luminance(editor_surface));
        // The wash reads when its rendered color clears the visibility bar
        // over the surface (both after mode quantization -- a 256-color
        // terminal paints the palette slot, not the blend). A candidate the
        // palette maps to an unknown slot never blocks: showing the wash
        // beats refusing to compute.
        let reads = |candidate: Color| {
            quantized_luminance(candidate).is_none_or(|candidate_luminance| {
                (candidate_luminance - surface_render_luminance).abs()
                    >= SELECTION_MIN_LUMINANCE_DELTA
            })
        };
        // Half contrast by default; strengthen the blend only when the
        // quantized wash still separates from the editor surface AND reads.
        for alpha in [0.5, 0.75, 1.0] {
            let adjusted = to_terminal_color(blend(selection, editor_surface, alpha), self.mode);
            if adjusted != surface_ansi && reads(adjusted) {
                return Style::default().bg(adjusted);
            }
        }
        // The blend reads too close to the surface (every built-in
        // theme): step the wash toward the contrast endpoint -- the one on
        // the selection's side of the surface first, the opposite one
        // (crossing the surface) second -- until the quantized candidate
        // clears the bar. The strongest step is tracked across BOTH
        // endpoints like TS: the first candidate to clear the bar wins,
        // and when nothing clears it a step replaces the selection only
        // if it improved on the selection's own delta.
        let delta = (selection_render_luminance - surface_render_luminance).abs();
        let endpoints = if selection_render_luminance >= surface_render_luminance {
            [(255u16, 255, 255), (0, 0, 0)]
        } else {
            [(0u16, 0, 0), (255, 255, 255)]
        };
        let mut best: Option<Color> = None;
        let mut best_delta = delta;
        for endpoint in endpoints {
            let spread = luminance(endpoint) - selection_render_luminance;
            if spread == 0.0 {
                continue;
            }
            let target = surface_render_luminance + spread.signum() * SELECTION_MIN_LUMINANCE_DELTA;
            let base_alpha = ((target - selection_render_luminance) / spread)
                .clamp(0.0, f64::from(SELECTION_MAX_BLEND_ALPHA));
            // If the direct hit undershoots the bar, keep stepping toward
            // the cap -- a stronger blend may quantize to a palette slot
            // that passes.
            let mut alphas = Vec::new();
            let mut alpha = base_alpha as f32;
            while alpha < SELECTION_MAX_BLEND_ALPHA {
                alphas.push(alpha);
                alpha += SELECTION_BLEND_STEP;
            }
            alphas.push(SELECTION_MAX_BLEND_ALPHA);
            for alpha in alphas {
                let candidate = to_terminal_color(blend(endpoint, selection, alpha), self.mode);
                let Some(candidate_luminance) = quantized_luminance(candidate) else {
                    continue;
                };
                let result_delta = (candidate_luminance - surface_render_luminance).abs();
                if result_delta >= SELECTION_MIN_LUMINANCE_DELTA - 1.0 {
                    best = Some(candidate);
                    best_delta = result_delta;
                    break;
                }
                if result_delta > best_delta {
                    best = Some(candidate);
                    best_delta = result_delta;
                }
            }
            if best.is_some() && best_delta >= SELECTION_MIN_LUMINANCE_DELTA - 1.0 {
                break;
            }
        }
        match best {
            Some(candidate) => Style::default().bg(candidate),
            // A selection pinned at its own endpoint with a palette too
            // coarse to reach the bar: the plain selection is the least
            // surprising fallback (TS keeps the configured value too).
            None => self.bg_style(ThemeBg::SelectedBg),
        }
    }

    /// The ONE selected-row style every activity surface paints (the
    /// operator's consistency rule: the selected row's background is
    /// IDENTICAL across the dock's groups, the agents view's rows, the
    /// heartbeats picker, and the bash view -- one style, not
    /// per-surface copies): the soft wash the menu panels' selected rows
    /// carry ([`Theme::soft_selection_style`]). Each surface keeps its
    /// own foreground colors; the style patches only the background,
    /// with no extra modifiers. A theme whose slots resolve to no band
    /// (a `selectedBg` that is missing or explicitly empty resolves to
    /// `Color::Reset`, which paints nothing) falls through to the
    /// onboarding wash, so a selected row always reads as selected
    /// (Macroscope PR #2908's contract).
    #[must_use]
    pub fn selection_row_style(&self) -> Style {
        let band = self
            .soft_selection_style()
            .bg
            .filter(|color| *color != Color::Reset)
            .unwrap_or_else(|| crate::onboarding::highlight_wash(self));
        Style::default().bg(band)
    }

    /// Paint one line's spans with [`Theme::selection_row_style`] --
    /// the `bg_paint` counterpart for the one selection style: each
    /// span keeps its own foreground, gains the one band.
    #[must_use]
    pub fn selection_paint(&self, line: crate::Line) -> crate::Line {
        let style = self.selection_row_style();
        line.into_iter()
            .map(|mut span| {
                span.style = span.style.patch(style);
                span
            })
            .collect()
    }
}

fn span_with(span: crate::Span, modifier: Modifier) -> crate::Span {
    let mut s = span;
    s.style = s.style.add_modifier(modifier);
    s
}

fn fg_name_lookup(name: &str) -> Option<&'static str> {
    Some(match name {
        "accent" => "accent",
        "border" => "border",
        "borderAccent" => "borderAccent",
        "borderMuted" => "borderMuted",
        "success" => "success",
        "error" => "error",
        "warning" => "warning",
        "muted" => "muted",
        "dim" => "dim",
        "text" => "text",
        "thinkingText" => "thinkingText",
        "userMessageText" => "userMessageText",
        "customMessageText" => "customMessageText",
        "customMessageLabel" => "customMessageLabel",
        "refinementHeader" => "refinementHeader",
        "refinementSummary" => "refinementSummary",
        "toolTitle" => "toolTitle",
        "toolOutput" => "toolOutput",
        "mdBody" => "mdBody",
        "mdHeading" => "mdHeading",
        "mdLink" => "mdLink",
        "mdLinkUrl" => "mdLinkUrl",
        "mdCode" => "mdCode",
        "mdCodeBlock" => "mdCodeBlock",
        "mdCodeBlockBorder" => "mdCodeBlockBorder",
        "mdQuote" => "mdQuote",
        "mdQuoteBorder" => "mdQuoteBorder",
        "mdHr" => "mdHr",
        "mdListBullet" => "mdListBullet",
        "toolDiffAdded" => "toolDiffAdded",
        "toolDiffRemoved" => "toolDiffRemoved",
        "toolDiffText" => "toolDiffText",
        "toolDiffContext" => "toolDiffContext",
        "syntaxComment" => "syntaxComment",
        "syntaxKeyword" => "syntaxKeyword",
        "syntaxFunction" => "syntaxFunction",
        "syntaxVariable" => "syntaxVariable",
        "syntaxString" => "syntaxString",
        "syntaxNumber" => "syntaxNumber",
        "syntaxType" => "syntaxType",
        "syntaxOperator" => "syntaxOperator",
        "syntaxPunctuation" => "syntaxPunctuation",
        "thinkingOff" => "thinkingOff",
        "thinkingMinimal" => "thinkingMinimal",
        "thinkingLow" => "thinkingLow",
        "thinkingMedium" => "thinkingMedium",
        "thinkingHigh" => "thinkingHigh",
        "thinkingXhigh" => "thinkingXhigh",
        "bashMode" => "bashMode",
        _ => return None,
    })
}

fn bg_name_lookup(name: &str) -> Option<&'static str> {
    Some(match name {
        "selectedBg" => "selectedBg",
        "userMessageBg" => "userMessageBg",
        "customMessageBg" => "customMessageBg",
        "toolPendingBg" => "toolPendingBg",
        "toolSuccessBg" => "toolSuccessBg",
        "toolErrorBg" => "toolErrorBg",
        "toolDiffAddedBg" => "toolDiffAddedBg",
        "toolDiffRemovedBg" => "toolDiffRemovedBg",
        "toolPanelBg" => "toolPanelBg",
        _ => return None,
    })
}

/// Read and validate a theme file (TS `parseThemeJsonContent`): JSON with
/// a string `name`, optional `vars`, and every required color token.
///
/// # Errors
///
/// Returns `Err` carrying the path when the file cannot be read, is not
/// a theme object, or misses required color tokens.
pub fn read_theme_json(path: &std::path::Path) -> Result<ThemeJson> {
    let raw = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read theme {}", path.display()))?;
    let json: ThemeJson = serde_json::from_str(&raw)
        .with_context(|| format!("Failed to parse theme {}", path.display()))?;
    let missing: Vec<&str> = REQUIRED_COLOR_TOKENS
        .into_iter()
        .filter(|token| !json.colors.contains_key(*token))
        .collect();
    if !missing.is_empty() {
        bail!(
            "Invalid theme {}: missing required color tokens: {}",
            path.display(),
            missing.join(", ")
        );
    }
    Ok(json)
}

/// Load a theme file (TS `loadThemeFromPath`).
///
/// # Errors
///
/// Returns `Err` carrying the path when [`read_theme_json`] fails or a
/// color does not resolve.
pub fn load_theme_from_path(path: &std::path::Path, mode: ColorMode) -> Result<Theme> {
    let json = read_theme_json(path)?;
    Theme::from_json(&json, mode).with_context(|| format!("Invalid theme {}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prime_theme_resolves() {
        let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
        let accent = theme.fg_style(ThemeColor::Accent);
        match accent.fg {
            Some(Color::Rgb(0x7c, 0x6f, 0xaf)) => {}
            other => panic!("unexpected accent {other:?}"),
        }
        let panel = theme.bg_style(ThemeBg::ToolPanelBg);
        assert!(matches!(panel.bg, Some(Color::Rgb(0x0d, 0x0d, 0x10))));
    }

    #[test]
    fn rgb_to_256_gray() {
        assert_eq!(rgb_to_256((0, 0, 0)), 16);
        assert_eq!(rgb_to_256((255, 255, 255)), 231);
    }

    #[test]
    fn var_reference_resolves() {
        let theme = Theme::builtin("eukhe", ColorMode::Color256);
        let accent = theme.fg_style(ThemeColor::Accent);
        assert!(matches!(accent.fg, Some(Color::Indexed(_))));
    }

    /// A theme file must carry every required token (TS schema check).
    #[test]
    fn a_theme_file_missing_required_tokens_is_invalid() {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("partial.json");
        let mut partial: serde_json::Value =
            serde_json::from_str(include_str!("../tests/fixtures/dusk-apple-theme.json"))
                .expect("fixture parses");
        let colors = partial["colors"].as_object_mut().expect("colors");
        colors.remove("bashMode");
        colors.remove("thinkingXhigh");
        std::fs::write(&path, partial.to_string()).expect("write theme");
        let error = read_theme_json(&path).expect_err("partial theme");
        assert_eq!(
            format!("{error:#}"),
            format!(
                "Invalid theme {}: missing required color tokens: thinkingXhigh, bashMode",
                path.display()
            )
        );
    }

    /// Var references chain (TS `resolveVarRefs` recursion) and integer
    /// values are 256-color indices; a cycle is an error.
    #[test]
    fn var_references_chain_and_cycles_fail() {
        let theme = |raw: &str| {
            let json: ThemeJson = serde_json::from_str(raw).expect("valid theme json");
            Theme::from_json(&json, ColorMode::TrueColor).map_err(|error| format!("{error:#}"))
        };
        let chained = theme(
            r##"{ "name": "c", "vars": { "a": "b", "b": "#102030", "i": 42 },
                  "colors": { "accent": "a", "dim": "i" } }"##,
        )
        .expect("chained vars resolve");
        assert_eq!(
            (
                chained.fg_style(ThemeColor::Accent).fg,
                chained.fg_style(ThemeColor::Dim).fg
            ),
            (Some(Color::Rgb(0x10, 0x20, 0x30)), Some(Color::Indexed(42)))
        );
        assert_eq!(
            theme(
                r#"{ "name": "c", "vars": { "a": "b", "b": "a" }, "colors": { "accent": "a" } }"#
            ),
            Err("color \"accent\": Circular variable reference detected: a".to_string())
        );
    }

    #[test]
    fn background_parses_strict_six_hex_after_var_resolution() {
        let json = serde_json::from_str::<ThemeJson>(
            r##"{
                "name": "custom",
                "vars": { "canvas": "#0A0B0C" },
                "colors": { "background": "canvas", "text": "#f4f4f5" }
            }"##,
        )
        .expect("valid theme json");
        let theme = Theme::from_json(&json, ColorMode::TrueColor).expect("theme resolves");
        // Case-insensitive 6-hex, reached through a var reference.
        assert_eq!(theme.background_rgb(), Some((0x0a, 0x0b, 0x0c)));
    }

    /// The ONE selection style paints the soft wash in every theme,
    /// never the accent, never a bold modifier. A theme whose slots
    /// resolve to no band (a `selectedBg` that is missing or
    /// explicitly empty resolves to `Color::Reset`, which paints
    /// nothing) falls through to the onboarding wash (Macroscope
    /// 2026-09-28: an unresolvable slot must fall through, not strand
    /// the selection without a band).
    #[test]
    fn the_selection_style_is_the_soft_wash_never_the_accent() {
        let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
        assert_eq!(
            theme.selection_row_style(),
            theme.soft_selection_style(),
            "prime: the selection paints the soft wash"
        );
        assert_ne!(
            theme.selection_row_style().bg,
            theme.fg_style(ThemeColor::Accent).fg,
            "the accent never rides the selection band"
        );
        let json = serde_json::from_str::<ThemeJson>(
            r##"{
                "name": "loud-accent",
                "colors": { "text": "#f4f4f5", "accent": "#ff00ff", "selectedBg": "#222226" }
            }"##,
        )
        .expect("valid theme json");
        let loud = Theme::from_json(&json, ColorMode::TrueColor).expect("theme resolves");
        assert_eq!(
            loud.selection_row_style().bg,
            loud.soft_selection_style().bg,
            "the accent stays out of the band even when it is loud"
        );
        let bare = serde_json::from_str::<ThemeJson>(
            r##"{ "name": "bare", "colors": { "text": "#f4f4f5" } }"##,
        )
        .expect("valid theme json");
        let bare = Theme::from_json(&bare, ColorMode::TrueColor).expect("theme resolves");
        assert_eq!(
            bare.selection_row_style().bg,
            Some(crate::onboarding::highlight_wash(&bare)),
            "with no resolvable band, the wash keeps the selected row readable"
        );
        // An empty `selectedBg` resolves the same way: the slot's
        // Reset is filtered too, so the wash takes the band.
        let empty_slot = serde_json::from_str::<ThemeJson>(
            r##"{
                "name": "empty-slot",
                "colors": { "text": "#f4f4f5", "selectedBg": "" }
            }"##,
        )
        .expect("valid theme json");
        let empty_slot =
            Theme::from_json(&empty_slot, ColorMode::TrueColor).expect("theme resolves");
        assert_eq!(empty_slot.bg_color(ThemeBg::SelectedBg), Some(Color::Reset));
        assert_eq!(
            empty_slot.selection_row_style().bg,
            Some(crate::onboarding::highlight_wash(&empty_slot)),
            "an empty selectedBg never paints Reset"
        );
    }

    /// The selection wash must READ (the operator's 2026-09-26 directive:
    /// the panel redesign's selection was barely visible): every built-in
    /// theme's wash clears [`SELECTION_MIN_LUMINANCE_DELTA`] over the
    /// editor surface, in both color modes -- a 256-color terminal
    /// evaluates the palette slots it actually paints.
    #[test]
    fn soft_selection_reads_off_the_editor_surface() {
        for name in ["eukhe", "dark", "light"] {
            for mode in [ColorMode::TrueColor, ColorMode::Color256] {
                let theme = Theme::builtin(name, mode);
                let wash = theme
                    .soft_selection_style()
                    .bg
                    .expect("the selection wash paints a background");
                let surface = theme
                    .bg_color(ThemeBg::UserMessageBg)
                    .expect("the editor surface resolves");
                let (Some(wash_lum), Some(surface_lum)) =
                    (quantized_luminance(wash), quantized_luminance(surface))
                else {
                    panic!("{name}/{mode:?}: wash and surface must both evaluate");
                };
                assert!(
                    (wash_lum - surface_lum).abs() >= SELECTION_MIN_LUMINANCE_DELTA - 1.0,
                    "{name}/{mode:?}: wash {wash:?} lum {wash_lum:.2} vs surface {surface:?} lum {surface_lum:.2}"
                );
            }
        }
    }

    /// The ladder's pinned values: the wash clears the bar by stepping
    /// from the selection toward the endpoint on its side of the surface
    /// (white for the dark themes, black for the light one), and the
    /// 256-color palette keeps a slot the surface's slot separates from.
    #[test]
    fn soft_selection_pins_the_contrast_ladder_values() {
        let prime = Theme::builtin("eukhe", ColorMode::TrueColor);
        assert_eq!(
            prime.soft_selection_style().bg,
            Some(Color::Rgb(54, 54, 58))
        );
        let prime256 = Theme::builtin("eukhe", ColorMode::Color256);
        assert_eq!(
            prime256.soft_selection_style().bg,
            Some(Color::Indexed(237))
        );
        let dark = Theme::builtin("dark", ColorMode::TrueColor);
        assert_eq!(dark.soft_selection_style().bg, Some(Color::Rgb(80, 80, 95)));
        let dark256 = Theme::builtin("dark", ColorMode::Color256);
        assert_eq!(dark256.soft_selection_style().bg, Some(Color::Indexed(244)));
        let light = Theme::builtin("light", ColorMode::TrueColor);
        assert_eq!(
            light.soft_selection_style().bg,
            Some(Color::Rgb(202, 202, 218))
        );
        let light256 = Theme::builtin("light", ColorMode::Color256);
        assert_eq!(
            light256.soft_selection_style().bg,
            Some(Color::Indexed(251))
        );
    }

    /// No reliable blend base, no ladder: a base-ANSI selection (the
    /// terminal defines its rendered color) keeps the plain selection --
    /// TS's ANSI guard.
    #[test]
    fn soft_selection_keeps_the_plain_selection_without_a_blend_base() {
        let json = serde_json::from_str::<ThemeJson>(
            r##"{
                "name": "ansi",
                "colors": {
                    "selectedBg": 4,
                    "userMessageBg": "#1a1a1f"
                }
            }"##,
        )
        .expect("valid theme json");
        let theme = Theme::from_json(&json, ColorMode::TrueColor).expect("theme resolves");
        assert_eq!(
            theme.soft_selection_style().bg,
            theme.bg_style(ThemeBg::SelectedBg).bg
        );
    }

    #[test]
    fn background_stays_none_for_non_six_hex_shapes() {
        // Empty, 3-hex shorthand, an unknown var, an ANSI index, and a
        // missing value are all unparseable: the wash falls back to its
        // hardcoded canvas (the built-in themes carry no background at all).
        for raw in ["\"\"", "\"#abc\"", "\"5\"", "17", "null"] {
            let json: ThemeJson = serde_json::from_str(&format!(
                r#"{{ "name": "custom", "colors": {{ "background": {raw} }} }}"#
            ))
            .expect("valid theme json");
            let theme = Theme::from_json(&json, ColorMode::TrueColor).expect("theme resolves");
            assert_eq!(theme.background_rgb(), None, "background {raw}");
        }
    }

    /// The selection band in every theme and color mode is the soft
    /// wash, carries NO modifiers (a selected row's own styles stay its
    /// own), and reads off its surface.
    #[test]
    fn the_selection_band_is_the_wash_and_reads_off_its_surface() {
        for name in ["eukhe", "dark", "light"] {
            for mode in [ColorMode::TrueColor, ColorMode::Color256] {
                let theme = Theme::builtin(name, mode);
                let selection = theme.selection_row_style();
                assert_eq!(
                    selection.bg,
                    theme.soft_selection_style().bg,
                    "{name}/{mode:?}: the selection is the one light wash"
                );
                assert!(
                    selection.add_modifier.is_empty(),
                    "{name}/{mode:?}: the selection carries no modifiers"
                );
                let band = selection.bg.expect("the selection paints a background");
                let band_lum = quantized_luminance(band)
                    .unwrap_or_else(|| panic!("{name}/{mode:?}: the band must evaluate"));
                let surface = theme
                    .bg_color(ThemeBg::UserMessageBg)
                    .and_then(quantized_luminance)
                    .expect("the editor surface evaluates");
                assert!(
                    (band_lum - surface).abs() >= SELECTION_MIN_LUMINANCE_DELTA - 1.0,
                    "{name}/{mode:?}: the light band reads off its surface"
                );
            }
        }
    }
}
