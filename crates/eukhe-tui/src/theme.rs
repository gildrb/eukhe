//! The terminal theme: a resolved [`eukhe_theme::Palette`] rendered as
//! terminal styles per color slot. The theme files and name resolution
//! live in `eukhe-theme` (the resolver the HTML export shares;
//! [`crate::theme_catalog`] mounts it), its rules and the 256-color
//! quantization in the compiled core ([`crate::theme_rules`],
//! `eukhe_bend::rules::color`). Colors render as truecolor or 256-color
//! ANSI depending on `COLORTERM`/`TERM`.
//!
//! This module is the only place that makes a [`Color`]: its value is
//! private, so the compiler refuses a color literal in any other module.
//! Every color a frame paints is a theme token or a value computed here
//! from the tokens.

use crate::style::{Modifier, Style};
use eukhe_bend::rules::tui_color;
use eukhe_theme::{ColorValue, Mode, Palette, Rgb, Token};
use std::collections::HashMap;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, LazyLock, Mutex, PoisonError};

/// A terminal color. Only the theme module makes one (the value is
/// private): other code gets colors from a [`Theme`] and cannot write
/// one. The SGR encoding reads it through [`Color::fg_sgr`] and
/// [`Color::bg_sgr`].
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Color(Paint);

/// What a [`Color`] paints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Paint {
    /// The terminal's default color (SGR 39 / 49).
    Reset,
    /// A 256-color palette index (SGR 38;5 / 48;5).
    Indexed(u8),
    /// A 24-bit color (SGR 38;2 / 48;2).
    Rgb(u8, u8, u8),
}

impl Color {
    const RESET: Color = Color(Paint::Reset);

    const fn rgb(rgb: Rgb) -> Color {
        Color(Paint::Rgb(rgb.r, rgb.g, rgb.b))
    }

    /// The SGR parameters that paint this color as the foreground.
    pub(crate) fn fg_sgr(self) -> String {
        match self.0 {
            Paint::Reset => "39".to_string(),
            Paint::Indexed(index) => format!("38;5;{index}"),
            Paint::Rgb(r, g, b) => format!("38;2;{r};{g};{b}"),
        }
    }

    /// The SGR parameters that paint this color as the background.
    pub(crate) fn bg_sgr(self) -> String {
        match self.0 {
            Paint::Reset => "49".to_string(),
            Paint::Indexed(index) => format!("48;5;{index}"),
            Paint::Rgb(r, g, b) => format!("48;2;{r};{g};{b}"),
        }
    }

    /// The RGB this color paints where the terminal does not decide it:
    /// none for the terminal default and the base ANSI slots (0-15).
    fn known_rgb(self) -> Option<Rgb> {
        match self.0 {
            Paint::Rgb(r, g, b) => Some(Rgb::new(r, g, b)),
            Paint::Indexed(index) => (!eukhe_theme::is_terminal_defined(index))
                .then(|| Rgb::from_channels(eukhe_bend::rules::color::ansi256(index))),
            Paint::Reset => None,
        }
    }
}

/// The variant form, `Rgb(1, 2, 3)`, which the [`Style`] builder chain
/// prints after `Color::`.
impl fmt::Debug for Color {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
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
    ContextHigh,
    BashMode,
}

impl ThemeColor {
    /// Every slot, in declaration order: `ALL[color as usize] == color`.
    const ALL: [ThemeColor; 44] = [
        ThemeColor::Accent,
        ThemeColor::Border,
        ThemeColor::BorderAccent,
        ThemeColor::BorderMuted,
        ThemeColor::Success,
        ThemeColor::Error,
        ThemeColor::Warning,
        ThemeColor::Muted,
        ThemeColor::Dim,
        ThemeColor::Text,
        ThemeColor::ThinkingText,
        ThemeColor::UserMessageText,
        ThemeColor::CustomMessageText,
        ThemeColor::CustomMessageLabel,
        ThemeColor::RefinementHeader,
        ThemeColor::RefinementSummary,
        ThemeColor::ToolTitle,
        ThemeColor::ToolOutput,
        ThemeColor::MdBody,
        ThemeColor::MdHeading,
        ThemeColor::MdLink,
        ThemeColor::MdLinkUrl,
        ThemeColor::MdCode,
        ThemeColor::MdCodeBlock,
        ThemeColor::MdCodeBlockBorder,
        ThemeColor::MdQuote,
        ThemeColor::MdQuoteBorder,
        ThemeColor::MdHr,
        ThemeColor::MdListBullet,
        ThemeColor::ToolDiffAdded,
        ThemeColor::ToolDiffRemoved,
        ThemeColor::ToolDiffText,
        ThemeColor::ToolDiffContext,
        ThemeColor::SyntaxComment,
        ThemeColor::SyntaxKeyword,
        ThemeColor::SyntaxFunction,
        ThemeColor::SyntaxVariable,
        ThemeColor::SyntaxString,
        ThemeColor::SyntaxNumber,
        ThemeColor::SyntaxType,
        ThemeColor::SyntaxOperator,
        ThemeColor::SyntaxPunctuation,
        ThemeColor::ContextHigh,
        ThemeColor::BashMode,
    ];

    fn token(self) -> Token {
        ROLES.fg[self as usize]
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
    /// Every slot, in declaration order: `ALL[bg as usize] == bg`.
    const ALL: [ThemeBg; 9] = [
        ThemeBg::SelectedBg,
        ThemeBg::UserMessageBg,
        ThemeBg::CustomMessageBg,
        ThemeBg::ToolPendingBg,
        ThemeBg::ToolSuccessBg,
        ThemeBg::ToolErrorBg,
        ThemeBg::ToolDiffAddedBg,
        ThemeBg::ToolDiffRemovedBg,
        ThemeBg::ToolPanelBg,
    ];

    fn token(self) -> Token {
        ROLES.bg[self as usize]
    }
}

/// The theme colors the terminal UI computes with instead of painting
/// them as they are: the effort ramp's two ends, the two ends a selection
/// band lifts toward, and the canvas (the theme's background) that the
/// onboarding wash lifts from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ThemeRgb {
    EffortLow,
    EffortHigh,
    LiftLight,
    LiftDark,
    Canvas,
}

impl ThemeRgb {
    /// Every slot, in declaration order: `ALL[slot as usize] == slot`.
    const ALL: [ThemeRgb; 5] = [
        ThemeRgb::EffortLow,
        ThemeRgb::EffortHigh,
        ThemeRgb::LiftLight,
        ThemeRgb::LiftDark,
        ThemeRgb::Canvas,
    ];

    fn token(self) -> Token {
        ROLES.rgb[self as usize]
    }
}

// The slot tables index by discriminant: each `ALL` lists its enum in
// declaration order.
const _: () = {
    let mut index = 0;
    while index < ThemeColor::ALL.len() {
        assert!(ThemeColor::ALL[index] as usize == index);
        index += 1;
    }
    let mut index = 0;
    while index < ThemeBg::ALL.len() {
        assert!(ThemeBg::ALL[index] as usize == index);
        index += 1;
    }
    let mut index = 0;
    while index < ThemeRgb::ALL.len() {
        assert!(ThemeRgb::ALL[index] as usize == index);
        index += 1;
    }
};

/// The theme token of every color slot, decided by the compiled core
/// (`bend/tui_color.bend` `roles`, entry `bend/ffi_tui_color.bend`): the
/// ink slots ([`ThemeColor`]), the surface slots ([`ThemeBg`]) and the
/// colors the UI computes with ([`ThemeRgb`]), each in declaration order.
struct Roles {
    fg: [Token; ThemeColor::ALL.len()],
    bg: [Token; ThemeBg::ALL.len()],
    rgb: [Token; ThemeRgb::ALL.len()],
}

/// The roles, asked of the core once per process (they are constant).
static ROLES: LazyLock<Roles> = LazyLock::new(Roles::from_core);

impl Roles {
    /// # Panics
    ///
    /// When the core names another count of slots or a token past the
    /// table: an inconsistent build (`laws/tui_color.bend`
    /// `tui_roles_cover` holds 58 distinct tokens below 58).
    fn from_core() -> Roles {
        let tokens: Vec<Token> = tui_color::roles()
            .into_iter()
            .map(|index| Token::ALL[index])
            .collect();
        let (fg, rest) = tokens.split_at(ThemeColor::ALL.len());
        let (bg, rgb) = rest.split_at(ThemeBg::ALL.len());
        let slots = "the core names one token per color slot";
        Roles {
            fg: fg.try_into().expect(slots),
            bg: bg.try_into().expect(slots),
            rgb: rgb.try_into().expect(slots),
        }
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
    match (color.0, mode) {
        (Paint::Rgb(r, g, b), ColorMode::Color256) => {
            Color(Paint::Indexed(eukhe_bend::rules::color::to256([r, g, b])))
        }
        (Paint::Rgb(..) | Paint::Indexed(_) | Paint::Reset, ColorMode::TrueColor)
        | (Paint::Indexed(_) | Paint::Reset, ColorMode::Color256) => color,
    }
}

/// The channels of a color, as the core reads them.
fn channels(rgb: Rgb) -> tui_color::Rgb {
    [rgb.r, rgb.g, rgb.b]
}

/// The effort ramps a theme has drawn, by rung count: the core computes
/// each once per theme (clones share them), not once per frame.
#[derive(Debug, Default, Clone)]
struct EffortRamps(Arc<Mutex<HashMap<usize, Arc<[Rgb]>>>>);

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
fn luminance(rgb: Rgb) -> f64 {
    0.299 * f64::from(rgb.r) + 0.587 * f64::from(rgb.g) + 0.114 * f64::from(rgb.b)
}

/// The luminance of what actually renders: a 256-color terminal paints the
/// palette slot, not the configured RGB (the quantized candidate evaluates
/// through this; base ANSI slots stay unknown).
pub(crate) fn quantized_luminance(color: Color) -> Option<f64> {
    color.known_rgb().map(luminance)
}

/// `alpha` of `top` over `1 - alpha` of `bottom`, per channel.
fn blend(top: Rgb, bottom: Rgb, alpha: f64) -> Rgb {
    let channel = |top: u8, bottom: u8| {
        (f64::from(top) * alpha + f64::from(bottom) * (1.0 - alpha))
            .round()
            .clamp(0.0, 255.0) as u8
    };
    Rgb::new(
        channel(top.r, bottom.r),
        channel(top.g, bottom.g),
        channel(top.b, bottom.b),
    )
}

/// How far the onboarding wash lifts the canvas toward the lift end (TS
/// `HIGHLIGHT_LIFT`).
const HIGHLIGHT_LIFT: f64 = 0.08;

/// Source of [`Theme::generation`]: every resolved theme gets a fresh one.
static NEXT_THEME_GENERATION: AtomicU64 = AtomicU64::new(0);

/// The active theme: resolved styles per color slot, indexed by the slot
/// enum's discriminant.
#[derive(Debug, Clone)]
pub struct Theme {
    pub name: String,
    fg: [Style; ThemeColor::ALL.len()],
    bg: [Option<Color>; ThemeBg::ALL.len()],
    /// The colors the theme computes with ([`ThemeRgb`]), as the palette
    /// paints them (`Palette::rgb`): blends mix the true colors and
    /// quantize their result per [`Theme::mode`].
    rgb: [Rgb; ThemeRgb::ALL.len()],
    /// Light or dark, by the background's luminance (never the name).
    canvas_mode: Mode,
    pub mode: ColorMode,
    /// Identity of this resolution: clones share it, so equal generations
    /// mean equal themes without comparing the tables.
    generation: u64,
    /// The effort ramps drawn so far ([`Theme::effort_ramp`]).
    effort_ramps: EffortRamps,
}

impl PartialEq for Theme {
    fn eq(&self, other: &Self) -> bool {
        self.generation == other.generation
            || (self.name == other.name
                && self.fg == other.fg
                && self.bg == other.bg
                && self.rgb == other.rgb
                && self.canvas_mode == other.canvas_mode
                && self.mode == other.mode)
    }
}

impl Theme {
    /// Render a resolved palette for a terminal of `mode`: the terminal
    /// default (`""`) is the terminal's own color, an index stays an
    /// index, and a `#rrggbb` value quantizes in a 256-color terminal.
    #[must_use]
    pub fn from_palette(palette: &Palette, mode: ColorMode) -> Theme {
        let color = |token: Token| {
            let color = match palette.value(token) {
                ColorValue::Default => Color::RESET,
                ColorValue::Indexed(index) => Color(Paint::Indexed(index)),
                ColorValue::Rgb(rgb) => Color::rgb(rgb),
            };
            to_terminal_color(color, mode)
        };
        Theme {
            name: palette.name().to_string(),
            fg: ThemeColor::ALL.map(|slot| Style::default().fg(color(slot.token()))),
            bg: ThemeBg::ALL.map(|slot| Some(color(slot.token()))),
            rgb: ThemeRgb::ALL.map(|slot| palette.rgb(slot.token())),
            canvas_mode: palette.mode(),
            mode,
            generation: NEXT_THEME_GENERATION.fetch_add(1, Ordering::Relaxed),
            effort_ramps: EffortRamps::default(),
        }
    }

    /// A bundled theme ([`eukhe_theme::BUILTIN_THEME_NAMES`]).
    /// User-facing names resolve through [`eukhe_theme::ThemeSources`],
    /// which reports unknown names.
    ///
    /// # Panics
    ///
    /// Panics when `name` is not a builtin: callers name builtins
    /// statically.
    #[must_use]
    pub fn builtin(name: &str, mode: ColorMode) -> Theme {
        let palette = Palette::builtin(name, crate::theme_rules::THEME_RULES)
            .unwrap_or_else(|| panic!("{name} is not a builtin theme"));
        Theme::from_palette(&palette, mode)
    }

    #[must_use]
    pub fn fg_style(&self, color: ThemeColor) -> Style {
        self.fg[color as usize]
    }

    #[must_use]
    pub fn bg_style(&self, color: ThemeBg) -> Style {
        self.bg_color(color)
            .map_or_else(Style::default, |bg| Style::default().bg(bg))
    }

    #[must_use]
    pub fn bg_color(&self, color: ThemeBg) -> Option<Color> {
        self.bg[color as usize]
    }

    /// Identity of this resolution (shared by clones): a frame compares
    /// it to skip re-checking an unchanged theme.
    pub(crate) fn generation(&self) -> u64 {
        self.generation
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

    /// The effort ramp for a ladder of `rungs` levels: the style of each
    /// rung, lowest first, from the theme's `effortLow` toward its
    /// `effortHigh`, as the compiled core draws it (`bend/tui_color.bend`
    /// `ramp`; the last rung is `effortHigh`). The core draws each length
    /// once per theme.
    ///
    /// # Panics
    ///
    /// When `rungs` is above [`tui_color::RAMP_MAX`]: callers pass a
    /// model's effort ladder, a few levels of the level vocabulary.
    pub fn effort_ramp(&self, rungs: usize) -> impl Iterator<Item = Style> + '_ {
        let ramp = Arc::clone(
            self.effort_ramps
                .0
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .entry(rungs)
                .or_insert_with(|| {
                    tui_color::ramp(
                        channels(self.rgb[ThemeRgb::EffortLow as usize]),
                        channels(self.rgb[ThemeRgb::EffortHigh as usize]),
                        rungs,
                    )
                    .into_iter()
                    .map(|[r, g, b]| Rgb::new(r, g, b))
                    .collect()
                }),
        );
        (0..ramp.len()).map(move |rung| {
            Style::default().fg(to_terminal_color(Color::rgb(ramp[rung]), self.mode))
        })
    }

    /// The selected-row wash (TS `onboardingHighlightBackground`): the
    /// canvas (the theme's background, `Palette::rgb`) lifted a few
    /// percent toward `liftLight` on a dark theme and `liftDark` on a
    /// light one (the mode comes from the background, never the name),
    /// quantized per [`Theme::mode`].
    pub(crate) fn highlight_wash(&self) -> Color {
        let lift = match self.canvas_mode {
            Mode::Dark => ThemeRgb::LiftLight,
            Mode::Light => ThemeRgb::LiftDark,
        };
        let washed = blend(
            self.rgb[lift as usize],
            self.rgb[ThemeRgb::Canvas as usize],
            HIGHLIGHT_LIFT,
        );
        to_terminal_color(Color::rgb(washed), self.mode)
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
    /// toward the theme's lift end -- `liftLight` when the selection
    /// reads lighter than the surface, `liftDark` when it reads darker --
    /// until it
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
        // The blend needs real RGB. A truecolor theme carries its
        // configured RGB directly; a 256-color theme stores the
        // quantized slot, whose palette RGB is what the terminal
        // actually renders there. The base ANSI slots (0-15) are
        // terminal-defined, so those keep the plain selection (TS's
        // ANSI guard: no reliable blend base exists).
        let (Some(selection), Some(editor_surface)) = (
            self.bg_color(ThemeBg::SelectedBg)
                .and_then(Color::known_rgb),
            self.bg_color(ThemeBg::UserMessageBg)
                .and_then(Color::known_rgb),
        ) else {
            return self.bg_style(ThemeBg::SelectedBg);
        };
        let surface_ansi = to_terminal_color(Color::rgb(editor_surface), self.mode);
        // The selection also evaluates through the palette: a 256-color
        // terminal paints the quantized slot, so the ladder aims from
        // what actually renders (TS's `renderedSelection`).
        let selection_render_luminance =
            quantized_luminance(to_terminal_color(Color::rgb(selection), self.mode))
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
            let adjusted = to_terminal_color(
                Color::rgb(blend(selection, editor_surface, alpha)),
                self.mode,
            );
            if adjusted != surface_ansi && reads(adjusted) {
                return Style::default().bg(adjusted);
            }
        }
        // The blend reads too close to the surface (every built-in
        // theme): step the wash toward a lift end -- the one on the
        // selection's side of the surface first, the opposite one
        // (crossing the surface) second -- until the quantized candidate
        // clears the bar. The strongest step is tracked across BOTH
        // ends like TS: the first candidate to clear the bar wins,
        // and when nothing clears it a step replaces the selection only
        // if it improved on the selection's own delta.
        let delta = (selection_render_luminance - surface_render_luminance).abs();
        let (light, dark) = (
            self.rgb[ThemeRgb::LiftLight as usize],
            self.rgb[ThemeRgb::LiftDark as usize],
        );
        let endpoints = if selection_render_luminance >= surface_render_luminance {
            [light, dark]
        } else {
            [dark, light]
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
                let candidate = to_terminal_color(
                    Color::rgb(blend(endpoint, selection, f64::from(alpha))),
                    self.mode,
                );
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
    /// the terminal default, which paints nothing) falls through to the
    /// onboarding wash, so a selected row always reads as selected
    /// (Macroscope PR #2908's contract).
    #[must_use]
    pub fn selection_row_style(&self) -> Style {
        let band = self
            .soft_selection_style()
            .bg
            .filter(|color| *color != Color::RESET)
            .unwrap_or_else(|| self.highlight_wash());
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

/// Tests: a theme whose required tokens are all the terminal default
/// (`""`), with the `colors` entries of `overrides` (a JSON object) on
/// top, rendered for `mode`.
///
/// # Panics
///
/// Panics when the result is not a valid theme.
#[cfg(test)]
pub(crate) fn theme_with_colors(overrides: &serde_json::Value, mode: ColorMode) -> Theme {
    let mut colors: serde_json::Map<String, serde_json::Value> = Token::ALL
        .into_iter()
        .filter(|token| {
            // The optional tokens: a file may leave them to their fallbacks.
            !matches!(
                token,
                Token::RefinementHeader
                    | Token::RefinementSummary
                    | Token::MdBody
                    | Token::Background
                    | Token::Foreground
            )
        })
        .map(|token| (token.name().to_string(), serde_json::Value::from("")))
        .collect();
    colors.extend(overrides.as_object().expect("an object").clone());
    let file = serde_json::json!({ "name": "custom", "colors": colors });
    let palette =
        Palette::parse(&file.to_string(), crate::theme_rules::THEME_RULES).expect("a valid theme");
    Theme::from_palette(&palette, mode)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prime_theme_resolves() {
        let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
        assert_eq!(
            [
                theme.fg_style(ThemeColor::Accent).fg,
                theme.bg_style(ThemeBg::ToolPanelBg).bg,
            ],
            [
                Some(Color(Paint::Rgb(0x7c, 0x6f, 0xaf))),
                Some(Color(Paint::Rgb(0x0d, 0x0d, 0x10))),
            ]
        );
    }

    #[test]
    fn var_reference_resolves() {
        let theme = Theme::builtin("eukhe", ColorMode::Color256);
        let accent = theme.fg_style(ThemeColor::Accent);
        assert!(matches!(accent.fg, Some(Color(Paint::Indexed(_)))));
    }

    /// The effort ramp comes from the theme and the ladder's length: the
    /// light theme's three rungs run from one step above its `effortLow`
    /// (#875f87) to its `effortHigh` (#8b008b), not a fixed violet.
    #[test]
    fn the_effort_ramp_follows_the_theme_and_the_ladder() {
        let light = Theme::builtin("light", ColorMode::TrueColor);
        assert_eq!(
            light.effort_ramp(3).collect::<Vec<Style>>(),
            [(136, 63, 136), (137, 31, 137), (139, 0, 139)]
                .map(|(r, g, b)| Style::default().fg(Color(Paint::Rgb(r, g, b))))
        );
        let eukhe = Theme::builtin("eukhe", ColorMode::TrueColor);
        assert_eq!(
            eukhe.effort_ramp(1).collect::<Vec<Style>>(),
            [Style::default().fg(Color(Paint::Rgb(0xa7, 0x8b, 0xfa)))]
        );
    }

    /// The wash lifts the theme's background toward its lift end: the
    /// `liftLight` end on a dark background, the `liftDark` end on a
    /// light one. The builtin themes lift their own background (eukhe:
    /// #050506), never a canvas written in code.
    #[test]
    fn the_wash_lifts_the_canvas_toward_the_lift_end() {
        let wash = |colors: serde_json::Value, mode: ColorMode| {
            theme_with_colors(&colors, mode).highlight_wash()
        };
        let tinted = serde_json::json!({ "background": "#050506", "liftLight": "#ff0000", "liftDark": "#00ff00" });
        let light = serde_json::json!({ "background": "#f0f0f0", "liftLight": "#ffffff", "liftDark": "#000000" });
        assert_eq!(
            [
                wash(tinted.clone(), ColorMode::TrueColor),
                wash(tinted, ColorMode::Color256),
                wash(light, ColorMode::TrueColor),
                Theme::builtin("eukhe", ColorMode::TrueColor).highlight_wash(),
            ],
            [
                Color(Paint::Rgb(25, 5, 6)),
                Color(Paint::Indexed(eukhe_bend::rules::color::to256([25, 5, 6]))),
                Color(Paint::Rgb(221, 221, 221)),
                Color(Paint::Rgb(25, 25, 26)),
            ]
        );
    }

    /// The contrast ladder steps toward the theme's lift ends: a red
    /// `liftLight` gives a red-tinted band where a white one gives gray.
    #[test]
    fn the_selection_ladder_steps_toward_the_lift_end() {
        let band = |lift: &str| {
            theme_with_colors(
                &serde_json::json!({
                    "selectedBg": "#222226",
                    "userMessageBg": "#1a1a1f",
                    "liftLight": lift,
                    "liftDark": "#000000",
                }),
                ColorMode::TrueColor,
            )
            .soft_selection_style()
            .bg
        };
        assert_eq!(
            [band("#ff0000"), band("#ffffff")],
            [
                Some(Color(Paint::Rgb(140, 18, 20))),
                Some(Color(Paint::Rgb(54, 54, 58)))
            ]
        );
    }

    /// The ONE selection style paints the soft wash in every theme,
    /// never the accent, never a bold modifier. A theme whose slots
    /// resolve to no band (a `selectedBg` that is missing or
    /// explicitly empty resolves to the terminal default, which paints
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
        let loud = theme_with_colors(
            &serde_json::json!({ "text": "#f4f4f5", "accent": "#ff00ff", "selectedBg": "#222226" }),
            ColorMode::TrueColor,
        );
        assert_eq!(
            loud.selection_row_style().bg,
            loud.soft_selection_style().bg,
            "the accent stays out of the band even when it is loud"
        );
        // An empty `selectedBg` resolves to Reset, which the band filters:
        // the wash takes the band.
        let empty_slot = theme_with_colors(
            &serde_json::json!({ "text": "#f4f4f5", "selectedBg": "" }),
            ColorMode::TrueColor,
        );
        assert_eq!(empty_slot.bg_color(ThemeBg::SelectedBg), Some(Color::RESET));
        assert_eq!(
            empty_slot.selection_row_style().bg,
            Some(empty_slot.highlight_wash()),
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
    /// (the white `liftLight` for the dark themes, the black `liftDark`
    /// for the light one), and the
    /// 256-color palette keeps a slot the surface's slot separates from.
    #[test]
    fn soft_selection_pins_the_contrast_ladder_values() {
        let prime = Theme::builtin("eukhe", ColorMode::TrueColor);
        assert_eq!(
            prime.soft_selection_style().bg,
            Some(Color(Paint::Rgb(54, 54, 58)))
        );
        let prime256 = Theme::builtin("eukhe", ColorMode::Color256);
        assert_eq!(
            prime256.soft_selection_style().bg,
            Some(Color(Paint::Indexed(237)))
        );
        let dark = Theme::builtin("dark", ColorMode::TrueColor);
        assert_eq!(
            dark.soft_selection_style().bg,
            Some(Color(Paint::Rgb(80, 80, 95)))
        );
        let dark256 = Theme::builtin("dark", ColorMode::Color256);
        assert_eq!(
            dark256.soft_selection_style().bg,
            Some(Color(Paint::Indexed(244)))
        );
        let light = Theme::builtin("light", ColorMode::TrueColor);
        assert_eq!(
            light.soft_selection_style().bg,
            Some(Color(Paint::Rgb(202, 202, 218)))
        );
        let light256 = Theme::builtin("light", ColorMode::Color256);
        assert_eq!(
            light256.soft_selection_style().bg,
            Some(Color(Paint::Indexed(251)))
        );
    }

    /// No reliable blend base, no ladder: a base-ANSI selection (the
    /// terminal defines its rendered color) keeps the plain selection --
    /// TS's ANSI guard.
    #[test]
    fn soft_selection_keeps_the_plain_selection_without_a_blend_base() {
        let theme = theme_with_colors(
            &serde_json::json!({ "selectedBg": 4, "userMessageBg": "#1a1a1f" }),
            ColorMode::TrueColor,
        );
        assert_eq!(
            theme.soft_selection_style().bg,
            theme.bg_style(ThemeBg::SelectedBg).bg
        );
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
