//! The terminal theme: a resolved [`eukhe_theme::Palette`] rendered as
//! terminal styles per color slot. The theme files, their validation and
//! name resolution live in `eukhe-theme` (the resolver the HTML export
//! shares; [`crate::theme_catalog`] mounts it). Colors render as truecolor
//! or 256-color ANSI depending on `COLORTERM`/`TERM`.

use crate::style::{Color, Modifier, Style};
use eukhe_theme::{ColorValue, Palette, Rgb, Token};
use std::sync::atomic::{AtomicU64, Ordering};

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
    /// Every slot, in declaration order: `ALL[color as usize] == color`.
    const ALL: [ThemeColor; 49] = [
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
        ThemeColor::ThinkingOff,
        ThemeColor::ThinkingMinimal,
        ThemeColor::ThinkingLow,
        ThemeColor::ThinkingMedium,
        ThemeColor::ThinkingHigh,
        ThemeColor::ThinkingXhigh,
        ThemeColor::BashMode,
    ];

    fn token(self) -> Token {
        match self {
            ThemeColor::Accent => Token::Accent,
            ThemeColor::Border => Token::Border,
            ThemeColor::BorderAccent => Token::BorderAccent,
            ThemeColor::BorderMuted => Token::BorderMuted,
            ThemeColor::Success => Token::Success,
            ThemeColor::Error => Token::Error,
            ThemeColor::Warning => Token::Warning,
            ThemeColor::Muted => Token::Muted,
            ThemeColor::Dim => Token::Dim,
            ThemeColor::Text => Token::Text,
            ThemeColor::ThinkingText => Token::ThinkingText,
            ThemeColor::UserMessageText => Token::UserMessageText,
            ThemeColor::CustomMessageText => Token::CustomMessageText,
            ThemeColor::CustomMessageLabel => Token::CustomMessageLabel,
            ThemeColor::RefinementHeader => Token::RefinementHeader,
            ThemeColor::RefinementSummary => Token::RefinementSummary,
            ThemeColor::ToolTitle => Token::ToolTitle,
            ThemeColor::ToolOutput => Token::ToolOutput,
            ThemeColor::MdBody => Token::MdBody,
            ThemeColor::MdHeading => Token::MdHeading,
            ThemeColor::MdLink => Token::MdLink,
            ThemeColor::MdLinkUrl => Token::MdLinkUrl,
            ThemeColor::MdCode => Token::MdCode,
            ThemeColor::MdCodeBlock => Token::MdCodeBlock,
            ThemeColor::MdCodeBlockBorder => Token::MdCodeBlockBorder,
            ThemeColor::MdQuote => Token::MdQuote,
            ThemeColor::MdQuoteBorder => Token::MdQuoteBorder,
            ThemeColor::MdHr => Token::MdHr,
            ThemeColor::MdListBullet => Token::MdListBullet,
            ThemeColor::ToolDiffAdded => Token::ToolDiffAdded,
            ThemeColor::ToolDiffRemoved => Token::ToolDiffRemoved,
            ThemeColor::ToolDiffText => Token::ToolDiffText,
            ThemeColor::ToolDiffContext => Token::ToolDiffContext,
            ThemeColor::SyntaxComment => Token::SyntaxComment,
            ThemeColor::SyntaxKeyword => Token::SyntaxKeyword,
            ThemeColor::SyntaxFunction => Token::SyntaxFunction,
            ThemeColor::SyntaxVariable => Token::SyntaxVariable,
            ThemeColor::SyntaxString => Token::SyntaxString,
            ThemeColor::SyntaxNumber => Token::SyntaxNumber,
            ThemeColor::SyntaxType => Token::SyntaxType,
            ThemeColor::SyntaxOperator => Token::SyntaxOperator,
            ThemeColor::SyntaxPunctuation => Token::SyntaxPunctuation,
            ThemeColor::ThinkingOff => Token::ThinkingOff,
            ThemeColor::ThinkingMinimal => Token::ThinkingMinimal,
            ThemeColor::ThinkingLow => Token::ThinkingLow,
            ThemeColor::ThinkingMedium => Token::ThinkingMedium,
            ThemeColor::ThinkingHigh => Token::ThinkingHigh,
            ThemeColor::ThinkingXhigh => Token::ThinkingXhigh,
            ThemeColor::BashMode => Token::BashMode,
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
        match self {
            ThemeBg::SelectedBg => Token::SelectedBg,
            ThemeBg::UserMessageBg => Token::UserMessageBg,
            ThemeBg::CustomMessageBg => Token::CustomMessageBg,
            ThemeBg::ToolPendingBg => Token::ToolPendingBg,
            ThemeBg::ToolSuccessBg => Token::ToolSuccessBg,
            ThemeBg::ToolErrorBg => Token::ToolErrorBg,
            ThemeBg::ToolDiffAddedBg => Token::ToolDiffAddedBg,
            ThemeBg::ToolDiffRemovedBg => Token::ToolDiffRemovedBg,
            ThemeBg::ToolPanelBg => Token::ToolPanelBg,
        }
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
};

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
        (Color::Rgb(r, g, b), ColorMode::Color256) => {
            Color::Indexed(eukhe_theme::rgb_to_256(Rgb::new(r, g, b)))
        }
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

/// The xterm-256 palette slot's RGB: the 6x6x6 cube and the gray ramp.
/// The base ANSI slots (0-15) are terminal-defined, so their rendered
/// color is unknown.
fn indexed_to_rgb(index: u8) -> Option<(u16, u16, u16)> {
    if eukhe_theme::is_terminal_defined(index) {
        return None;
    }
    let rgb = eukhe_theme::ansi256(index);
    Some((u16::from(rgb.r), u16::from(rgb.g), u16::from(rgb.b)))
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

/// Source of [`Theme::generation`]: every resolved theme gets a fresh one.
static NEXT_THEME_GENERATION: AtomicU64 = AtomicU64::new(0);

/// The active theme: resolved styles per color slot, indexed by the slot
/// enum's discriminant.
#[derive(Debug, Clone)]
pub struct Theme {
    pub name: String,
    fg: [Style; ThemeColor::ALL.len()],
    bg: [Option<Color>; ThemeBg::ALL.len()],
    /// The theme record's parseable `background` key, raw RGB: blends that
    /// use it (TS `onboardingHighlightBackground`) mix against the true
    /// colour and quantize their result per [`Theme::mode`], not this.
    background: Option<(u8, u8, u8)>,
    pub mode: ColorMode,
    /// Identity of this resolution: clones share it, so equal generations
    /// mean equal themes without comparing the tables.
    generation: u64,
}

impl PartialEq for Theme {
    fn eq(&self, other: &Self) -> bool {
        self.generation == other.generation
            || (self.name == other.name
                && self.fg == other.fg
                && self.bg == other.bg
                && self.background == other.background
                && self.mode == other.mode)
    }
}

impl Theme {
    /// Render a resolved palette for a terminal of `mode`: the terminal
    /// default (`""`) is [`Color::Reset`], an index stays an index, and a
    /// `#rrggbb` value quantizes in a 256-color terminal.
    #[must_use]
    pub fn from_palette(palette: &Palette, mode: ColorMode) -> Theme {
        let color = |token: Token| {
            let color = match palette.value(token) {
                ColorValue::Default => Color::Reset,
                ColorValue::Indexed(index) => Color::Indexed(index),
                ColorValue::Rgb(rgb) => Color::Rgb(rgb.r, rgb.g, rgb.b),
            };
            to_terminal_color(color, mode)
        };
        Theme {
            name: palette.name().to_string(),
            fg: ThemeColor::ALL.map(|slot| Style::default().fg(color(slot.token()))),
            bg: ThemeBg::ALL.map(|slot| Some(color(slot.token()))),
            background: palette
                .declared_background()
                .map(|rgb| (rgb.r, rgb.g, rgb.b)),
            mode,
            generation: NEXT_THEME_GENERATION.fetch_add(1, Ordering::Relaxed),
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
        let palette =
            Palette::builtin(name).unwrap_or_else(|| panic!("{name} is not a builtin theme"));
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
        .filter(|token| token.presence() == eukhe_theme::Presence::Required)
        .map(|token| (token.name().to_string(), serde_json::Value::from("")))
        .collect();
    colors.extend(overrides.as_object().expect("an object").clone());
    let file = serde_json::json!({ "name": "custom", "colors": colors });
    let palette = Palette::parse(&file.to_string()).expect("a valid theme");
    Theme::from_palette(&palette, mode)
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
    fn var_reference_resolves() {
        let theme = Theme::builtin("eukhe", ColorMode::Color256);
        let accent = theme.fg_style(ThemeColor::Accent);
        assert!(matches!(accent.fg, Some(Color::Indexed(_))));
    }

    /// The file's own `#rrggbb` `background` is the onboarding canvas; an
    /// empty one or an index leaves the canvas to the wash's fallback.
    #[test]
    fn background_is_the_declared_six_hex() {
        let theme = |background: serde_json::Value| {
            theme_with_colors(
                &serde_json::json!({ "background": background, "text": "#f4f4f5" }),
                ColorMode::TrueColor,
            )
            .background_rgb()
        };
        assert_eq!(
            [
                theme(serde_json::json!("#0A0B0C")),
                theme(serde_json::json!("")),
                theme(serde_json::json!(17)),
            ],
            [Some((0x0a, 0x0b, 0x0c)), None, None]
        );
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
