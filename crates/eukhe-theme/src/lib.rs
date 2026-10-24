//! Themes for every Eukhe surface that paints a theme file: the bundled
//! theme files (`themes/*.json`, beside their `theme-schema.json`), the
//! files the theme sources reach, read and decoded ([`RawTheme`]), the
//! complete [`Palette`] and the one theme name resolver ([`ThemeSources`])
//! of the terminal UI and the HTML export. Every decision on what was read
//! (validation, completion, the name a theme resolves to, the colors) runs
//! in the compiled Bend core (`bend/theme/`, `bend/color.bend`;
//! `laws/theme.bend`, docs/interface.md, Themes), passed in as
//! [`ThemeRules`].

mod color;
mod palette;
mod rules;
mod sources;
mod token;

pub use color::{is_terminal_defined, Mode, Rgb};
pub use palette::{
    ColorValue, ExportSurface, LoadFailure, Palette, PaletteParts, ThemeError, BUILTIN_THEME_NAMES,
    DEFAULT_THEME_NAME, LIGHT_THEME_NAME,
};
pub use rules::{Cause, Choice, Outcome, Picked, RawSource, RawTheme, RawValue, ThemeRules};
pub use sources::{ResolvedPalette, ThemeSources};
pub use token::Token;
