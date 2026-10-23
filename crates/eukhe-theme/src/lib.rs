//! Themes for every Eukhe surface that paints a theme file: the bundled
//! theme files (`themes/*.json`, beside their `theme-schema.json`), their
//! strict validation into a complete [`Palette`], the one theme name
//! resolver ([`ThemeSources`]) of the terminal UI and the HTML export, and
//! the color math both use (WCAG luminance and contrast, the ANSI-256
//! palette and quantization). `bend/theme.bend` and `bend/color.bend` model
//! it; `laws/theme.bend` states its laws (docs/interface.md, Themes).

mod color;
mod palette;
mod sources;
mod token;

pub use color::{
    ansi256, contrast_at_least, is_terminal_defined, linear_channel, luminance, rgb_to_256,
    ContrastRatio, Mode, Rgb, LINEAR_ONE, LUMINANCE_ONE,
};
pub use palette::{
    ColorValue, ExportSurface, LoadFailure, Palette, ThemeError, BUILTIN_THEME_NAMES,
    DEFAULT_THEME_NAME, LIGHT_THEME_NAME,
};
pub use sources::{ResolvedPalette, ThemeSources};
pub use token::{Layer, Presence, Token};
