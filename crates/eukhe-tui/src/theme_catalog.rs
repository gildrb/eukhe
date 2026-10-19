//! The theme a client surface mounts: the settings' theme name resolved
//! through [`eukhe_theme::ThemeSources`] (the one resolver the HTML export
//! shares) and rendered for the terminal's color mode.

use eukhe_theme::ThemeSources;

use crate::client_settings::ClientSettings;
use crate::theme::{detect_color_mode, ColorMode, Theme};

/// A resolved theme and the problems met on the way.
#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedTheme {
    pub theme: Theme,
    /// One line per problem, the requested theme's failure first.
    pub warnings: Vec<String>,
}

/// Resolve `name` through `sources` (empty: the default theme; a missing
/// or invalid theme: the default theme and a warning) for `mode`.
#[must_use]
pub fn resolve_theme(sources: &ThemeSources, name: &str, mode: ColorMode) -> ResolvedTheme {
    let resolved = sources.resolve(name);
    ResolvedTheme {
        theme: Theme::from_palette(&resolved.palette, mode),
        warnings: resolved.warnings,
    }
}

/// The theme a client surface mounts: resolved through the settings
/// seam's sources (its warnings also go to the agent log), or through the
/// builtins alone when the surface runs without a seam.
#[must_use]
pub fn load_client_theme(settings: Option<&dyn ClientSettings>, name: &str) -> ResolvedTheme {
    let mode = detect_color_mode();
    let Some(settings) = settings else {
        return resolve_theme(&ThemeSources::default(), name, mode);
    };
    let resolved = resolve_theme(&settings.theme_sources(), name, mode);
    for warning in &resolved.warnings {
        settings.log_theme_warning(warning);
    }
    resolved
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::style::Color;
    use crate::theme::ThemeColor;

    const DUSK_APPLE: &str = include_str!("../../eukhe-theme/tests/fixtures/dusk-apple-theme.json");
    const MODE: ColorMode = ColorMode::TrueColor;

    /// The omp/pi theme file (`$schema`, vars, an `export` section)
    /// renders its var-resolved colors; the refinement pair it leaves out
    /// comes from the dark builtin (its background is dark).
    #[test]
    fn a_custom_theme_renders_its_colors() {
        let dir = tempfile::tempdir().expect("temp dir");
        std::fs::write(dir.path().join("dusk-apple.json"), DUSK_APPLE).expect("write theme");
        let resolved = resolve_theme(
            &ThemeSources {
                custom_dir: Some(dir.path().to_path_buf()),
                ..ThemeSources::default()
            },
            "dusk-apple",
            MODE,
        );
        assert_eq!(resolved.warnings, Vec::<String>::new());
        let fg = |color| resolved.theme.fg_style(color).fg;
        assert_eq!(
            [
                fg(ThemeColor::Muted),
                fg(ThemeColor::Dim),
                fg(ThemeColor::Text),
                fg(ThemeColor::MdBody),
                fg(ThemeColor::RefinementHeader),
            ],
            [
                Some(Color::Rgb(0xd9, 0xd0, 0xc6)),
                Some(Color::Rgb(0x9b, 0x96, 0x90)),
                Some(Color::Rgb(0xe9, 0xe4, 0xde)),
                Some(Color::Rgb(0xe9, 0xe4, 0xde)),
                Some(Color::Rgb(0x95, 0x75, 0xcd)),
            ]
        );
    }

    /// Without the registration (`--no-themes` drops the resource
    /// themes), a theme only a registered path provides is not found.
    #[test]
    fn an_unregistered_theme_falls_back_to_the_default() {
        assert_eq!(
            resolve_theme(&ThemeSources::default(), "dusk-apple", MODE),
            ResolvedTheme {
                theme: Theme::builtin(eukhe_theme::DEFAULT_THEME_NAME, MODE),
                warnings: vec![
                    "Theme \"dusk-apple\" unavailable, using \"eukhe\": Theme not found: \
                     dusk-apple"
                        .to_string()
                ],
            }
        );
    }
}
