//! The export's colors: a resolved theme ([`eukhe_theme::Palette`], from
//! the resolver the terminal UI shares) as the CSS custom properties the
//! export template reads. Every color comes from the theme, and every
//! value written is `#rrggbb`.

use eukhe_theme::{ExportSurface, Palette, Rgb, Token};

/// The CSS variables plus the three background colors the export template
/// substitutes.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ExportTheme {
    /// The `:root` custom-property block (`--token: #rrggbb;` per line).
    pub(crate) theme_vars: String,
    pub(crate) body_bg: Rgb,
    pub(crate) container_bg: Rgb,
    pub(crate) info_bg: Rgb,
}

/// The page, card and info backgrounds a theme without an `export`
/// section gets, derived from its user-message surface: a light surface
/// darkens the page slightly, a dark one darkens page and card more, and
/// the info row shifts toward a warm tint.
fn derived_backgrounds(base: Rgb) -> [Rgb; 3] {
    let shifted = |r: u8, g: u8, b: u8| {
        Rgb::new(
            base.r.saturating_add(r),
            base.g.saturating_add(g),
            base.b.saturating_sub(b),
        )
    };
    if eukhe_bend::rules::color::light(base.channels()) {
        [base.scaled(0.96), base, shifted(10, 5, 20)]
    } else {
        [base.scaled(0.7), base.scaled(0.85), shifted(20, 15, 0)]
    }
}

/// The export theme of `palette`: every token as a `--token` line, and
/// the export backgrounds (the theme's `export` section, else derived).
pub(crate) fn export_theme(palette: &Palette) -> ExportTheme {
    let theme_vars = Token::ALL
        .iter()
        .map(|token| format!("--{}: {};", token.name(), palette.rgb(*token)))
        .collect::<Vec<_>>()
        .join("\n      ");
    let [page, card, info] = derived_backgrounds(palette.rgb(Token::UserMessageBg));
    let surface =
        |surface: ExportSurface, derived: Rgb| palette.export_surface(surface).unwrap_or(derived);
    ExportTheme {
        theme_vars,
        body_bg: surface(ExportSurface::Page, page),
        container_bg: surface(ExportSurface::Card, card),
        info_bg: surface(ExportSurface::Info, info),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn palette(raw: &str) -> Palette {
        Palette::parse(raw, crate::theme_rules::THEME_RULES).expect("a valid theme")
    }

    /// The bundled eukhe theme: `--accent` through the `primary` variable,
    /// the terminal-default text as the theme's foreground, and the export
    /// section's `bg`/`surface`/`panel` references.
    #[test]
    fn the_default_theme_exports_its_variables_and_backgrounds() {
        let theme = export_theme(&Palette::default_theme(crate::theme_rules::THEME_RULES));
        let lines: Vec<&str> = theme.theme_vars.split("\n      ").collect();
        assert_eq!(lines.len(), Token::ALL.len());
        assert_eq!(
            [
                lines.contains(&"--accent: #7c6faf;"),
                lines.contains(&"--text: #e5e5e7;"),
                lines.contains(&"--background: #050506;"),
            ],
            [true, true, true]
        );
        assert_eq!(
            (theme.body_bg, theme.container_bg, theme.info_bg),
            (
                Rgb::new(0x05, 0x05, 0x06),
                Rgb::new(0x0d, 0x0d, 0x10),
                Rgb::new(0x15, 0x15, 0x18)
            )
        );
    }

    /// Without an `export` section the backgrounds derive from the
    /// user-message surface: a dark one at 0.7/0.85, the info row shifted
    /// +20/+15/+0; a light one at 0.96, the info row +10/+5/-20; the
    /// terminal default on that surface is the theme's background.
    #[test]
    fn backgrounds_derive_from_the_user_message_surface() {
        let dusk = palette(include_str!(
            "../../../eukhe-theme/tests/fixtures/dusk-apple-theme.json"
        ));
        let with_surface = |surface: &str| {
            let mut value: serde_json::Value = serde_json::from_str(include_str!(
                "../../../eukhe-theme/tests/fixtures/dusk-apple-theme.json"
            ))
            .expect("json");
            value["colors"]["userMessageBg"] = serde_json::Value::from(surface);
            value["colors"]["background"] = serde_json::Value::from(surface);
            let theme = export_theme(&palette(&value.to_string()));
            (theme.body_bg, theme.container_bg, theme.info_bg)
        };
        let dusk = export_theme(&dusk);
        assert_eq!(
            [
                with_surface("#343541"),
                with_surface("#eeeeee"),
                (dusk.body_bg, dusk.container_bg, dusk.info_bg),
            ],
            [
                (
                    Rgb::new(36, 37, 46),
                    Rgb::new(44, 45, 55),
                    Rgb::new(72, 68, 65)
                ),
                (
                    Rgb::new(228, 228, 228),
                    Rgb::new(238, 238, 238),
                    Rgb::new(248, 243, 218)
                ),
                // dusk-apple's surface is the terminal default: the default
                // theme's background, #050506.
                (Rgb::new(4, 4, 4), Rgb::new(4, 4, 5), Rgb::new(25, 20, 6)),
            ]
        );
    }
}
