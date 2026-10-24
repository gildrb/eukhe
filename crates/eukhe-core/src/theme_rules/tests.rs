//! The theme rules end to end: the bundled files paint the model's shipped
//! tables, and names resolve over real files through the compiled core.

use std::path::Path;

use eukhe_theme::{
    ColorValue, Mode, Palette, ResolvedPalette, Rgb, ThemeSources, Token, BUILTIN_THEME_NAMES,
};

use super::THEME_RULES;

const DUSK_APPLE: &str = include_str!("../../../eukhe-theme/tests/fixtures/dusk-apple-theme.json");

fn write(path: &Path, content: &str) {
    std::fs::create_dir_all(path.parent().expect("parent")).expect("dir");
    std::fs::write(path, content).expect("write theme");
}

fn custom_dir_sources(dir: &Path) -> ThemeSources {
    ThemeSources {
        custom_dir: Some(dir.to_path_buf()),
        ..ThemeSources::default()
    }
}

fn parse(raw: &str) -> Palette {
    Palette::parse(raw, THEME_RULES).expect("a valid theme")
}

fn default_with(warnings: Vec<String>) -> ResolvedPalette {
    ResolvedPalette {
        palette: Palette::default_theme(THEME_RULES),
        warnings,
    }
}

/// The bundled files paint the tables the laws check (legible, status
/// colors distinct): `bend/theme/bundled.bend` holds them.
#[test]
fn the_bundled_files_paint_the_shipped_tables() {
    for (index, name) in (0..).zip(BUILTIN_THEME_NAMES) {
        let palette = Palette::builtin(name, THEME_RULES).expect("builtin");
        let paints: Vec<[u8; 3]> = Token::ALL
            .iter()
            .map(|token| palette.rgb(*token).channels())
            .collect();
        assert_eq!(paints, eukhe_bend::rules::theme::shipped(index), "{name}");
    }
}

/// The builtins load with their names, modes and backgrounds.
#[test]
fn builtins_load_with_their_modes() {
    let modes: Vec<(String, Mode, Rgb)> = BUILTIN_THEME_NAMES
        .iter()
        .map(|name| {
            let palette = Palette::builtin(name, THEME_RULES).expect("builtin");
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

/// The JSON a file holds reaches the rules: variables, an index, the
/// terminal default and a light background.
#[test]
fn a_file_decodes_into_the_rules() {
    let mut value: serde_json::Value = serde_json::from_str(DUSK_APPLE).expect("json");
    value["colors"]["accent"] = serde_json::Value::from(4);
    value["colors"]["text"] = serde_json::Value::from("");
    value["colors"]["background"] = serde_json::Value::from("#fafafa");
    let palette = parse(&value.to_string());
    assert_eq!(
        (
            palette.value(Token::Accent),
            palette.rgb(Token::Accent),
            palette.value(Token::Text),
            palette.mode()
        ),
        (
            ColorValue::Indexed(4),
            Rgb::new(0, 0, 128),
            ColorValue::Default,
            Mode::Light
        )
    );
}

/// A custom-directory file resolves by the name it advertises, not by its
/// file name.
#[test]
fn a_custom_theme_resolves_by_its_json_name() {
    let dir = tempfile::tempdir().expect("temp dir");
    write(&dir.path().join("renamed.json"), DUSK_APPLE);
    assert_eq!(
        custom_dir_sources(dir.path()).resolve("dusk-apple", THEME_RULES),
        ResolvedPalette {
            palette: parse(DUSK_APPLE),
            warnings: Vec::new(),
        }
    );
}

#[test]
fn an_invalid_theme_warns_and_falls_back_to_the_default() {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("dusk-apple.json");
    write(
        &path,
        &DUSK_APPLE.replacen("\"accent\": \"accent\"", "\"accent\": \"nope\"", 1),
    );
    assert_eq!(
        custom_dir_sources(dir.path()).resolve("dusk-apple", THEME_RULES),
        default_with(vec![format!(
            "Theme \"dusk-apple\" unavailable, using \"eukhe\": Invalid theme {}: color \
             \"accent\": Variable reference not found: nope",
            path.display()
        )])
    );
}

/// A registered file (`--theme <path>`) resolves by its JSON name; a
/// registered file that fails to parse warns even when another theme is
/// requested; an empty name is the default theme.
#[test]
fn registered_files_resolve_by_their_json_name() {
    let dir = tempfile::tempdir().expect("temp dir");
    let renamed = dir.path().join("cli-theme.json");
    write(&renamed, DUSK_APPLE);
    let malformed = dir.path().join("extra").join("malformed.json");
    write(&malformed, "{ not json");
    let sources = ThemeSources {
        registered: vec![renamed, malformed.parent().expect("dir").to_path_buf()],
        ..ThemeSources::default()
    };
    let malformed_warning = format!(
        "Failed to parse theme {}: key must be a string at line 1 column 3",
        malformed.display()
    );
    assert_eq!(
        [
            sources.resolve("dusk-apple", THEME_RULES),
            sources.resolve("", THEME_RULES)
        ],
        [
            ResolvedPalette {
                palette: parse(DUSK_APPLE),
                warnings: vec![malformed_warning.clone()],
            },
            default_with(vec![malformed_warning]),
        ]
    );
    assert_eq!(
        sources.available_names(THEME_RULES),
        ["dark", "dusk-apple", "eukhe", "light"]
    );
}

/// A registered file shadows a builtin of the same name; a second file
/// with a name already taken and other colors warns and loses; a second
/// file with the same theme loses silently.
#[test]
fn the_first_file_with_a_name_wins() {
    let dir = tempfile::tempdir().expect("temp dir");
    let first = dir.path().join("a.json");
    let second = dir.path().join("b.json");
    let same = dir.path().join("c.json");
    let registered_dark = DUSK_APPLE.replacen("\"name\": \"dusk-apple\"", "\"name\": \"dark\"", 1);
    write(&first, &registered_dark);
    write(&second, &registered_dark.replacen("#c4a77d", "#c4a77e", 1));
    write(&same, &registered_dark);
    let resolved = ThemeSources {
        registered: vec![first.clone(), second.clone(), same],
        ..ThemeSources::default()
    }
    .resolve("dark", THEME_RULES);
    assert_ne!(
        resolved.palette,
        Palette::builtin("dark", THEME_RULES).expect("dark")
    );
    assert_eq!(
        resolved,
        ResolvedPalette {
            palette: parse(&registered_dark),
            warnings: vec![format!(
                "Theme name \"dark\" collision: {} (using {})",
                second.display(),
                first.display()
            )],
        }
    );
}

#[test]
fn a_missing_registered_path_warns() {
    let dir = tempfile::tempdir().expect("temp dir");
    let missing = dir.path().join("gone.json");
    assert_eq!(
        ThemeSources {
            registered: vec![missing.clone()],
            ..ThemeSources::default()
        }
        .resolve("dark", THEME_RULES),
        ResolvedPalette {
            palette: Palette::builtin("dark", THEME_RULES).expect("dark"),
            warnings: vec![format!("Theme path does not exist: {}", missing.display())],
        }
    );
}

/// A name is never a path: `../x` finds no file outside the sources, even
/// when that file is a valid theme.
#[test]
fn a_name_never_reaches_outside_the_sources() {
    let dir = tempfile::tempdir().expect("temp dir");
    let themes = dir.path().join("themes");
    std::fs::create_dir_all(&themes).expect("themes dir");
    write(&dir.path().join("escaped.json"), DUSK_APPLE);
    assert_eq!(
        custom_dir_sources(&themes).resolve("../escaped", THEME_RULES),
        default_with(vec![
            "Theme \"../escaped\" unavailable, using \"eukhe\": Theme not found: ../escaped"
                .to_string()
        ])
    );
}
