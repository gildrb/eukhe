use super::*;

const DUSK_APPLE: &str = include_str!("../../tests/fixtures/dusk-apple-theme.json");

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

fn default_with(warnings: Vec<String>) -> ResolvedPalette {
    ResolvedPalette {
        palette: Palette::default_theme(),
        warnings,
    }
}

/// A custom-directory file resolves by the name it advertises, not by its
/// file name.
#[test]
fn a_custom_theme_resolves_by_its_json_name() {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("renamed.json");
    write(&path, DUSK_APPLE);
    assert_eq!(
        custom_dir_sources(dir.path()).resolve("dusk-apple"),
        ResolvedPalette {
            palette: Palette::parse(DUSK_APPLE).expect("dusk-apple is valid"),
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
        custom_dir_sources(dir.path()).resolve("dusk-apple"),
        default_with(vec![format!(
            "Theme \"dusk-apple\" unavailable, using \"eukhe\": Invalid theme {}: color \
             \"accent\": Variable reference not found: nope",
            path.display()
        )])
    );
}

#[test]
fn a_missing_theme_warns_and_falls_back_to_the_default() {
    let dir = tempfile::tempdir().expect("temp dir");
    assert_eq!(
        custom_dir_sources(dir.path()).resolve("dusk-apple"),
        default_with(vec![
            "Theme \"dusk-apple\" unavailable, using \"eukhe\": Theme not found: dusk-apple"
                .to_string()
        ])
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
        [sources.resolve("dusk-apple"), sources.resolve("")],
        [
            ResolvedPalette {
                palette: Palette::parse(DUSK_APPLE).expect("theme loads"),
                warnings: vec![malformed_warning.clone()],
            },
            default_with(vec![malformed_warning]),
        ]
    );
    assert_eq!(
        sources.available_names(),
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
    let dark = Palette::builtin("dark").expect("dark");
    let registered_dark = DUSK_APPLE.replacen("\"name\": \"dusk-apple\"", "\"name\": \"dark\"", 1);
    write(&first, &registered_dark);
    write(&second, &registered_dark.replacen("#c4a77d", "#c4a77e", 1));
    write(&same, &registered_dark);
    let resolved = ThemeSources {
        registered: vec![first.clone(), second.clone(), same],
        ..ThemeSources::default()
    }
    .resolve("dark");
    assert_ne!(resolved.palette, dark);
    assert_eq!(
        resolved,
        ResolvedPalette {
            palette: Palette::parse(&registered_dark).expect("valid"),
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
        .resolve("dark"),
        ResolvedPalette {
            palette: Palette::builtin("dark").expect("dark"),
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
    let resolved = custom_dir_sources(&themes).resolve("../escaped");
    assert_eq!(
        resolved,
        default_with(vec![
            "Theme \"../escaped\" unavailable, using \"eukhe\": Theme not found: ../escaped"
                .to_string()
        ])
    );
}
