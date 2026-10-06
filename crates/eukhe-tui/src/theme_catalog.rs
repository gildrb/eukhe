//! Theme name resolution (TS `loadTheme`): the registered theme files by
//! their JSON `name` (TS `setRegisteredThemes` from the resource loader),
//! then the builtins, then `<custom-dir>/<name>.json` (TS
//! `getCustomThemesDir`). A missing or invalid theme resolves to the
//! default builtin with a warning, and every registered file that fails to
//! load warns too (TS's startup theme diagnostics).

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};

use crate::client_settings::ClientSettings;
use crate::theme::{detect_color_mode, load_theme_from_path, read_theme_json, ColorMode, Theme};

/// The theme an empty name and every failed lookup resolve to.
pub const DEFAULT_THEME_NAME: &str = "eukhe";

/// Where theme names resolve. The composition root fills it from the
/// resource system; the default resolves the builtins only.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ThemeSources {
    /// Registered theme files and directories in precedence order (the
    /// resource system's themes, then `--theme` paths): the first file
    /// advertising a name wins.
    pub registered: Vec<PathBuf>,
    /// `<agent-dir>/themes`: a name that is neither registered nor a
    /// builtin loads `<name>.json` from here.
    pub custom_dir: Option<PathBuf>,
    /// Failures resolving the registered paths, reported with the theme
    /// warnings.
    pub diagnostics: Vec<String>,
}

/// A resolved theme and the problems met on the way.
#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedTheme {
    pub theme: Theme,
    /// One line per problem, the requested theme's failure first.
    pub warnings: Vec<String>,
}

impl ThemeSources {
    /// Resolve `name` (empty: the default theme); every registered file
    /// is read again, so edited files and settings apply.
    #[must_use]
    pub fn resolve(&self, name: &str, mode: ColorMode) -> ResolvedTheme {
        let mut registry_warnings = Vec::new();
        let mut loaded: Vec<(PathBuf, Theme)> = Vec::new();
        let mut failures: Vec<(PathBuf, String)> = Vec::new();
        for path in self.registered_files(&mut registry_warnings) {
            match load_theme_from_path(&path, mode) {
                Ok(theme) => {
                    // TS `dedupeThemes`: the first file with a name wins.
                    if let Some((winner, _)) = loaded
                        .iter()
                        .find(|(_, existing)| existing.name == theme.name)
                    {
                        registry_warnings.push(format!(
                            "Theme name \"{}\" collision: {} (using {})",
                            theme.name,
                            path.display(),
                            winner.display()
                        ));
                    } else {
                        loaded.push((path, theme));
                    }
                }
                Err(error) => failures.push((path, format!("{error:#}"))),
            }
        }
        let mut warnings = Vec::new();
        let theme = match self.lookup(name, mode, &loaded, &mut failures) {
            Ok(theme) => theme,
            Err(reason) => {
                warnings.push(format!(
                    "Theme \"{name}\" unavailable, using \"{DEFAULT_THEME_NAME}\": {reason}"
                ));
                Theme::builtin(DEFAULT_THEME_NAME, mode)
            }
        };
        warnings.extend(self.diagnostics.iter().cloned());
        warnings.extend(registry_warnings);
        warnings.extend(failures.into_iter().map(|(_, error)| error));
        ResolvedTheme { theme, warnings }
    }

    /// TS `loadTheme`: registered, builtin, then the custom directory. A
    /// registered `<name>.json` that failed to load is the theme's own
    /// failure (TS falls through to the same file and fails the same way).
    fn lookup(
        &self,
        name: &str,
        mode: ColorMode,
        loaded: &[(PathBuf, Theme)],
        failures: &mut Vec<(PathBuf, String)>,
    ) -> Result<Theme, String> {
        if name.is_empty() {
            return Ok(Theme::builtin(DEFAULT_THEME_NAME, mode));
        }
        if let Some((_, theme)) = loaded.iter().find(|(_, theme)| theme.name == name) {
            return Ok(theme.clone());
        }
        if eukhe_types::themes::builtin_theme_json(name).is_some() {
            return Ok(Theme::builtin(name, mode));
        }
        if let Some(index) = failures
            .iter()
            .position(|(path, _)| path.file_stem().is_some_and(|stem| stem == name))
        {
            return Err(failures.remove(index).1);
        }
        let Some(dir) = &self.custom_dir else {
            return Err(format!("Theme not found: {name}"));
        };
        let path = dir.join(format!("{name}.json"));
        if !path.exists() {
            return Err(format!(
                "Theme not found: {name} (not registered, not a builtin, no {})",
                path.display()
            ));
        }
        load_theme_from_path(&path, mode).map_err(|error| format!("{error:#}"))
    }

    /// The registered theme files: directories expand to their `*.json`
    /// entries, duplicates drop, and unusable paths warn (TS
    /// `loadThemes`).
    fn registered_files(&self, warnings: &mut Vec<String>) -> Vec<PathBuf> {
        let mut files = Vec::new();
        let mut seen: HashSet<PathBuf> = HashSet::new();
        let mut push = |path: PathBuf, files: &mut Vec<PathBuf>| {
            // Identity only: an uncanonicalizable path keys on itself and
            // its load reports the real error.
            let key = std::fs::canonicalize(&path).unwrap_or_else(|_| path.clone());
            if seen.insert(key) {
                files.push(path);
            }
        };
        for path in &self.registered {
            match std::fs::metadata(path) {
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    warnings.push(format!("Theme path does not exist: {}", path.display()));
                }
                Err(error) => {
                    warnings.push(format!(
                        "Failed to read theme path {}: {error}",
                        path.display()
                    ));
                }
                Ok(metadata) => {
                    if metadata.is_dir() {
                        match theme_files_in(path) {
                            Ok(found) => {
                                for file in found {
                                    push(file, &mut files);
                                }
                            }
                            Err(error) => warnings.push(format!(
                                "Failed to read theme directory {}: {error}",
                                path.display()
                            )),
                        }
                    } else if is_json_file_name(path) {
                        push(path.clone(), &mut files);
                    } else {
                        warnings.push(format!("Theme path is not a JSON file: {}", path.display()));
                    }
                }
            }
        }
        files
    }

    /// TS `getAvailableThemes`: the builtins, the custom directory's
    /// `*.json` names, and the registered themes' names, sorted. Files
    /// that fail to read are left out here; [`Self::resolve`] reports them.
    #[must_use]
    pub fn available_names(&self) -> Vec<String> {
        let mut names: BTreeSet<String> = eukhe_types::themes::BUILTIN_THEME_NAMES
            .iter()
            .map(ToString::to_string)
            .collect();
        if let Some(Ok(files)) = self.custom_dir.as_deref().map(theme_files_in) {
            names.extend(
                files
                    .iter()
                    .filter_map(|file| file.file_stem()?.to_str().map(str::to_string)),
            );
        }
        let mut ignored = Vec::new();
        for path in self.registered_files(&mut ignored) {
            if let Ok(json) = read_theme_json(&path) {
                names.insert(json.name().to_string());
            }
        }
        names.into_iter().collect()
    }
}

fn is_json_file_name(path: &Path) -> bool {
    path.extension()
        .is_some_and(|extension| extension == "json")
}

/// A directory's `*.json` entries (symlinks followed), sorted by path.
fn theme_files_in(dir: &Path) -> std::io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        if is_json_file_name(&path) && !path.is_dir() {
            files.push(path);
        }
    }
    files.sort();
    Ok(files)
}

/// The theme a client surface mounts: resolved through the settings
/// seam's sources (its warnings also go to the agent log), or through the
/// builtins alone when the surface runs without a seam.
#[must_use]
pub fn load_client_theme(settings: Option<&dyn ClientSettings>, name: &str) -> ResolvedTheme {
    let mode = detect_color_mode();
    let Some(settings) = settings else {
        return ThemeSources::default().resolve(name, mode);
    };
    let resolved = settings.theme_sources().resolve(name, mode);
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

    const DUSK_APPLE: &str = include_str!("../tests/fixtures/dusk-apple-theme.json");
    const MODE: ColorMode = ColorMode::TrueColor;

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

    /// The omp/pi theme file (`$schema`, vars, an `export` section) loads
    /// by name from the agent dir with its var-resolved colors.
    #[test]
    fn a_custom_theme_resolves_by_name_from_the_custom_dir() {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("dusk-apple.json");
        write(&path, DUSK_APPLE);
        let resolved = custom_dir_sources(dir.path()).resolve("dusk-apple", MODE);
        assert_eq!(
            resolved,
            ResolvedTheme {
                theme: load_theme_from_path(&path, MODE).expect("dusk-apple loads"),
                warnings: Vec::new(),
            }
        );
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

    #[test]
    fn an_invalid_theme_warns_and_falls_back_to_the_default() {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("broken.json");
        write(
            &path,
            &DUSK_APPLE.replacen("\"accent\": \"accent\"", "\"accent\": \"nope\"", 1),
        );
        let resolved = custom_dir_sources(dir.path()).resolve("broken", MODE);
        assert_eq!(
            resolved,
            ResolvedTheme {
                theme: Theme::builtin(DEFAULT_THEME_NAME, MODE),
                warnings: vec![format!(
                    "Theme \"broken\" unavailable, using \"eukhe\": Invalid theme {}: color \
                     \"accent\": Variable reference not found: nope",
                    path.display()
                )],
            }
        );
    }

    #[test]
    fn a_missing_theme_warns_and_falls_back_to_the_default() {
        let dir = tempfile::tempdir().expect("temp dir");
        let resolved = custom_dir_sources(dir.path()).resolve("dusk-apple", MODE);
        assert_eq!(
            resolved,
            ResolvedTheme {
                theme: Theme::builtin(DEFAULT_THEME_NAME, MODE),
                warnings: vec![format!(
                    "Theme \"dusk-apple\" unavailable, using \"eukhe\": Theme not found: \
                     dusk-apple (not registered, not a builtin, no {})",
                    dir.path().join("dusk-apple.json").display()
                )],
            }
        );
    }

    /// A registered file (`--theme <path>`) resolves by its JSON name, not
    /// its file name; a registered file that fails to parse warns even
    /// when another theme is requested.
    #[test]
    fn registered_files_resolve_by_their_json_name() {
        let dir = tempfile::tempdir().expect("temp dir");
        let renamed = dir.path().join("cli-theme.json");
        write(&renamed, DUSK_APPLE);
        let malformed = dir.path().join("extra").join("malformed.json");
        write(&malformed, "{ not json");
        let sources = ThemeSources {
            registered: vec![
                renamed.clone(),
                malformed.parent().expect("dir").to_path_buf(),
            ],
            ..ThemeSources::default()
        };
        let resolved = sources.resolve("dusk-apple", MODE);
        assert_eq!(
            resolved,
            ResolvedTheme {
                theme: load_theme_from_path(&renamed, MODE).expect("theme loads"),
                warnings: vec![format!(
                    "Failed to parse theme {}: key must be a string at line 1 column 3",
                    malformed.display()
                )],
            }
        );
        assert_eq!(
            sources.available_names(),
            ["dark", "dusk-apple", "eukhe", "light"]
        );
    }

    /// Without the registration (`--no-themes` drops the resource
    /// themes), a theme only a registered path provides is not found.
    #[test]
    fn an_unregistered_theme_outside_the_custom_dir_is_not_found() {
        let resolved = ThemeSources::default().resolve("dusk-apple", MODE);
        assert_eq!(
            resolved,
            ResolvedTheme {
                theme: Theme::builtin(DEFAULT_THEME_NAME, MODE),
                warnings: vec![
                    "Theme \"dusk-apple\" unavailable, using \"eukhe\": Theme not found: \
                     dusk-apple"
                        .to_string()
                ],
            }
        );
    }

    #[test]
    fn a_missing_registered_path_warns() {
        let dir = tempfile::tempdir().expect("temp dir");
        let missing = dir.path().join("gone.json");
        let resolved = ThemeSources {
            registered: vec![missing.clone()],
            ..ThemeSources::default()
        }
        .resolve("dark", MODE);
        assert_eq!(
            resolved,
            ResolvedTheme {
                theme: Theme::builtin("dark", MODE),
                warnings: vec![format!("Theme path does not exist: {}", missing.display())],
            }
        );
    }
}
