//! Theme name resolution: the one resolver of the terminal UI and the
//! HTML export. This module reads every file the sources reach (the
//! registered files: the resource system's themes, then `--theme` paths;
//! then the files of the custom directory, `<agent-dir>/themes`) and words
//! the warnings; the theme rules ([`ThemeRules`]) decide the theme a name
//! picks (by the JSON `name` a theme advertises: the registered files, the
//! builtins, then the custom files; a name no valid theme advertises is
//! the default theme with a warning; resolution never fails).

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};

use crate::palette::{Palette, ThemeFileError, BUILTIN_THEME_NAMES, DEFAULT_THEME_NAME};
use crate::rules::{Cause, Choice, Outcome, Picked, RawSource, RawTheme, ThemeRules};

/// Where theme names resolve. The composition root fills it from the
/// resource system; the default resolves the builtins only.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ThemeSources {
    /// Registered theme files and directories in precedence order: the
    /// first file advertising a name wins.
    pub registered: Vec<PathBuf>,
    /// `<agent-dir>/themes`: its `*.json` files resolve after the builtins.
    pub custom_dir: Option<PathBuf>,
    /// Failures resolving the registered paths, reported with the theme
    /// warnings.
    pub diagnostics: Vec<String>,
}

/// A resolved theme and the problems met on the way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedPalette {
    pub palette: Palette,
    /// One line per problem, the requested theme's failure first.
    pub warnings: Vec<String>,
}

/// Where a theme file came from: the registered paths or the custom
/// directory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Origin {
    Registered,
    Custom,
}

/// A theme file the sources reach, read and decoded.
struct Load {
    path: PathBuf,
    origin: Origin,
    /// Its theme object, or why it is none (naming the file).
    theme: Result<RawTheme, ThemeFileError>,
}

/// Every theme file the sources reach, in load order (the registered
/// files, then the custom directory's), and the unusable paths.
struct Catalog {
    loads: Vec<Load>,
    /// Unusable paths and directories.
    warnings: Vec<String>,
}

impl Catalog {
    /// What `name` resolves to over the files, by `rules`.
    fn pick(&self, name: &str, rules: ThemeRules) -> Picked {
        let sources: Vec<RawSource<'_>> = self
            .loads
            .iter()
            .map(|load| RawSource {
                custom: matches!(load.origin, Origin::Custom),
                stem: load.path.file_stem().and_then(std::ffi::OsStr::to_str),
                theme: load.theme.as_ref().ok(),
            })
            .collect();
        (rules.resolve)(name, &sources)
    }

    /// Why the file at `at` did not load, naming it: a warning's text.
    fn failure(&self, at: usize, outcomes: &[Outcome]) -> String {
        let load = &self.loads[at];
        match (&load.theme, outcomes.get(at)) {
            (Err(error), _) => error.to_string(),
            (Ok(_), Some(Outcome::Invalid(reason))) => {
                format!("Invalid theme {}: {reason}", load.path.display())
            }
            (Ok(_), Some(Outcome::Loaded | Outcome::NoTheme) | None) => {
                panic!("the rules name {} as failed", load.path.display())
            }
        }
    }

    fn name(&self, at: usize) -> &str {
        self.loads[at]
            .theme
            .as_ref()
            .map_or("", |theme| theme.name.as_str())
    }
}

impl ThemeSources {
    /// Resolve `name` (empty: the default theme) by `rules`. Every file is
    /// read again, so edited files and settings apply.
    ///
    /// # Panics
    ///
    /// Never: the rules name a builtin by its index, a cause or a broken
    /// file among the files that failed, and a clash among the files that
    /// loaded.
    #[must_use]
    pub fn resolve(&self, name: &str, rules: ThemeRules) -> ResolvedPalette {
        let mut catalog = self.catalog();
        let picked = catalog.pick(name, rules);
        let catalog_warnings = std::mem::take(&mut catalog.warnings);
        let mut warnings = Vec::new();
        if let Some(cause) = picked.cause {
            let reason = match cause {
                Cause::Failed(at) => catalog.failure(at, &picked.outcomes),
                Cause::NotFound => format!("Theme not found: {name}"),
            };
            warnings.push(format!(
                "Theme \"{name}\" unavailable, using \"{DEFAULT_THEME_NAME}\": {reason}"
            ));
        }
        warnings.extend(self.diagnostics.iter().cloned());
        warnings.extend(catalog_warnings);
        warnings.extend(picked.clashes.iter().map(|&(at, winner)| {
            format!(
                "Theme name \"{}\" collision: {} (using {})",
                catalog.name(at),
                catalog.loads[at].path.display(),
                catalog.loads[winner].path.display()
            )
        }));
        warnings.extend(
            picked
                .broken
                .iter()
                .map(|&at| catalog.failure(at, &picked.outcomes)),
        );
        let palette = match picked.theme {
            Choice::Builtin(at) => Palette::builtin(BUILTIN_THEME_NAMES[at], rules)
                .expect("the rules name a builtin by its index"),
            Choice::File(_, palette) => *palette,
        };
        ResolvedPalette { palette, warnings }
    }

    /// Every name that resolves to its own theme: the builtins and the
    /// valid files' names, sorted.
    #[must_use]
    pub fn available_names(&self, rules: ThemeRules) -> Vec<String> {
        let catalog = self.catalog();
        let picked = catalog.pick("", rules);
        let mut names: BTreeSet<String> = BUILTIN_THEME_NAMES
            .iter()
            .map(ToString::to_string)
            .collect();
        names.extend(
            picked
                .outcomes
                .iter()
                .zip(&catalog.loads)
                .filter(|(outcome, _)| matches!(outcome, Outcome::Loaded))
                .map(|(_, load)| {
                    load.theme
                        .as_ref()
                        .map_or("", |t| t.name.as_str())
                        .to_string()
                }),
        );
        names.into_iter().collect()
    }

    fn catalog(&self) -> Catalog {
        let (registered, mut warnings) = entries_into_parts(registered_entries(&self.registered));
        let (custom, custom_warnings) = self
            .custom_dir
            .as_deref()
            .map(custom_entries)
            .map(entries_into_parts)
            .unwrap_or_default();
        warnings.extend(custom_warnings);
        let (files, file_count) = truncate_files(dedupe(registered.into_iter().chain(custom)));
        if let Some(file_count) = file_count {
            warnings.push(format!(
                "{file_count} theme files found; only the first {MAX_THEME_FILES} are read"
            ));
        }
        let loads = files
            .into_iter()
            .map(|(path, origin)| Load {
                theme: read_theme(&path),
                path,
                origin,
            })
            .collect();
        Catalog { loads, warnings }
    }
}

/// The most theme files one load reads (registered first, then custom).
/// The theme rules number a file 3 + its index as a U32 and decode the
/// files one stack frame each, so a load stays far below both limits.
const MAX_THEME_FILES: usize = 4096;

/// The theme object of the file at `path`, or why it is none.
fn read_theme(path: &Path) -> Result<RawTheme, ThemeFileError> {
    let raw = std::fs::read_to_string(path).map_err(|source| ThemeFileError::Read {
        path: path.to_path_buf(),
        source,
    })?;
    RawTheme::decode(&raw).map_err(|source| ThemeFileError::Parse {
        path: path.to_path_buf(),
        source,
    })
}

/// What one source path gave: its theme files, each with its canonical key,
/// or a warning.
#[derive(Debug)]
enum Entry {
    Files(Vec<(PathBuf, PathBuf, Origin)>),
    Warning(String),
}

/// Canonical paths are computed beside filesystem reads; an unresolved path
/// identifies itself so its read error can still be reported.
fn keyed_files(files: Vec<PathBuf>, origin: Origin) -> Entry {
    Entry::Files(
        files
            .into_iter()
            .map(|path| {
                let key = std::fs::canonicalize(&path).unwrap_or_else(|_| path.clone());
                (path, key, origin)
            })
            .collect(),
    )
}

/// Separate IO results from paths and warnings without sharing mutable state.
fn entries_into_parts(entries: Vec<Entry>) -> (Vec<(PathBuf, PathBuf, Origin)>, Vec<String>) {
    entries.into_iter().fold(
        (Vec::new(), Vec::new()),
        |(mut files, mut warnings), entry| {
            match entry {
                Entry::Files(found) => files.extend(found),
                Entry::Warning(warning) => warnings.push(warning),
            }
            (files, warnings)
        },
    )
}

/// Keep first paths in order, comparing their precomputed canonical keys.
fn dedupe(files: impl IntoIterator<Item = (PathBuf, PathBuf, Origin)>) -> Vec<(PathBuf, Origin)> {
    let mut seen = HashSet::new();
    files
        .into_iter()
        .filter_map(|(path, key, origin)| seen.insert(key).then_some((path, origin)))
        .collect()
}

/// Limit a source list after counting it, retaining its first paths.
fn truncate_files(mut files: Vec<(PathBuf, Origin)>) -> (Vec<(PathBuf, Origin)>, Option<usize>) {
    let count = files.len();
    let truncated = (count > MAX_THEME_FILES).then_some(count);
    if truncated.is_some() {
        files.truncate(MAX_THEME_FILES);
    }
    (files, truncated)
}

/// Read registered paths and expand directories in registration order.
fn registered_entries(registered: &[PathBuf]) -> Vec<Entry> {
    registered
        .iter()
        .map(|path| match std::fs::metadata(path) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                Entry::Warning(format!("Theme path does not exist: {}", path.display()))
            }
            Err(error) => Entry::Warning(format!(
                "Failed to read theme path {}: {error}",
                path.display()
            )),
            Ok(metadata) if metadata.is_dir() => match theme_files_in(path) {
                Ok(files) => keyed_files(files, Origin::Registered),
                Err(error) => Entry::Warning(format!(
                    "Failed to read theme directory {}: {error}",
                    path.display()
                )),
            },
            Ok(_) if is_json_file_name(path) => keyed_files(vec![path.clone()], Origin::Registered),
            Ok(_) => Entry::Warning(format!("Theme path is not a JSON file: {}", path.display())),
        })
        .collect()
}

/// Read the custom directory after registered paths.
fn custom_entries(dir: &Path) -> Vec<Entry> {
    match theme_files_in(dir) {
        Ok(files) => vec![keyed_files(files, Origin::Custom)],
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Vec::new(),
        Err(error) => vec![Entry::Warning(format!(
            "Failed to read theme directory {}: {error}",
            dir.display()
        ))],
    }
}

fn is_json_file_name(path: &Path) -> bool {
    path.extension()
        .is_some_and(|extension| extension == "json")
}

/// A directory's `*.json` entries (symlinks followed), sorted by path.
fn theme_files_in(dir: &Path) -> std::io::Result<Vec<PathBuf>> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<std::io::Result<Vec<_>>>()?
        .into_iter()
        .filter(|path| is_json_file_name(path) && !path.is_dir())
        .collect();
    files.sort();
    Ok(files)
}

#[cfg(test)]
mod tests {

    use std::path::PathBuf;

    use super::theme_files_in;

    #[test]
    fn theme_files_skip_directories_and_non_json_entries() {
        let root = std::env::temp_dir().join(format!(
            "eukhe-theme-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system clock after epoch")
                .as_nanos()
        ));
        let nested = root.join("nested.json");
        std::fs::create_dir_all(&nested).expect("create temporary theme directory");
        std::fs::write(root.join("theme.json"), "{}").expect("create theme file");
        std::fs::write(root.join("notes.txt"), "ignored").expect("create non-theme file");

        assert_eq!(
            theme_files_in(&root).expect("read theme directory"),
            vec![root.join("theme.json")]
        );

        std::fs::remove_dir_all(root).expect("remove temporary directory");
    }
    #[cfg(unix)]
    #[test]
    fn dedupe_keeps_first_registered_path_over_directory_and_custom_symlink() {
        use std::os::unix::fs::symlink;

        use super::{custom_entries, dedupe, entries_into_parts, registered_entries, Origin};

        let root = std::env::temp_dir().join(format!(
            "eukhe-theme-dedupe-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system clock after epoch")
                .as_nanos()
        ));
        let registered_dir = root.join("registered");
        let custom_dir = root.join("custom");
        std::fs::create_dir_all(&registered_dir).expect("create registered themes");
        std::fs::create_dir_all(&custom_dir).expect("create custom themes");
        let theme = registered_dir.join("theme.json");
        std::fs::write(&theme, "{}").expect("create theme file");
        symlink(&theme, custom_dir.join("alias.json")).expect("create custom symlink");

        let (registered, _) =
            entries_into_parts(registered_entries(&[theme.clone(), registered_dir]));
        let (custom, _) = entries_into_parts(custom_entries(&custom_dir));
        let files = dedupe(registered.into_iter().chain(custom));

        assert_eq!(files, vec![(theme, Origin::Registered)]);
        std::fs::remove_dir_all(root).expect("remove temporary directory");
    }
    #[test]
    fn resolve_warnings_keep_the_documented_order_and_text() {
        use super::ThemeSources;
        use crate::{
            Cause, Choice, ColorValue, Mode, Outcome, Palette, PaletteParts, Picked, RawSource,
            Rgb, ThemeLoadError, ThemeRules, Token,
        };

        fn palette() -> Palette {
            Palette::new(PaletteParts {
                name: "test".into(),
                colors: [ColorValue::Default; Token::ALL.len()],
                paints: [Rgb::new(0, 0, 0); Token::ALL.len()],
                declared_background: None,
                export: [None; 3],
                mode: Mode::Dark,
            })
        }

        fn resolve(_: &str, sources: &[RawSource<'_>]) -> Picked {
            Picked {
                theme: Choice::Builtin(0),
                cause: Some(Cause::NotFound),
                clashes: vec![(1, 0)],
                broken: vec![2],
                outcomes: sources
                    .iter()
                    .enumerate()
                    .map(|(at, _)| match at {
                        2 => Outcome::Invalid(ThemeLoadError {
                            reason: "broken".into(),
                        }),
                        0 | 1 => Outcome::Loaded,
                        _ => Outcome::NoTheme,
                    })
                    .collect(),
            }
        }

        let root = std::env::temp_dir().join(format!(
            "eukhe-theme-warnings-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system clock after epoch")
                .as_nanos()
        ));
        std::fs::create_dir_all(&root).expect("create temporary theme directory");
        let first = root.join("first.json");
        let second = root.join("second.json");
        let invalid = root.join("invalid.json");
        let missing = root.join("missing.json");
        std::fs::write(&first, r#"{"name":"first","colors":{}}"#).expect("create first theme");
        std::fs::write(&second, r#"{"name":"second","colors":{}}"#).expect("create second theme");
        std::fs::write(&invalid, r#"{"name":"invalid","colors":{}}"#)
            .expect("create invalid theme");
        let sources = ThemeSources {
            registered: vec![
                first.clone(),
                second.clone(),
                invalid.clone(),
                missing.clone(),
            ],
            diagnostics: vec!["registered diagnostic".into()],
            ..ThemeSources::default()
        };

        let rules = ThemeRules {
            load: |_| Ok(palette()),
            resolve,
        };
        let result = sources.resolve("ghost", rules);

        assert_eq!(
            result.warnings,
            vec![
                "Theme \"ghost\" unavailable, using \"forge\": Theme not found: ghost".into(),
                "registered diagnostic".into(),
                format!("Theme path does not exist: {}", missing.display()),
                format!(
                    "Theme name \"second\" collision: {} (using {})",
                    second.display(),
                    first.display()
                ),
                format!("Invalid theme {}: broken", invalid.display()),
            ]
        );
        std::fs::remove_dir_all(root).expect("remove temporary directory");
    }
    #[test]
    fn truncation_counts_all_files_and_keeps_the_first_in_order() {
        use super::{truncate_files, Origin, MAX_THEME_FILES};

        let files: Vec<_> = (0..=MAX_THEME_FILES)
            .map(|index| (PathBuf::from(format!("{index}.json")), Origin::Registered))
            .collect();
        let (truncated, count) = truncate_files(files.clone());

        assert_eq!(count, Some(MAX_THEME_FILES + 1));
        assert_eq!(truncated, files[..MAX_THEME_FILES]);
    }
}
