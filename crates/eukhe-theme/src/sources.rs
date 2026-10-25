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

use crate::palette::{LoadFailure, Palette, BUILTIN_THEME_NAMES, DEFAULT_THEME_NAME};
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

/// A theme file the sources reach, read and decoded.
struct Load {
    path: PathBuf,
    /// From the custom directory (else registered).
    custom: bool,
    /// Its theme object, or why it is none (naming the file).
    theme: Result<RawTheme, String>,
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
                custom: load.custom,
                stem: load.path.file_stem().and_then(std::ffi::OsStr::to_str),
                theme: load.theme.as_ref().ok(),
            })
            .collect();
        (rules.resolve)(name, &sources)
    }

    /// Why the file at `at` did not load, naming it.
    fn failure(&self, at: usize, outcomes: &[Outcome]) -> String {
        let load = &self.loads[at];
        match (&load.theme, outcomes.get(at)) {
            (Err(message), _) => message.clone(),
            (Ok(theme), Some(Outcome::Invalid(reason))) => {
                LoadFailure::invalid(&load.path, &theme.name, reason).message
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
        let catalog = self.catalog();
        let picked = catalog.pick(name, rules);
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
        warnings.extend(catalog.warnings.iter().cloned());
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
        let mut warnings = Vec::new();
        let mut seen: HashSet<PathBuf> = HashSet::new();
        let registered_files = registered_files(&self.registered, &mut seen, &mut warnings);
        let custom_files = match &self.custom_dir {
            Some(dir) => match theme_files_in(dir) {
                Ok(files) => unique(files, &mut seen),
                // No custom directory: nothing to load.
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => Vec::new(),
                Err(error) => {
                    warnings.push(format!(
                        "Failed to read theme directory {}: {error}",
                        dir.display()
                    ));
                    Vec::new()
                }
            },
            None => Vec::new(),
        };
        let mut files: Vec<(PathBuf, bool)> = registered_files
            .into_iter()
            .map(|path| (path, false))
            .chain(custom_files.into_iter().map(|path| (path, true)))
            .collect();
        if files.len() > MAX_THEME_FILES {
            warnings.push(format!(
                "{} theme files found; only the first {MAX_THEME_FILES} are read",
                files.len()
            ));
            files.truncate(MAX_THEME_FILES);
        }
        let loads = files
            .into_iter()
            .map(|(path, custom)| Load {
                theme: read_theme(&path),
                path,
                custom,
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
fn read_theme(path: &Path) -> Result<RawTheme, String> {
    let raw = std::fs::read_to_string(path)
        .map_err(|error| format!("Failed to read theme {}: {error}", path.display()))?;
    RawTheme::decode(&raw)
        .map_err(|reason| format!("Failed to parse theme {}: {reason}", path.display()))
}

/// The paths `files` that `seen` does not hold yet (by canonical path).
fn unique(files: Vec<PathBuf>, seen: &mut HashSet<PathBuf>) -> Vec<PathBuf> {
    files
        .into_iter()
        .filter(|path| {
            // Identity only: an uncanonicalizable path keys on itself and
            // its load reports the real error.
            seen.insert(std::fs::canonicalize(path).unwrap_or_else(|_| path.clone()))
        })
        .collect()
}

/// The registered theme files: directories expand to their `*.json`
/// entries, duplicates drop, and unusable paths warn.
fn registered_files(
    registered: &[PathBuf],
    seen: &mut HashSet<PathBuf>,
    warnings: &mut Vec<String>,
) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for path in registered {
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
            Ok(metadata) if metadata.is_dir() => match theme_files_in(path) {
                Ok(found) => files.extend(unique(found, seen)),
                Err(error) => warnings.push(format!(
                    "Failed to read theme directory {}: {error}",
                    path.display()
                )),
            },
            Ok(_) if is_json_file_name(path) => files.extend(unique(vec![path.clone()], seen)),
            Ok(_) => {
                warnings.push(format!("Theme path is not a JSON file: {}", path.display()));
            }
        }
    }
    files
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
