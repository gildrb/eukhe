//! Theme name resolution: the one resolver of the terminal UI and the
//! HTML export. A name resolves by the JSON `name` the theme advertises,
//! in this order: the registered files (the resource system's themes, then
//! `--theme` paths), the builtins, then the files of the custom directory
//! (`<agent-dir>/themes`). A name no valid theme advertises resolves to the
//! default theme with a warning; resolution never fails.

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};

use crate::palette::{LoadFailure, Palette, BUILTIN_THEME_NAMES, DEFAULT_THEME_NAME};

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

/// Every theme file the sources reach, loaded.
struct Catalog {
    /// Valid registered files, the first per name.
    registered: Vec<Palette>,
    /// Valid custom-directory files, the first per name.
    custom: Vec<Palette>,
    /// Files that did not load, with their paths.
    failures: Vec<(PathBuf, LoadFailure)>,
    /// Unusable paths and name collisions.
    warnings: Vec<String>,
}

impl ThemeSources {
    /// Resolve `name` (empty: the default theme). Every file is read
    /// again, so edited files and settings apply.
    #[must_use]
    pub fn resolve(&self, name: &str) -> ResolvedPalette {
        let mut catalog = self.catalog();
        let mut warnings = Vec::new();
        let palette = if name.is_empty() {
            Palette::default_theme()
        } else if let Some(found) = catalog
            .registered
            .iter()
            .find(|palette| palette.name() == name)
        {
            found.clone()
        } else if let Some(builtin) = Palette::builtin(name) {
            builtin
        } else if let Some(found) = catalog.custom.iter().find(|palette| palette.name() == name) {
            found.clone()
        } else {
            // The reason: a failed file advertising the name (or, when it is
            // not a theme object, named `<name>.json`), else not found.
            let reason = catalog
                .failures
                .iter()
                .position(|(path, failure)| match &failure.name {
                    Some(advertised) => advertised == name,
                    None => path.file_stem().is_some_and(|stem| stem == name),
                })
                .map_or_else(
                    || format!("Theme not found: {name}"),
                    |at| catalog.failures.remove(at).1.message,
                );
            warnings.push(format!(
                "Theme \"{name}\" unavailable, using \"{DEFAULT_THEME_NAME}\": {reason}"
            ));
            Palette::default_theme()
        };
        warnings.extend(self.diagnostics.iter().cloned());
        warnings.extend(catalog.warnings);
        warnings.extend(
            catalog
                .failures
                .into_iter()
                .map(|(_, failure)| failure.message),
        );
        ResolvedPalette { palette, warnings }
    }

    /// Every name that resolves to its own theme: the builtins and the
    /// valid files' names, sorted.
    #[must_use]
    pub fn available_names(&self) -> Vec<String> {
        let catalog = self.catalog();
        let mut names: BTreeSet<String> = BUILTIN_THEME_NAMES
            .iter()
            .map(ToString::to_string)
            .collect();
        names.extend(
            catalog
                .registered
                .iter()
                .chain(&catalog.custom)
                .map(|palette| palette.name().to_string()),
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
        let mut catalog = Catalog {
            registered: Vec::new(),
            custom: Vec::new(),
            failures: Vec::new(),
            warnings,
        };
        let mut winners: Vec<(String, PathBuf)> = Vec::new();
        for (path, custom) in registered_files
            .into_iter()
            .map(|path| (path, false))
            .chain(custom_files.into_iter().map(|path| (path, true)))
        {
            match Palette::load(&path) {
                Ok(palette) => {
                    if let Some((_, winner)) =
                        winners.iter().find(|(name, _)| name == palette.name())
                    {
                        catalog.warnings.push(format!(
                            "Theme name \"{}\" collision: {} (using {})",
                            palette.name(),
                            path.display(),
                            winner.display()
                        ));
                        continue;
                    }
                    winners.push((palette.name().to_string(), path));
                    if custom {
                        catalog.custom.push(palette);
                    } else {
                        catalog.registered.push(palette);
                    }
                }
                Err(failure) => catalog.failures.push((path, failure)),
            }
        }
        catalog
    }
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

#[cfg(test)]
mod tests;
