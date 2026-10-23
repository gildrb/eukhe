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

/// A theme file the sources reach, loaded.
struct Load {
    path: PathBuf,
    /// From the custom directory (else registered).
    custom: bool,
    outcome: Result<Palette, LoadFailure>,
}

impl Load {
    fn palette(&self) -> &Palette {
        self.outcome
            .as_ref()
            .expect("the pick names a file that loaded")
    }

    fn failure(&self) -> String {
        match &self.outcome {
            Err(failure) => failure.message.clone(),
            Ok(palette) => panic!("the pick names {} as failed", palette.name()),
        }
    }
}

/// Every theme file the sources reach, in load order (the registered
/// files, then the custom directory's), and the unusable paths.
struct Catalog {
    loads: Vec<Load>,
    /// Unusable paths and directories.
    warnings: Vec<String>,
}

/// A loaded file as the pick sees it (`bend/theme/choice.bend` `Ld`).
#[derive(Debug, Clone, PartialEq, Eq)]
enum Reached<'a> {
    /// A valid file, by the name it advertises.
    Fine { name: &'a str, custom: bool },
    /// A file that did not load: the name it advertises when it is a theme
    /// object, and its file stem when that is text.
    Broke {
        name: Option<&'a str>,
        stem: Option<&'a str>,
    },
}

/// The theme a name picks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Choice {
    /// The builtin at this index of [`BUILTIN_THEME_NAMES`] (0: the default
    /// theme, also for the empty name and a name that picks nothing).
    Builtin(usize),
    /// The loaded file at this index.
    File(usize),
}

/// Why a name picks no theme.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cause {
    /// The loaded file at this index did not load and blames the name.
    Failed(usize),
    NotFound,
}

/// What a name picks (`bend/theme/choice.bend` `pick`): the theme, the cause of
/// its warning (none when it does not warn), the clashes (a file and the
/// earlier file whose name it repeats) and the other files that did not
/// load, each in load order.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Pick {
    theme: Choice,
    cause: Option<Cause>,
    clashes: Vec<(usize, usize)>,
    broken: Vec<usize>,
}

/// The rule `bend/theme/choice.bend` `pick` states: a name resolves to the first
/// valid registered file, else the builtin, else the first valid custom
/// file advertising it; the empty name is the default theme; a name no
/// valid file advertises is the default theme with a warning whose cause
/// is the first failed file that advertises it (or, no theme object, is
/// named after it).
fn pick(reached: &[Reached<'_>], name: &str) -> Pick {
    let fine = |want_custom: bool| {
        reached
            .iter()
            .enumerate()
            .filter_map(move |(at, load)| match load {
                Reached::Fine { name, custom } if *custom == want_custom => Some((at, *name)),
                Reached::Fine { .. } | Reached::Broke { .. } => None,
            })
    };
    let theme = if name.is_empty() {
        Some(Choice::Builtin(0))
    } else {
        fine(false)
            .find(|(_, advertised)| *advertised == name)
            .map(|(at, _)| Choice::File(at))
            .or_else(|| {
                BUILTIN_THEME_NAMES
                    .iter()
                    .position(|builtin| *builtin == name)
                    .map(Choice::Builtin)
            })
            .or_else(|| {
                fine(true)
                    .find(|(_, advertised)| *advertised == name)
                    .map(|(at, _)| Choice::File(at))
            })
    };
    let cause = match theme {
        Some(_) => None,
        None => Some(
            reached
                .iter()
                .position(|load| match load {
                    Reached::Broke {
                        name: Some(advertised),
                        ..
                    } => *advertised == name,
                    Reached::Broke { name: None, stem } => *stem == Some(name),
                    Reached::Fine { .. } => false,
                })
                .map_or(Cause::NotFound, Cause::Failed),
        ),
    };
    let clashes = reached
        .iter()
        .enumerate()
        .filter_map(|(at, load)| match load {
            Reached::Fine { name, .. } => reached
                .iter()
                .position(|other| match other {
                    Reached::Fine { name: first, .. } => first == name,
                    Reached::Broke { .. } => false,
                })
                .filter(|winner| *winner != at)
                .map(|winner| (at, winner)),
            Reached::Broke { .. } => None,
        })
        .collect();
    let skip = match cause {
        Some(Cause::Failed(at)) => Some(at),
        Some(Cause::NotFound) | None => None,
    };
    let broken = reached
        .iter()
        .enumerate()
        .filter(|(at, load)| matches!(load, Reached::Broke { .. }) && Some(*at) != skip)
        .map(|(at, _)| at)
        .collect();
    Pick {
        theme: theme.unwrap_or(Choice::Builtin(0)),
        cause,
        clashes,
        broken,
    }
}

impl ThemeSources {
    /// Resolve `name` (empty: the default theme). Every file is read
    /// again, so edited files and settings apply.
    ///
    /// # Panics
    ///
    /// Never: the pick names a builtin by its index, a cause or a broken
    /// file among the files that failed, and a clash or a theme among the
    /// files that loaded.
    #[must_use]
    pub fn resolve(&self, name: &str) -> ResolvedPalette {
        let catalog = self.catalog();
        let reached: Vec<Reached<'_>> = catalog
            .loads
            .iter()
            .map(|load| match &load.outcome {
                Ok(palette) => Reached::Fine {
                    name: palette.name(),
                    custom: load.custom,
                },
                Err(failure) => Reached::Broke {
                    name: failure.name.as_deref(),
                    stem: load.path.file_stem().and_then(std::ffi::OsStr::to_str),
                },
            })
            .collect();
        let picked = pick(&reached, name);
        let mut warnings = Vec::new();
        if let Some(cause) = picked.cause {
            let reason = match cause {
                Cause::Failed(at) => catalog.loads[at].failure(),
                Cause::NotFound => format!("Theme not found: {name}"),
            };
            warnings.push(format!(
                "Theme \"{name}\" unavailable, using \"{DEFAULT_THEME_NAME}\": {reason}"
            ));
        }
        warnings.extend(self.diagnostics.iter().cloned());
        warnings.extend(catalog.warnings);
        // A clash (the model's: a name an earlier valid file took) warns
        // only when its colors differ: the same theme twice (a config
        // mirrored into a project, a copy) loses silently.
        warnings.extend(
            picked
                .clashes
                .iter()
                .filter(|&&(at, winner)| {
                    catalog.loads[at].palette() != catalog.loads[winner].palette()
                })
                .map(|&(at, winner)| {
                    let clash = &catalog.loads[at];
                    format!(
                        "Theme name \"{}\" collision: {} (using {})",
                        clash.palette().name(),
                        clash.path.display(),
                        catalog.loads[winner].path.display()
                    )
                }),
        );
        warnings.extend(picked.broken.iter().map(|&at| catalog.loads[at].failure()));
        let palette = match picked.theme {
            Choice::Builtin(at) => Palette::builtin(BUILTIN_THEME_NAMES[at])
                .expect("the pick names a builtin by its index"),
            Choice::File(at) => catalog.loads[at].palette().clone(),
        };
        ResolvedPalette { palette, warnings }
    }

    /// Every name that resolves to its own theme: the builtins and the
    /// valid files' names, sorted.
    #[must_use]
    pub fn available_names(&self) -> Vec<String> {
        let mut names: BTreeSet<String> = BUILTIN_THEME_NAMES
            .iter()
            .map(ToString::to_string)
            .collect();
        names.extend(
            self.catalog()
                .loads
                .iter()
                .filter_map(|load| load.outcome.as_ref().ok())
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
        let loads = registered_files
            .into_iter()
            .map(|path| (path, false))
            .chain(custom_files.into_iter().map(|path| (path, true)))
            .map(|(path, custom)| Load {
                outcome: Palette::load(&path),
                path,
                custom,
            })
            .collect();
        Catalog { loads, warnings }
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
