//! The `resolve()` methods on the package manager: configured-source
//! resolution against what is installed (missing npm and git sources are
//! reported, never installed or fetched), settings top-level arrays, and
//! package resource collection (manifest, convention directories, and
//! filter patterns).

use std::path::{Path, PathBuf};

use anyhow::Result;

use super::super::source::{parse_source, NpmSource, ParsedSource, SourceScope, UserOrProject};
use super::super::PackageManager;
use super::super::{git, npm};
use std::collections::HashMap;

use super::discovery::collect_resource_files;
use super::patterns::{apply_patterns, split_patterns};
use super::{
    settings_array, to_resolved_paths, top_level_metadata, ConfiguredSource, MetadataSource,
    MissingPackage, PackageFilter, PathMetadata, ResolvedPaths, ResourceAccumulator,
    ResourceOrigin, ResourceType, RESOURCE_TYPES,
};
use crate::skills::diagnostics::ResourceDiagnostic;

/// Parse the object (filter) form of a `packages` settings entry.
fn parse_package_filter(entry: &serde_json::Value) -> Option<PackageFilter> {
    let object = entry.as_object()?;
    let strings = |value: Option<&serde_json::Value>| -> Option<Vec<String>> {
        match value {
            Some(serde_json::Value::Array(entries)) => Some(
                entries
                    .iter()
                    .filter_map(serde_json::Value::as_str)
                    .map(str::to_string)
                    .collect(),
            ),
            _ => None,
        }
    };
    Some(PackageFilter {
        skills: strings(object.get("skills")),
        prompts: strings(object.get("prompts")),
        themes: strings(object.get("themes")),
    })
}

/// Dedupe configured sources by package identity (npm name, git host/path,
/// or scope-resolved local path); a project entry replaces an equal user
/// entry (project wins).
fn dedupe_configured_sources(
    manager: &PackageManager,
    all_packages: Vec<(serde_json::Value, UserOrProject)>,
) -> Vec<ConfiguredSource> {
    let mut seen: HashMap<String, usize> = HashMap::new();
    let mut deduped: Vec<ConfiguredSource> = Vec::new();
    for (entry, scope) in all_packages {
        let (source, is_object) = super::super::manager::split_entry(&entry);
        let filter = is_object.then(|| parse_package_filter(&entry)).flatten();
        let identity = match parse_source(&source) {
            Ok(ParsedSource::Npm(npm_source)) => format!("npm:{}", npm_source.name),
            Ok(ParsedSource::Git(git_source)) => {
                format!("git:{}/{}", git_source.host, git_source.path)
            }
            Ok(ParsedSource::Local(local)) => {
                let base_dir = manager.base_dir_for_scope(scope.into());
                let resolved = PackageManager::resolve_path_from_base(&local.path, &base_dir);
                format!("local:{}", resolved.display())
            }
            Err(error) => format!("invalid:{}", error.input),
        };
        match seen.get(&identity) {
            None => {
                seen.insert(identity, deduped.len());
                deduped.push(ConfiguredSource {
                    source,
                    scope,
                    filter,
                });
            }
            Some(existing_index) => {
                if scope == UserOrProject::Project {
                    deduped[*existing_index] = ConfiguredSource {
                        source,
                        scope,
                        filter,
                    };
                }
            }
        }
    }
    deduped
}

/// Files or directory trees behind a list of paths: files pass through,
/// directories are collected per resource kind; missing paths are skipped.
/// Broken ignore rules in the directories go into `diagnostics`.
pub(crate) fn collect_files_from_paths(
    paths: &[PathBuf],
    resource_type: ResourceType,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for path in paths {
        let Ok(stats) = std::fs::metadata(path) else {
            continue;
        };
        if stats.is_file() {
            files.push(path.clone());
        } else if stats.is_dir() {
            files.extend(collect_resource_files(path, resource_type, diagnostics));
        }
    }
    files
}

fn installed_npm_matches_pinned_version(source: &NpmSource, installed_path: &Path) -> bool {
    let Some(installed_version) = npm::installed_npm_version(installed_path) else {
        return false;
    };
    let (_, pinned_version) = super::super::source::parse_npm_spec(&source.spec);
    match pinned_version {
        None => true,
        Some(pinned) => installed_version == pinned,
    }
}

impl PackageManager {
    /// Resolve every session resource path from what is installed.
    /// Configured npm and git sources that are not installed (or an npm
    /// source not at its pinned version) are left out and listed in
    /// [`ResolvedPaths::missing_packages`]. Resolution never installs,
    /// clones, or fetches: only `eukhe package install` and
    /// `eukhe package update` do.
    ///
    /// # Errors
    ///
    /// Returns an error when a configured package source cannot be parsed
    /// or its git install path escapes the install root.
    pub fn resolve(&self) -> Result<ResolvedPaths> {
        let global = self.settings().global_settings().clone();
        let project = self.settings().project_settings().clone();
        let mut accumulator = ResourceAccumulator::default();

        // Project entries precede user entries; the dedupe keeps the project
        // entry when the same package identity appears in both scopes.
        let mut all_packages: Vec<(serde_json::Value, UserOrProject)> = Vec::new();
        for entry in project.packages.iter().flatten() {
            all_packages.push((entry.clone(), UserOrProject::Project));
        }
        for entry in global.packages.iter().flatten() {
            all_packages.push((entry.clone(), UserOrProject::User));
        }
        let package_sources = dedupe_configured_sources(self, all_packages);
        self.resolve_package_sources(package_sources, &mut accumulator)?;

        let global_base_dir = self.agent_dir().to_path_buf();
        let project_base_dir = self.cwd().join(super::super::CONFIG_DIR_NAME);

        for resource_type in RESOURCE_TYPES {
            let project_entries = settings_array(&project, resource_type);
            let global_entries = settings_array(&global, resource_type);
            Self::resolve_local_entries(
                &project_entries,
                resource_type,
                &mut accumulator,
                &top_level_metadata(MetadataSource::Local, SourceScope::Project),
                &project_base_dir,
            );
            Self::resolve_local_entries(
                &global_entries,
                resource_type,
                &mut accumulator,
                &top_level_metadata(MetadataSource::Local, SourceScope::User),
                &global_base_dir,
            );
        }

        self.add_auto_discovered_resources(
            &mut accumulator,
            &global,
            &project,
            &global_base_dir,
            &project_base_dir,
        );

        Ok(to_resolved_paths(accumulator))
    }

    fn resolve_package_sources(
        &self,
        sources: Vec<ConfiguredSource>,
        accumulator: &mut ResourceAccumulator,
    ) -> Result<()> {
        for configured in sources {
            let parsed = parse_source(&configured.source)?;
            let mut metadata = PathMetadata {
                source: MetadataSource::Package(configured.source.clone()),
                scope: configured.scope.into(),
                origin: ResourceOrigin::Package,
                base_dir: None,
            };
            let installed_path = match &parsed {
                ParsedSource::Local(local) => {
                    let base_dir = self.base_dir_for_scope(configured.scope.into());
                    Self::resolve_local_source(
                        &local.path,
                        accumulator,
                        configured.filter.as_ref(),
                        &mut metadata,
                        &base_dir,
                    );
                    continue;
                }
                ParsedSource::Npm(npm_source) => {
                    let installed_path = self.npm_install_path(npm_source, configured.scope);
                    let installed = installed_path.exists()
                        && (!npm_source.pinned
                            || installed_npm_matches_pinned_version(npm_source, &installed_path));
                    installed.then_some(installed_path)
                }
                ParsedSource::Git(git_source) => {
                    let installed_path = git::git_install_path(
                        git_source,
                        configured.scope.into(),
                        self.cwd(),
                        self.agent_dir(),
                    )?;
                    installed_path.exists().then_some(installed_path)
                }
            };
            let Some(installed_path) = installed_path else {
                accumulator.missing_packages.push(MissingPackage {
                    source: configured.source,
                    scope: configured.scope,
                });
                continue;
            };
            metadata.base_dir = Some(installed_path.clone());
            PackageManager::collect_package_resources(
                &installed_path,
                accumulator,
                configured.filter.as_ref(),
                &metadata,
            );
        }
        Ok(())
    }

    /// Resolve one configured local package source: a directory's
    /// resources collect through the manifest/convention scanners; a
    /// bare file yields nothing.
    fn resolve_local_source(
        path: &str,
        accumulator: &mut ResourceAccumulator,
        filter: Option<&PackageFilter>,
        metadata: &mut PathMetadata,
        base_dir: &Path,
    ) {
        let resolved = PackageManager::resolve_path_from_base(path, base_dir);
        if !resolved.exists() {
            return;
        }
        let Ok(stats) = std::fs::metadata(&resolved) else {
            return;
        };
        if stats.is_dir() {
            metadata.base_dir = Some(resolved.clone());
            PackageManager::collect_package_resources(&resolved, accumulator, filter, metadata);
        }
    }

    /// Settings top-level array entries: plain paths relative to the
    /// settings base, pattern entries applied as filters.
    fn resolve_local_entries(
        entries: &[String],
        resource_type: ResourceType,
        accumulator: &mut ResourceAccumulator,
        metadata: &PathMetadata,
        base_dir: &Path,
    ) {
        if entries.is_empty() {
            return;
        }
        let (plain, pattern_entries) = split_patterns(entries);
        let resolved_plain: Vec<PathBuf> = plain
            .iter()
            .map(|path| PackageManager::resolve_path_from_base(path, base_dir))
            .collect();
        let all_files =
            collect_files_from_paths(&resolved_plain, resource_type, &mut accumulator.diagnostics);
        let enabled_paths = apply_patterns(&all_files, &pattern_entries, base_dir);
        for file in all_files {
            let enabled = enabled_paths.contains(&file);
            accumulator
                .map(resource_type)
                .add(&file, metadata.clone(), enabled);
        }
    }
}
