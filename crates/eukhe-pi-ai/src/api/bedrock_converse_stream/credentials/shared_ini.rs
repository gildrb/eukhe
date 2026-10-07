//! The shared config/credentials file loader of `@smithy/core/config`
//! (formerly `@smithy/shared-ini-file-loader`): `parseIni`, `getConfigData`,
//! `loadSharedConfigFiles`, `parseKnownFiles`, `loadSsoSessionData`,
//! `getProfileName`, and the `loadConfig` env → shared-file → default lookup.

use std::sync::PoisonError;

use super::js_compat::node_path_join;
use super::CredentialEnv;
use crate::utils::js::{array_index_key, is_js_whitespace, js_trim};

/// `IniSectionType` values.
const SECTION_TYPES: [&str; 3] = ["profile", "sso-session", "services"];

/// One section: a JS object of strings in insertion order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct IniSection {
    entries: Vec<(String, String)>,
}

impl IniSection {
    /// `section[key]`.
    pub(crate) fn get(&self, key: &str) -> Option<&str> {
        self.entries
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| value.as_str())
    }

    /// `section[key] = value` (an existing key keeps its position).
    pub(crate) fn set(&mut self, key: &str, value: String) {
        match self.entries.iter_mut().find(|(name, _)| name == key) {
            Some(entry) => entry.1 = value,
            None => self.entries.push((key.to_owned(), value)),
        }
    }

    /// `Object.assign(section, other)`.
    fn assign(&mut self, other: &IniSection) {
        for (key, value) in &other.entries {
            self.set(key, value.clone());
        }
    }

    /// `Object.keys(section)`: array-index keys ascending, then the rest in
    /// insertion order.
    pub(crate) fn keys(&self) -> Vec<&str> {
        js_key_order(self.entries.iter().map(|(key, _)| key.as_str()))
    }

    #[cfg(test)]
    pub(crate) fn from_pairs(pairs: &[(&str, &str)]) -> Self {
        let mut section = Self::default();
        for (key, value) in pairs {
            section.set(key, (*value).to_owned());
        }
        section
    }
}

/// JS own-key enumeration order of `keys` (insertion order otherwise).
pub(crate) fn js_key_order<'a>(keys: impl Iterator<Item = &'a str>) -> Vec<&'a str> {
    let mut indexed = Vec::new();
    let mut named = Vec::new();
    for key in keys {
        match array_index_key(key) {
            Some(index) => indexed.push((index, key)),
            None => named.push(key),
        }
    }
    indexed.sort_by_key(|(index, _)| *index);
    indexed
        .into_iter()
        .map(|(_, key)| key)
        .chain(named)
        .collect()
}

/// A parsed file: sections by name, a JS object in insertion order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct IniFile {
    sections: Vec<(String, IniSection)>,
}

impl IniFile {
    /// `file[name]`.
    pub(crate) fn get(&self, name: &str) -> Option<&IniSection> {
        self.sections
            .iter()
            .find(|(key, _)| key == name)
            .map(|(_, section)| section)
    }

    fn get_mut(&mut self, name: &str) -> Option<&mut IniSection> {
        self.sections
            .iter_mut()
            .find(|(key, _)| key == name)
            .map(|(_, section)| section)
    }

    /// `file[name] = section` (an existing name keeps its position).
    fn set(&mut self, name: &str, section: IniSection) {
        match self.get_mut(name) {
            Some(existing) => *existing = section,
            None => self.sections.push((name.to_owned(), section)),
        }
    }

    /// `Object.entries(file)`.
    fn entries(&self) -> Vec<(&str, &IniSection)> {
        js_key_order(self.sections.iter().map(|(name, _)| name.as_str()))
            .into_iter()
            .filter_map(|name| self.get(name).map(|section| (name, section)))
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn from_sections(sections: Vec<(&str, IniSection)>) -> Self {
        let mut file = Self::default();
        for (name, section) in sections {
            file.set(name, section);
        }
        file
    }
}

/// The text before the first `;`/`#` that starts the line or follows
/// whitespace (`iniLine.split(/(^|\s)[;#]/)[0]`).
fn strip_comment(line: &str) -> &str {
    let mut previous: Option<char> = None;
    for (index, c) in line.char_indices() {
        if matches!(c, ';' | '#') && previous.is_none_or(is_js_whitespace) {
            let end = previous.map_or(index, |previous| index - previous.len_utf8());
            return &line[..end];
        }
        previous = Some(c);
    }
    line
}

fn is_prefix_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | '-')
}

fn is_name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '@' | '+' | '.' | '%' | ':' | '/')
}

/// `prefixKeyRegex.exec(sectionName)`:
/// `/^([\w-]+)\s(["'])?([\w-@+.%:/]+)\2$/` → `(prefix, name)`.
fn match_prefixed_section(section_name: &str) -> Option<(&str, &str)> {
    let prefix_end = section_name
        .char_indices()
        .find(|(_, c)| !is_prefix_char(*c))
        .map_or(section_name.len(), |(index, _)| index);
    if prefix_end == 0 {
        return None;
    }
    let mut rest = section_name[prefix_end..].chars();
    let separator = rest.next().filter(|c| is_js_whitespace(*c))?;
    let rest = &section_name[prefix_end + separator.len_utf8()..];
    let name = match rest.chars().next() {
        Some(quote @ ('"' | '\'')) => rest[1..].strip_suffix(quote)?,
        _ => rest,
    };
    (!name.is_empty() && name.chars().all(is_name_char))
        .then(|| (&section_name[..prefix_end], name))
}

/// The error of a blocked section name (`Found invalid profile name "…"`);
/// the loader swallows it, so the file reads as empty.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InvalidProfileName(pub(crate) String);

/// `parseIni(iniData)`.
///
/// # Errors
///
/// [`InvalidProfileName`] for a `[__proto__]` / `[profile __proto__]` section.
pub(crate) fn parse_ini(data: &str) -> Result<IniFile, InvalidProfileName> {
    let mut map = IniFile::default();
    let mut current_section: Option<String> = None;
    let mut current_sub_section: Option<String> = None;
    for line in data.split('\n') {
        let line = line.strip_suffix('\r').unwrap_or(line);
        let trimmed = js_trim(strip_comment(line));
        let is_section = trimmed.len() >= 2 && trimmed.starts_with('[') && trimmed.ends_with(']');
        if is_section {
            current_section = None;
            current_sub_section = None;
            let section_name = &trimmed[1..trimmed.len() - 1];
            match match_prefixed_section(section_name) {
                Some((prefix, name)) => {
                    if SECTION_TYPES.contains(&prefix) {
                        current_section = Some(format!("{prefix}.{name}"));
                    }
                }
                None => current_section = Some(section_name.to_owned()),
            }
            if matches!(section_name, "__proto__" | "profile __proto__") {
                return Err(InvalidProfileName(format!(
                    "Found invalid profile name \"{section_name}\""
                )));
            }
            continue;
        }
        let Some(section) = current_section.as_deref().filter(|name| !name.is_empty()) else {
            continue;
        };
        let Some(equals) = trimmed.find('=').filter(|index| *index != 0) else {
            continue;
        };
        let name = js_trim(&trimmed[..equals]);
        let value = js_trim(&trimmed[equals + 1..]);
        if value.is_empty() {
            current_sub_section = Some(name.to_owned());
            continue;
        }
        if current_sub_section.is_some() && !line.starts_with(is_js_whitespace) {
            current_sub_section = None;
        }
        let key = match &current_sub_section {
            Some(sub_section) => format!("{sub_section}.{name}"),
            None => name.to_owned(),
        };
        // Assigning `__proto__` sets the prototype, never a key.
        if key == "__proto__" {
            continue;
        }
        if map.get(section).is_none() {
            map.set(section, IniSection::default());
        }
        if let Some(target) = map.get_mut(section) {
            target.set(&key, value.to_owned());
        }
    }
    Ok(map)
}

/// `getConfigData(data)`: `[default]` plus the `profile`, `sso-session`, and
/// `services` sections, profiles keyed by bare name.
pub(crate) fn get_config_data(data: &IniFile) -> IniFile {
    let mut result = IniFile::default();
    if let Some(default) = data.get("default") {
        result.set("default", default.clone());
    }
    for (key, section) in data.entries() {
        let Some(separator) = key.find('.') else {
            continue;
        };
        let prefix = &key[..separator];
        if !SECTION_TYPES.contains(&prefix) {
            continue;
        }
        let updated = if prefix == "profile" {
            &key[separator + 1..]
        } else {
            key
        };
        result.set(updated, section.clone());
    }
    result
}

/// `getConfigFilepath()`.
pub(crate) fn config_file_path(env: &CredentialEnv<'_>) -> String {
    env.truthy_var("AWS_CONFIG_FILE")
        .unwrap_or_else(|| env.home_path(&[".aws", "config"]))
}

/// `getCredentialsFilepath()`.
pub(crate) fn credentials_file_path(env: &CredentialEnv<'_>) -> String {
    env.truthy_var("AWS_SHARED_CREDENTIALS_FILE")
        .unwrap_or_else(|| env.home_path(&[".aws", "credentials"]))
}

/// The cached `readFile(path)` of the loader: each path is read once per
/// process; `None` when the read failed.
async fn read_cached_file(env: &CredentialEnv<'_>, path: &str) -> Option<String> {
    let cached = env
        .state
        .shared_files
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .get(path)
        .cloned();
    if let Some(text) = cached {
        return text;
    }
    let text = tokio::fs::read(path)
        .await
        .ok()
        .map(|bytes| String::from_utf8_lossy(&bytes).into_owned());
    env.state
        .shared_files
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .entry(path.to_owned())
        .or_insert(text)
        .clone()
}

/// `~/`-relative paths resolve against the home directory.
fn resolve_home_relative(env: &CredentialEnv<'_>, path: String) -> String {
    match path.strip_prefix("~/") {
        Some(rest) => node_path_join(&[&env.home_dir(), rest]),
        None => path,
    }
}

/// Both parsed files of `loadSharedConfigFiles()`.
#[derive(Debug, Clone, Default)]
pub(crate) struct SharedConfigFiles {
    pub(crate) config_file: IniFile,
    pub(crate) credentials_file: IniFile,
}

/// `loadSharedConfigFiles()`: unreadable or invalid files read as empty.
pub(crate) async fn load_shared_config_files(env: &CredentialEnv<'_>) -> SharedConfigFiles {
    let credentials_path = resolve_home_relative(env, credentials_file_path(env));
    let config_path = resolve_home_relative(env, config_file_path(env));
    let config_file = read_cached_file(env, &config_path)
        .await
        .and_then(|text| parse_ini(&text).ok())
        .map(|parsed| get_config_data(&parsed))
        .unwrap_or_default();
    let credentials_file = read_cached_file(env, &credentials_path)
        .await
        .and_then(|text| parse_ini(&text).ok())
        .unwrap_or_default();
    SharedConfigFiles {
        config_file,
        credentials_file,
    }
}

/// `mergeConfigFiles(configFile, credentialsFile)`: credentials values win.
pub(crate) fn merge_config_files(files: &SharedConfigFiles) -> IniFile {
    let mut merged = files.config_file.clone();
    for (name, section) in files.credentials_file.entries() {
        match merged.get_mut(name) {
            Some(existing) => existing.assign(section),
            None => merged.set(name, section.clone()),
        }
    }
    merged
}

/// `parseKnownFiles()`.
pub(crate) async fn parse_known_files(env: &CredentialEnv<'_>) -> IniFile {
    merge_config_files(&load_shared_config_files(env).await)
}

/// `loadSsoSessionData()`: the `[sso-session name]` sections of the config
/// file, by name. The path is not `~/`-expanded (as in the SDK).
pub(crate) async fn load_sso_session_data(env: &CredentialEnv<'_>) -> IniFile {
    let Some(text) = read_cached_file(env, &config_file_path(env)).await else {
        return IniFile::default();
    };
    let Ok(parsed) = parse_ini(&text) else {
        return IniFile::default();
    };
    let mut sessions = IniFile::default();
    for (key, section) in parsed.entries() {
        if let Some(name) = key.strip_prefix("sso-session.") {
            sessions.set(name, section.clone());
        }
    }
    sessions
}

/// `getProfileName({ profile })`: the profile, `AWS_PROFILE`, else `default`.
pub(crate) fn get_profile_name(env: &CredentialEnv<'_>, profile: Option<&str>) -> String {
    profile
        .filter(|profile| !profile.is_empty())
        .map(str::to_owned)
        .or_else(|| env.truthy_var("AWS_PROFILE"))
        .unwrap_or_else(|| "default".to_owned())
}

/// `preferredFile` of `fromSharedConfigFiles`: which file's profile values win.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PreferredFile {
    Config,
    Credentials,
}

/// The `fromEnv` → `fromSharedConfigFiles` links of `loadConfig`: the env
/// selector's value, else the file selector's value over the merged profile
/// (selector failures fall through like `undefined`). `None` leaves the
/// caller's default.
pub(crate) async fn load_config<T>(
    env: &CredentialEnv<'_>,
    profile: Option<&str>,
    preferred_file: PreferredFile,
    env_selector: impl Fn(&CredentialEnv<'_>) -> Option<T>,
    file_selector: impl Fn(&IniSection, &IniFile) -> Option<T>,
) -> Option<T> {
    if let Some(value) = env_selector(env) {
        return Some(value);
    }
    let profile_name = get_profile_name(env, profile);
    let files = load_shared_config_files(env).await;
    let from_credentials = files.credentials_file.get(&profile_name);
    let from_config = files.config_file.get(&profile_name);
    let (base, preferred, preferred_file) = match preferred_file {
        PreferredFile::Config => (from_credentials, from_config, &files.config_file),
        PreferredFile::Credentials => (from_config, from_credentials, &files.credentials_file),
    };
    let mut merged = base.cloned().unwrap_or_default();
    if let Some(preferred) = preferred {
        merged.assign(preferred);
    }
    file_selector(&merged, preferred_file)
}

/// `booleanSelector`: `"true"` / `"false"`; anything else fails (falls through).
pub(crate) fn boolean_value(value: Option<&str>) -> Option<bool> {
    match value? {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}
