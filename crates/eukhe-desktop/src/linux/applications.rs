//! XDG desktop entries: listing, running state, launching (port of omp
//! `crates/natives/src/desktop/linux/applications.rs`).
//!
//! Running state comes from `/proc` executables; wrappers and sandboxes may
//! hide it. A background launch carries the startup timestamp zero, the
//! X11 no-focus hint, which applications and window managers may ignore.

use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::applications::{Activation, AppError, AppKind, AppState, Application, Document, Opened};
use crate::control::intervention::StartTime;
use crate::error::{Error, Feature, Refusal};
use crate::types::Pid;

/// Why a desktop entry cannot be listed or launched.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
enum EntryError {
    #[error("cannot read {path}: {cause}")]
    Read { path: PathBuf, cause: String },
    #[error("Linux application paths are absolute .desktop files")]
    NotDesktopFile,
    #[error("the desktop entry is malformed: {0}")]
    Malformed(&'static str),
    #[error("the desktop entry is hidden")]
    Hidden,
    #[error("the desktop entry is no Type=Application")]
    NotApplication,
    #[error("the desktop entry's TryExec {0:?} is not executable")]
    TryExec(String),
    #[error("the desktop entry has no Exec command (D-Bus activation only)")]
    NoExec,
    #[error("the desktop Exec executable {0:?} is not installed")]
    Missing(String),
    #[error("Terminal=true needs xdg-terminal-exec or /usr/bin/x-terminal-emulator")]
    NoTerminal,
    #[error("cannot launch {path}: {cause}")]
    Spawn { path: PathBuf, cause: String },
}

impl From<EntryError> for Error {
    fn from(error: EntryError) -> Self {
        Self::Refused(Refusal::Platform {
            detail: error.to_string().into(),
        })
    }
}

/// Whether an entry runs in a terminal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Launch {
    Direct,
    Terminal,
}

/// One parsed `[Desktop Entry]`.
#[derive(Debug, PartialEq, Eq)]
struct Entry {
    id: String,
    path: PathBuf,
    name: String,
    icon: Option<String>,
    exec: Option<String>,
    working_directory: Option<PathBuf>,
    launch: Launch,
    kind: AppKind,
}

fn data_roots() -> Vec<PathBuf> {
    let home = env::var_os("XDG_DATA_HOME")
        .filter(|value| !value.is_empty())
        .map(PathBuf::from)
        .filter(|path| path.is_absolute())
        .or_else(|| env::var_os("HOME").map(|home| PathBuf::from(home).join(".local/share")))
        .filter(|path| path.is_absolute());
    let directories = env::var_os("XDG_DATA_DIRS")
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| "/usr/local/share:/usr/share".into());
    home.into_iter()
        .chain(env::split_paths(&directories).filter(|path| path.is_absolute()))
        .map(|root| root.join("applications"))
        .collect()
}

/// `.desktop` files below `directory`; directory symlinks are not followed,
/// since they can form cycles.
fn desktop_files(directory: &Path) -> Vec<PathBuf> {
    let Ok(entries) = fs::read_dir(directory) else {
        return Vec::new();
    };
    let mut files = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        match entry.file_type() {
            Ok(kind) if kind.is_dir() => files.extend(desktop_files(&path)),
            Ok(_)
                if path
                    .extension()
                    .is_some_and(|extension| extension == "desktop")
                    && path.is_file() =>
            {
                files.push(path);
            }
            Ok(_) | Err(_) => {}
        }
    }
    files.sort();
    files
}

fn desktop_id(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('/', "-")
}

/// Locale suffixes `Name[...]` is looked up under, most specific first.
fn locale_names() -> Vec<String> {
    let locale = ["LC_ALL", "LC_MESSAGES", "LANG"]
        .into_iter()
        .find_map(|key| env::var(key).ok().filter(|value| !value.is_empty()))
        .unwrap_or_default();
    let (base, modifier) = locale
        .split_once('@')
        .map_or((locale.as_str(), None), |(base, modifier)| {
            (base, Some(modifier))
        });
    let base = base.split('.').next().unwrap_or(base);
    if base.is_empty() || base == "C" || base == "POSIX" {
        return Vec::new();
    }
    let language = base.split('_').next().unwrap_or(base);
    let mut names = Vec::with_capacity(4);
    if let Some(modifier) = modifier {
        names.push(format!("{base}@{modifier}"));
    }
    names.push(base.to_owned());
    if language != base {
        if let Some(modifier) = modifier {
            names.push(format!("{language}@{modifier}"));
        }
        names.push(language.to_owned());
    }
    names
}

/// The desktop-entry string escapes: `\s`, `\n`, `\t`, `\r`, `\\`.
fn unescape(value: &str) -> Result<String, EntryError> {
    let mut output = String::with_capacity(value.len());
    let mut chars = value.chars();
    while let Some(character) = chars.next() {
        if character != '\\' {
            output.push(character);
            continue;
        }
        output.push(match chars.next() {
            Some('s') => ' ',
            Some('n') => '\n',
            Some('t') => '\t',
            Some('r') => '\r',
            Some('\\') => '\\',
            _ => return Err(EntryError::Malformed("an invalid escape sequence")),
        });
    }
    Ok(output)
}

/// A desktop-entry boolean, absent meaning false.
fn flag(values: &HashMap<&str, &str>, key: &str) -> Result<bool, EntryError> {
    match values.get(key).copied() {
        None | Some("false") => Ok(false),
        Some("true") => Ok(true),
        Some(_) => Err(EntryError::Malformed(
            "a boolean key holds neither true nor false",
        )),
    }
}

/// The `[Desktop Entry]` group's keys.
fn entry_values(text: &str) -> Result<HashMap<&str, &str>, EntryError> {
    let mut values = HashMap::new();
    let mut in_entry = false;
    let mut found = false;
    for line in text.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            in_entry = line == "[Desktop Entry]";
            if in_entry && found {
                return Err(EntryError::Malformed("two Desktop Entry groups"));
            }
            found |= in_entry;
            continue;
        }
        if let (true, Some((key, value))) = (in_entry, line.split_once('=')) {
            if values.insert(key.trim(), value.trim()).is_some() {
                return Err(EntryError::Malformed("a key appears twice"));
            }
        }
    }
    Ok(values)
}

fn read_entry(path: &Path, id: String) -> Result<Entry, EntryError> {
    if !path.is_absolute()
        || path
            .extension()
            .is_none_or(|extension| extension != "desktop")
    {
        return Err(EntryError::NotDesktopFile);
    }
    let text = fs::read_to_string(path).map_err(|error| EntryError::Read {
        path: path.to_owned(),
        cause: error.to_string(),
    })?;
    parse_entry(&text, path, id)
}

fn parse_entry(text: &str, path: &Path, id: String) -> Result<Entry, EntryError> {
    let values = entry_values(text)?;
    if flag(&values, "Hidden")? {
        return Err(EntryError::Hidden);
    }
    if values.get("Type").copied() != Some("Application") {
        return Err(EntryError::NotApplication);
    }
    let base = values.get("Name").ok_or(EntryError::Malformed("no Name"))?;
    let name = locale_names()
        .iter()
        .find_map(|locale| values.get(format!("Name[{locale}]").as_str()))
        .unwrap_or(base);
    let name = unescape(name)?;
    if name.is_empty() {
        return Err(EntryError::Malformed("an empty Name"));
    }
    let working_directory = values
        .get("Path")
        .map(|value| unescape(value))
        .transpose()?
        .filter(|value| !value.is_empty())
        .map(PathBuf::from);
    if working_directory
        .as_ref()
        .is_some_and(|path| !path.is_absolute())
    {
        return Err(EntryError::Malformed("a relative Path"));
    }
    if let Some(value) = values.get("TryExec") {
        let executable = unescape(value)?;
        if resolve_executable(&executable, working_directory.as_deref()).is_none() {
            return Err(EntryError::TryExec(executable));
        }
    }
    Ok(Entry {
        id,
        path: path.to_owned(),
        name,
        icon: values
            .get("Icon")
            .map(|value| unescape(value))
            .transpose()?,
        exec: values.get("Exec").map(|exec| (*exec).to_owned()),
        working_directory,
        launch: if flag(&values, "Terminal")? {
            Launch::Terminal
        } else {
            Launch::Direct
        },
        kind: if flag(&values, "NoDisplay")? {
            AppKind::Helper
        } else {
            AppKind::Regular
        },
    })
}

fn resolve_executable(executable: &str, working_directory: Option<&Path>) -> Option<PathBuf> {
    fs::canonicalize(executable_path(executable, working_directory)?).ok()
}

/// An executable named absolutely or found on `PATH`.
fn executable_path(executable: &str, working_directory: Option<&Path>) -> Option<PathBuf> {
    if executable.is_empty() || executable.contains('\0') {
        return None;
    }
    let usable = |path: PathBuf| {
        let metadata = fs::metadata(&path).ok()?;
        (metadata.is_file() && metadata.permissions().mode() & 0o111 != 0).then_some(path)
    };
    let executable = Path::new(executable);
    if executable.is_absolute() {
        return usable(executable.to_owned());
    }
    if executable.components().count() != 1 {
        return None;
    }
    let cwd = working_directory
        .map(Path::to_owned)
        .or_else(|| env::current_dir().ok())?;
    env::split_paths(&env::var_os("PATH")?).find_map(|directory| {
        usable(if directory.is_absolute() {
            directory.join(executable)
        } else {
            cwd.join(directory).join(executable)
        })
    })
}

/// Splits an `Exec` value into argv per the Desktop Entry specification's
/// two escaping layers: no shell, no expansion. File and URL codes drop.
fn exec_argv(
    raw: &str,
    name: &str,
    icon: Option<&str>,
    path: &Path,
) -> Result<Vec<String>, EntryError> {
    let words = exec_words(&unescape(raw)?)?;
    let mut argv = Vec::with_capacity(words.len());
    let mut file_codes = 0;
    for (index, word) in words.iter().enumerate() {
        let mut expanded = String::with_capacity(word.len());
        let mut chars = word.chars();
        let mut removed = false;
        let mut icon_arguments = false;
        while let Some(character) = chars.next() {
            if character != '%' {
                expanded.push(character);
                continue;
            }
            let code = chars
                .next()
                .ok_or(EntryError::Malformed("an incomplete Exec field code"))?;
            if index == 0 && code != '%' {
                return Err(EntryError::Malformed("a field code in the Exec executable"));
            }
            match code {
                '%' => expanded.push('%'),
                'c' => expanded.push_str(name),
                'k' => expanded.push_str(&path.to_string_lossy()),
                'i' if word == "%i" => icon_arguments = true,
                'f' | 'u' => {
                    file_codes += 1;
                    removed = true;
                }
                'F' | 'U' if word.len() == 2 => {
                    file_codes += 1;
                    removed = true;
                }
                'd' | 'D' | 'n' | 'N' | 'v' | 'm' => removed = true,
                _ => return Err(EntryError::Malformed("an unsupported Exec field code")),
            }
        }
        if icon_arguments {
            if let Some(icon) = icon.filter(|icon| !icon.is_empty()) {
                argv.push("--icon".to_owned());
                argv.push(icon.to_owned());
            }
        } else if !removed || !expanded.is_empty() {
            argv.push(expanded);
        }
    }
    if file_codes > 1 {
        return Err(EntryError::Malformed(
            "more than one file or URL field code",
        ));
    }
    if argv.first().is_none_or(String::is_empty) {
        return Err(EntryError::Malformed("no executable in Exec"));
    }
    Ok(argv)
}

/// The words of an unescaped `Exec` value: double quotes group, and
/// shell-reserved characters must be quoted.
fn exec_words(value: &str) -> Result<Vec<String>, EntryError> {
    let mut words = Vec::new();
    let mut word = String::new();
    let mut quoted = false;
    let mut started = false;
    let mut chars = value.chars();
    while let Some(character) = chars.next() {
        match character {
            '"' => {
                quoted = !quoted;
                started = true;
            }
            '\\' => {
                let next = chars
                    .next()
                    .ok_or(EntryError::Malformed("a trailing backslash in Exec"))?;
                if quoted && !matches!(next, '"' | '`' | '$' | '\\') {
                    return Err(EntryError::Malformed("an invalid quoted escape in Exec"));
                }
                word.push(next);
                started = true;
            }
            '%' if quoted => return Err(EntryError::Malformed("a field code inside quotes")),
            '\0' => return Err(EntryError::Malformed("NUL in Exec")),
            character if !quoted && character.is_ascii_whitespace() => {
                if started {
                    words.push(std::mem::take(&mut word));
                    started = false;
                }
            }
            '\'' | '>' | '<' | '~' | '|' | '&' | ';' | '$' | '*' | '?' | '#' | '(' | ')' | '`'
                if !quoted =>
            {
                return Err(EntryError::Malformed("a reserved character outside quotes"));
            }
            character => {
                word.push(character);
                started = true;
            }
        }
    }
    if quoted {
        return Err(EntryError::Malformed("an unterminated quote in Exec"));
    }
    if started {
        words.push(word);
    }
    Ok(words)
}

impl Entry {
    fn argv(&self) -> Result<Vec<String>, EntryError> {
        let exec = self.exec.as_deref().ok_or(EntryError::NoExec)?;
        exec_argv(exec, &self.name, self.icon.as_deref(), &self.path)
    }

    fn executable(&self) -> Option<PathBuf> {
        let argv = self.argv().ok()?;
        resolve_executable(argv.first()?, self.working_directory.as_deref())
    }

    fn application(&self, processes: &HashMap<PathBuf, Vec<Pid>>) -> Application {
        let pid = self
            .executable()
            .and_then(|exe| processes.get(&exe).and_then(|pids| pids.first()).copied());
        Application {
            id: self.id.clone(),
            name: self.name.clone(),
            path: self.path.clone(),
            state: match pid {
                Some(pid) => AppState::Running { pid: Some(pid) },
                None => AppState::NotRunning,
            },
        }
    }
}

/// Every readable process by executable, lowest pid first.
fn processes() -> HashMap<PathBuf, Vec<Pid>> {
    let mut processes: HashMap<PathBuf, Vec<Pid>> = HashMap::new();
    let Ok(entries) = fs::read_dir("/proc") else {
        return processes;
    };
    for entry in entries.flatten() {
        let Some(pid) = entry
            .file_name()
            .to_str()
            .and_then(|name| name.parse::<u32>().ok())
        else {
            continue;
        };
        if let Ok(exe) = fs::read_link(entry.path().join("exe")) {
            processes.entry(exe).or_default().push(Pid(pid));
        }
    }
    for pids in processes.values_mut() {
        pids.sort_unstable_by_key(|pid| pid.0);
    }
    processes
}

#[allow(
    clippy::unnecessary_wraps,
    reason = "the seam's signature; the macOS listing can fail"
)]
pub(crate) fn list_applications() -> Result<Vec<Application>, Error> {
    let processes = processes();
    let mut seen = HashSet::new();
    let mut applications = Vec::new();
    for root in data_roots() {
        for path in desktop_files(&root) {
            let id = desktop_id(&root, &path);
            // A hidden entry is a tombstone: it hides lower roots' entry.
            if !seen.insert(id.clone()) {
                continue;
            }
            if let Ok(entry) = read_entry(&path, id) {
                applications.push(entry.application(&processes));
            }
        }
    }
    Ok(applications)
}

pub(crate) fn application_at(path: &Path) -> Result<Application, Error> {
    let id = data_roots()
        .iter()
        .find(|root| path.starts_with(root))
        .map_or_else(
            || path.to_string_lossy().into_owned(),
            |root| desktop_id(root, path),
        );
    match read_entry(path, id) {
        Ok(entry) => Ok(entry.application(&processes())),
        Err(EntryError::Read { .. } | EntryError::NotDesktopFile) => Err(AppError::NotFound {
            input: path.to_string_lossy().into_owned(),
        }
        .into()),
        Err(error) => Err(error.into()),
    }
}

/// `NoDisplay` entries are handlers and helpers, not apps a user opens.
pub(crate) fn app_kind(app: &Application) -> AppKind {
    read_entry(&app.path, app.id.clone()).map_or(AppKind::Regular, |entry| entry.kind)
}

/// A startup id with timestamp zero: the X11 hint not to take focus.
fn background_startup_id() -> String {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    format!("eukhe-{}-{nonce}_TIME0", std::process::id())
}

/// The configured terminal helper running `argv`, never a guessed emulator.
fn terminal_command(entry: &Entry, argv: &[String]) -> Result<Command, EntryError> {
    let (program, arguments) = argv.split_first().ok_or(EntryError::NoExec)?;
    let executable = executable_path(program, entry.working_directory.as_deref())
        .ok_or_else(|| EntryError::Missing(program.clone()))?;
    if let Some(helper) = resolve_executable("xdg-terminal-exec", None) {
        let mut command = Command::new(helper);
        if let Some(directory) = &entry.working_directory {
            command.arg(format!("--dir={}", directory.display()));
        }
        command.arg("--").arg(&executable).args(arguments);
        return Ok(command);
    }
    let alternative = Path::new("/usr/bin/x-terminal-emulator");
    if executable_path(&alternative.to_string_lossy(), None).is_some() {
        let mut command = Command::new(alternative);
        command.arg("-e").arg(&executable).args(arguments);
        return Ok(command);
    }
    Err(EntryError::NoTerminal)
}

/// Launches `app` unless it runs; with `Activate`, brings its window
/// forward and reports it.
pub(crate) fn open_application(app: &Application, activation: Activation) -> Result<Opened, Error> {
    let entry = read_entry(&app.path, app.id.clone())?;
    let current = entry.application(&processes());
    let executable = entry.executable();
    let launched = match current.state {
        AppState::Running { pid } => pid,
        AppState::NotRunning => Some(launch(&entry, activation)?),
    };
    let window = match activation {
        Activation::Background => None,
        Activation::Activate => Some(super::x11::activate_process(
            launched,
            executable.as_deref(),
        )?),
    };
    Ok(Opened {
        application: entry.application(&processes()),
        window,
    })
}

/// Spawns the entry's command detached, returning the spawned pid.
fn launch(entry: &Entry, activation: Activation) -> Result<Pid, EntryError> {
    let argv = entry.argv()?;
    let mut command = match entry.launch {
        Launch::Terminal => terminal_command(entry, &argv)?,
        Launch::Direct => {
            let (program, arguments) = argv.split_first().ok_or(EntryError::NoExec)?;
            if entry.executable().is_none() {
                return Err(EntryError::Missing(program.clone()));
            }
            let mut command = Command::new(program);
            command.args(arguments);
            command
        }
    };
    command
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .env_remove("XDG_ACTIVATION_TOKEN")
        .env_remove("DESKTOP_STARTUP_ID");
    if let Some(directory) = &entry.working_directory {
        command.current_dir(directory);
    }
    match activation {
        Activation::Background => {
            command.env("DESKTOP_STARTUP_ID", background_startup_id());
        }
        Activation::Activate => {}
    }
    let mut child = command.spawn().map_err(|error| EntryError::Spawn {
        path: entry.path.clone(),
        cause: error.to_string(),
    })?;
    let pid = Pid(child.id());
    // Reaps the launcher, which may exit at once, without blocking.
    std::thread::spawn(move || child.wait());
    Ok(pid)
}

pub(crate) fn open_document(_: &str, _: &Document<'_>, _: Activation) -> Result<Opened, Error> {
    Err(Error::unsupported(Feature::Documents))
}

/// When `pid` started, in clock ticks since boot (`/proc/<pid>/stat` field 22).
pub(crate) fn process_started(pid: Pid) -> Option<StartTime> {
    let stat = fs::read_to_string(format!("/proc/{}/stat", pid.0)).ok()?;
    start_time(&stat)
}

fn start_time(stat: &str) -> Option<StartTime> {
    // The command name may hold spaces and parentheses: fields follow the
    // last `)`, starting at field 3.
    let (_, fields) = stat.rsplit_once(')')?;
    fields
        .split_ascii_whitespace()
        .nth(19)?
        .parse()
        .ok()
        .map(StartTime)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exec_splits_quotes_and_drops_file_codes() {
        let path = Path::new("/usr/share/applications/x.desktop");
        assert_eq!(
            exec_argv(r#"gedit --new-window "a b" %U"#, "Gedit", None, path),
            Ok(vec![
                "gedit".to_owned(),
                "--new-window".to_owned(),
                "a b".to_owned()
            ])
        );
        assert_eq!(
            exec_argv("app %i --name=%c", "App", Some("app-icon"), path),
            Ok(vec![
                "app".to_owned(),
                "--icon".to_owned(),
                "app-icon".to_owned(),
                "--name=App".to_owned()
            ])
        );
        assert_eq!(
            exec_argv("app; rm -rf /", "App", None, path),
            Err(EntryError::Malformed("a reserved character outside quotes"))
        );
        assert_eq!(
            exec_argv("%f", "App", None, path),
            Err(EntryError::Malformed("a field code in the Exec executable"))
        );
    }

    #[test]
    fn an_entry_parses_its_group_only() {
        let text =
            "[Desktop Entry]\nType=Application\nName=Fixture\nExec=/bin/true\nNoDisplay=true\n\
                    [Desktop Action new]\nName=Other\n";
        let entry = parse_entry(
            text,
            Path::new("/a/fixture.desktop"),
            "fixture.desktop".to_owned(),
        );
        assert!(entry.as_ref().is_ok_and(|entry| entry.name == "Fixture"
            && entry.kind == AppKind::Helper
            && entry.launch == Launch::Direct));
        let hidden = "[Desktop Entry]\nType=Application\nName=X\nHidden=true\n";
        assert_eq!(
            parse_entry(hidden, Path::new("/a/x.desktop"), String::new()),
            Err(EntryError::Hidden)
        );
    }

    #[test]
    fn the_start_time_follows_the_last_parenthesis() {
        let stat = "42 (a b) c) S 1 42 42 0 -1 4194560 100 0 0 0 1 2 0 0 20 0 1 0 98765 1000 10";
        assert_eq!(start_time(stat), Some(StartTime(98_765)));
        assert_eq!(start_time("garbage"), None);
    }
}
