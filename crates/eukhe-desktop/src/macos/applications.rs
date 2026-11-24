//! Installed applications: the bundles in the standard folders and the
//! running apps, resolved and opened through `NSWorkspace` (port of omp
//! `crates/natives/src/desktop/macos/applications.rs`).

use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use super::ffi::appkit::{self, Policy, RunningApp};
use super::guard;
use crate::applications::{Activation, AppError, AppKind, AppState, Application, Document, Opened};
use crate::error::{Error, Refusal};
use crate::types::{Pid, Window};

/// The folders applications install into, searched one level of
/// subfolders deep.
const ROOTS: [&str; 4] = [
    "/Applications",
    "/System/Applications",
    "/System/Library/CoreServices",
    "/System/Volumes/Preboot/Cryptexes/App/System/Applications",
];

/// How long an open waits for the app's first window.
const WINDOW_WAIT: Duration = Duration::from_secs(3);
const WINDOW_POLL: Duration = Duration::from_millis(100);

fn is_bundle(path: &Path) -> bool {
    path.extension()
        .is_some_and(|extension| extension.eq_ignore_ascii_case("app"))
}

/// The `.app` bundles directly in `folder` and in its plain subfolders.
fn bundles_in(folder: &Path, depth: u8, found: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(folder) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if is_bundle(&path) {
            found.push(path);
        } else if depth > 0 && entry.file_type().is_ok_and(|kind| kind.is_dir()) {
            bundles_in(&path, depth - 1, found);
        }
    }
}

pub(super) fn list() -> Vec<Application> {
    let running = appkit::running_apps();
    let mut paths = Vec::new();
    let home = std::env::var_os("HOME").map(|home| PathBuf::from(home).join("Applications"));
    for root in ROOTS.iter().map(PathBuf::from).chain(home) {
        bundles_in(&root, 1, &mut paths);
    }
    paths.extend(
        running
            .iter()
            .filter(|app| app.policy != Policy::Prohibited)
            .filter_map(|app| app.path.clone()),
    );
    paths.sort_unstable();
    paths.dedup();
    paths
        .into_iter()
        .filter_map(|path| application(path, &running))
        .collect()
}

fn application(path: PathBuf, running: &[RunningApp]) -> Option<Application> {
    let info = appkit::bundle(&path)?;
    let name = info.name.or_else(|| {
        path.file_stem()
            .and_then(|stem| stem.to_str())
            .map(str::to_owned)
    })?;
    let state = running
        .iter()
        .find(|app| app.path.as_deref() == Some(path.as_path()))
        .and_then(|app| u32::try_from(app.pid).ok())
        .map_or(AppState::NotRunning, |pid| AppState::Running {
            pid: Some(Pid(pid)),
        });
    Some(Application {
        id: info
            .id
            .unwrap_or_else(|| path.to_string_lossy().into_owned()),
        name,
        path,
        state,
    })
}

pub(super) fn at(path: &Path) -> Result<Application, Error> {
    application(path.to_path_buf(), &appkit::running_apps()).ok_or_else(|| {
        AppError::NotFound {
            input: path.to_string_lossy().into_owned(),
        }
        .into()
    })
}

/// Agents, background-only apps and bundles nested in another app are
/// helpers.
pub(super) fn kind(app: &Application) -> AppKind {
    let nested = app
        .path
        .parent()
        .is_some_and(|parent| parent.ancestors().any(is_bundle));
    if nested || appkit::bundle(&app.path).is_some_and(|info| info.agent) {
        AppKind::Helper
    } else {
        AppKind::Regular
    }
}

fn platform(detail: String) -> Error {
    Error::Refused(Refusal::Platform {
        detail: detail.into(),
    })
}

fn running(app: &Application, pid: i32) -> Application {
    Application {
        id: app.id.clone(),
        name: app.name.clone(),
        path: app.path.clone(),
        state: AppState::Running {
            pid: u32::try_from(pid).ok().map(Pid),
        },
    }
}

/// Launches or reopens `app`; waits briefly for its front window.
pub(super) fn open(
    app: &Application,
    activation: Activation,
    front_window: impl Fn(i32) -> Option<Window>,
) -> Result<Opened, Error> {
    let activate = match activation {
        Activation::Background => false,
        Activation::Activate => true,
    };
    let pid = appkit::open_app(&app.path, activate)
        .map_err(|failure| platform(format!("{} did not open: {failure}", app.name)))?;
    Ok(Opened {
        application: running(app, pid),
        window: wait_window(pid, front_window),
    })
}

/// Opens a file, folder or URL in its default app, in `how`'s app, or
/// selected in Finder.
pub(super) fn open_document(
    target: &str,
    how: &Document<'_>,
    activation: Activation,
    front_window: impl Fn(i32) -> Option<Window>,
) -> Result<Opened, Error> {
    let activate = match activation {
        Activation::Background => false,
        Activation::Activate => true,
    };
    let failed = |failure| platform(format!("{target:?} did not open: {failure}"));
    let pid = match how {
        Document::Default => appkit::open_document(target, None, activate).map_err(failed)?,
        Document::In(app) => {
            appkit::open_document(target, Some(&app.path), activate).map_err(failed)?
        }
        Document::Reveal => {
            appkit::reveal(Path::new(target)).map_err(failed)?;
            return finder(front_window);
        }
    };
    let app = appkit::app(pid)
        .and_then(|app| application(app.path?, &[]))
        .ok_or_else(|| platform(format!("the app that opened {target:?} is not readable")))?;
    Ok(Opened {
        application: running(&app, pid),
        window: wait_window(pid, front_window),
    })
}

/// Finder, which a reveal brings in front.
fn finder(front_window: impl Fn(i32) -> Option<Window>) -> Result<Opened, Error> {
    let running = appkit::running_apps();
    let finder = running
        .iter()
        .find(|app| app.bundle_id.as_deref() == Some("com.apple.finder"))
        .ok_or_else(|| platform("Finder is not running".to_owned()))?;
    let unreadable = || platform("Finder's bundle is not readable".to_owned());
    let path = finder.path.as_deref().ok_or_else(unreadable)?;
    let app = application(path.to_path_buf(), &running).ok_or_else(unreadable)?;
    Ok(Opened {
        window: wait_window(finder.pid, front_window),
        application: app,
    })
}

fn wait_window(pid: i32, front_window: impl Fn(i32) -> Option<Window>) -> Option<Window> {
    let mut window = None;
    guard::wait_for(WINDOW_WAIT, WINDOW_POLL, || {
        window = front_window(pid);
        window.is_some()
    });
    window
}
