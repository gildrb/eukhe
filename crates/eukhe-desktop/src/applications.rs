//! Installed applications: listing, resolving a name, opening (port of the
//! shared part of omp `crates/natives/src/desktop/applications.rs`).

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::error::Error;
use crate::platform;
use crate::types::{Pid, Support, Window};

/// One installed application and whether it runs now.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Application {
    /// The bundle id on macOS, the desktop entry id on Linux.
    pub id: String,
    pub name: String,
    pub path: PathBuf,
    pub state: AppState,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "snake_case")]
pub enum AppState {
    Running { pid: Option<Pid> },
    NotRunning,
}

/// Which applications a listing keeps.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AppScope {
    #[default]
    All,
    Running,
}

/// A listing's filter: `text` matches name, id or path, ignoring case.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AppQuery {
    #[serde(default)]
    pub text: Option<String>,
    #[serde(default)]
    pub scope: AppScope,
}

/// Whether an inventory entry is an app a user opens or a helper (an agent,
/// a background-only app, an extension) that shares its name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code, reason = "the platform backends construct both variants")]
pub(crate) enum AppKind {
    Regular,
    Helper,
}

/// Whether opening brings the application forward.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Activation {
    /// Launch or reopen behind the user's app.
    #[default]
    Background,
    Activate,
}

/// How a file, folder or URL target opens.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "with", rename_all = "snake_case")]
pub enum DocumentRoute {
    /// In its default application.
    #[default]
    Default,
    /// In the application an id, name or path names.
    App { app: String },
    /// Selected in the file manager.
    Reveal,
}

/// What `open_application` opens: an application id, name or path, or a
/// file, folder or URL.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpenRequest {
    pub target: String,
    #[serde(default)]
    pub activation: Activation,
    #[serde(default)]
    pub document: DocumentRoute,
}

/// An opened application and, where the backend waits for one, its front
/// window.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Opened {
    pub application: Application,
    pub window: Option<Window>,
}

/// How a document opens, resolved.
#[allow(dead_code, reason = "the platform backends read the application")]
pub(crate) enum Document<'a> {
    Default,
    In(&'a Application),
    Reveal,
}

/// Why an application target names nothing to open.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AppError {
    #[error("the target is empty or holds NUL; nothing was opened")]
    Invalid,
    #[error("application {input:?} is ambiguous; use an exact path (matches include {first:?} and {second:?}); nothing was opened")]
    Ambiguous {
        input: String,
        first: PathBuf,
        second: PathBuf,
    },
    #[error("application {input:?} was not found; list the applications or give an existing path; nothing was opened")]
    NotFound { input: String },
}

/// `apps` matching `query`, sorted by name, id, path.
pub(crate) fn filter(mut apps: Vec<Application>, query: &AppQuery) -> Vec<Application> {
    let text = query.text.as_deref().map(str::to_lowercase);
    apps.retain(|app| {
        let in_scope = match (query.scope, app.state) {
            (AppScope::All, _) | (AppScope::Running, AppState::Running { .. }) => true,
            (AppScope::Running, AppState::NotRunning) => false,
        };
        in_scope
            && text.as_deref().is_none_or(|text| {
                app.name.to_lowercase().contains(text)
                    || app.id.to_lowercase().contains(text)
                    || app.path.to_string_lossy().to_lowercase().contains(text)
            })
    });
    apps.sort_by(|a, b| {
        a.name
            .cmp(&b.name)
            .then_with(|| a.id.cmp(&b.id))
            .then_with(|| a.path.cmp(&b.path))
    });
    apps
}

/// The app `input` names: an exact id or path first, then a display name.
/// A name one regular app shares only with helpers names the regular app.
fn resolve<'a>(
    apps: &'a [Application],
    input: &str,
    kind: impl Fn(&Application) -> AppKind,
) -> Result<Option<&'a Application>, AppError> {
    let mut exact = apps
        .iter()
        .filter(|app| app.id == input || app.path.as_os_str() == input);
    if let Some(first) = exact.next() {
        return unique(first, exact.next(), input).map(Some);
    }
    let folded = input.to_lowercase();
    let mut names = apps.iter().filter(|app| app.name.to_lowercase() == folded);
    let Some(first) = names.next() else {
        return Ok(None);
    };
    let Some(second) = names.next() else {
        return Ok(Some(first));
    };
    let mut regular = [first, second]
        .into_iter()
        .chain(names)
        .filter(|app| kind(app) == AppKind::Regular);
    match (regular.next(), regular.next()) {
        (Some(only), None) => Ok(Some(only)),
        (Some(one), Some(other)) => unique(one, Some(other), input).map(Some),
        (None, _) => unique(first, Some(second), input).map(Some),
    }
}

fn unique<'a>(
    first: &'a Application,
    second: Option<&Application>,
    input: &str,
) -> Result<&'a Application, AppError> {
    match second {
        None => Ok(first),
        Some(second) => Err(AppError::Ambiguous {
            input: input.to_owned(),
            first: first.path.clone(),
            second: second.path.clone(),
        }),
    }
}

/// The scheme of a URL such as `https://…`; never a drive letter.
fn url_scheme(input: &str) -> Option<&str> {
    let (scheme, _) = input.split_once(':')?;
    (scheme.len() > 1
        && scheme.starts_with(|c: char| c.is_ascii_alphabetic())
        && scheme
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '+' | '-' | '.')))
    .then_some(scheme)
}

fn is_app_bundle(path: &Path) -> bool {
    path.extension()
        .is_some_and(|extension| extension.as_encoded_bytes().eq_ignore_ascii_case(b"app"))
}

/// What a target opens as.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Route {
    Application,
    Document,
}

/// An explicit document route asks for a document. Otherwise an exact id or
/// path is an application; then a URL, or an existing non-bundle path where
/// the backend opens documents, is a document.
fn route(apps: &[Application], request: &OpenRequest, documents: Support) -> Route {
    match request.document {
        DocumentRoute::App { .. } | DocumentRoute::Reveal => return Route::Document,
        DocumentRoute::Default => {}
    }
    let input = request.target.as_str();
    if apps
        .iter()
        .any(|app| app.id == input || app.path.as_os_str() == input)
    {
        return Route::Application;
    }
    let path = Path::new(input);
    let document = if path.exists() {
        documents == Support::Supported && !is_app_bundle(path)
    } else {
        url_scheme(input).is_some()
    };
    if document {
        Route::Document
    } else {
        Route::Application
    }
}

/// The installed application `input` names among `apps`: an id or path,
/// then a display name.
fn application(apps: &[Application], input: &str) -> Result<Application, Error> {
    let path = Path::new(input);
    let listed = apps
        .iter()
        .any(|app| app.id == input || app.path.as_os_str() == input);
    if !listed && (path.is_absolute() || input.contains(std::path::MAIN_SEPARATOR) || path.exists())
    {
        let app = platform::application_at(path)?;
        // A bundle read alone says it is not running: take the listed state.
        return Ok(apps
            .iter()
            .find(|listed| listed.path == app.path)
            .cloned()
            .unwrap_or(app));
    }
    resolve(apps, input, platform::app_kind)?
        .cloned()
        .ok_or_else(|| {
            Error::from(AppError::NotFound {
                input: input.to_owned(),
            })
        })
}

/// Opens what `request` names.
pub(crate) fn open(request: &OpenRequest) -> Result<Opened, Error> {
    if request.target.is_empty() || request.target.contains('\0') {
        return Err(AppError::Invalid.into());
    }
    let apps = platform::list_applications()?;
    match route(&apps, request, platform::OPENS_DOCUMENTS) {
        Route::Application => {
            let app = application(&apps, &request.target)?;
            platform::open_application(&app, request.activation)
        }
        Route::Document => {
            let app = match &request.document {
                DocumentRoute::App { app } => Some(application(&apps, app)?),
                DocumentRoute::Default | DocumentRoute::Reveal => None,
            };
            let how = match (&request.document, &app) {
                (DocumentRoute::Reveal, _) => Document::Reveal,
                (DocumentRoute::App { .. }, Some(app)) => Document::In(app),
                (DocumentRoute::Default | DocumentRoute::App { .. }, _) => Document::Default,
            };
            platform::open_document(&request.target, &how, request.activation)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn app(id: &str, name: &str, path: &str) -> Application {
        Application {
            id: id.to_owned(),
            name: name.to_owned(),
            path: PathBuf::from(path),
            state: AppState::NotRunning,
        }
    }

    #[test]
    fn a_name_shared_with_helpers_names_the_regular_app() {
        let apps = [
            app(
                "com.apple.AddressBook",
                "Contacts",
                "/System/Applications/Contacts.app",
            ),
            app(
                "com.apple.people",
                "Contacts",
                "/System/Library/PeopleViewService.appex",
            ),
        ];
        let kind = |app: &Application| {
            if is_app_bundle(&app.path) {
                AppKind::Regular
            } else {
                AppKind::Helper
            }
        };
        assert_eq!(resolve(&apps, "contacts", kind), Ok(Some(&apps[0])));
        assert_eq!(
            resolve(&apps, "contacts", |_| AppKind::Regular),
            Err(AppError::Ambiguous {
                input: "contacts".to_owned(),
                first: apps[0].path.clone(),
                second: apps[1].path.clone(),
            })
        );
    }

    #[test]
    fn urls_and_explicit_routes_open_as_documents() {
        let request = |target: &str, document| OpenRequest {
            target: target.to_owned(),
            activation: Activation::Background,
            document,
        };
        let apps = [app(
            "org.mozilla.firefox",
            "Firefox",
            "/usr/share/applications/firefox.desktop",
        )];
        assert_eq!(
            route(
                &apps,
                &request("https://eukhe.com", DocumentRoute::Default),
                Support::Supported
            ),
            Route::Document
        );
        assert_eq!(
            route(
                &apps,
                &request("org.mozilla.firefox", DocumentRoute::Default),
                Support::Supported
            ),
            Route::Application
        );
        assert_eq!(
            route(
                &apps,
                &request("C:\\x", DocumentRoute::Default),
                Support::Supported
            ),
            Route::Application
        );
        assert_eq!(
            route(
                &apps,
                &request("Firefox", DocumentRoute::Reveal),
                Support::Unsupported
            ),
            Route::Document
        );
    }
}
