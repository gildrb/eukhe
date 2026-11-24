//! `NSWorkspace` and `NSRunningApplication`: running apps, bundles,
//! launching and activation (port of the `AppKit` calls of omp
//! `crates/natives/src/desktop/macos/applications.rs`).

use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::time::Duration;

use block2::RcBlock;
use objc2::rc::Retained;
use objc2::runtime::AnyObject;
use objc2_app_kit::{
    NSApplicationActivationPolicy, NSRunningApplication, NSWorkspace, NSWorkspaceOpenConfiguration,
};
use objc2_foundation::{NSArray, NSBundle, NSError, NSNumber, NSString, NSURL};

/// How an app shows itself, by its activation policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Policy {
    /// A Dock app with windows and a menu bar.
    Regular,
    /// No Dock icon; may show windows (menu-bar extras, agents).
    Accessory,
    /// Background only.
    Prohibited,
}

/// One running application.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RunningApp {
    pub(crate) pid: i32,
    pub(crate) name: Option<String>,
    pub(crate) bundle_id: Option<String>,
    pub(crate) path: Option<PathBuf>,
    pub(crate) policy: Policy,
}

/// What an app bundle's Info.plist says about it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BundleInfo {
    pub(crate) id: Option<String>,
    pub(crate) name: Option<String>,
    /// `LSUIElement` or `LSBackgroundOnly`: an agent or helper.
    pub(crate) agent: bool,
}

pub(crate) fn running_apps() -> Vec<RunningApp> {
    NSWorkspace::sharedWorkspace()
        .runningApplications()
        .iter()
        .map(|app| running(&app))
        .collect()
}

fn running(app: &NSRunningApplication) -> RunningApp {
    let policy = app.activationPolicy();
    RunningApp {
        pid: app.processIdentifier(),
        name: app.localizedName().map(|name| name.to_string()),
        bundle_id: app.bundleIdentifier().map(|id| id.to_string()),
        path: app.bundleURL().and_then(|url| url_path(&url)),
        policy: if policy == NSApplicationActivationPolicy::Regular {
            Policy::Regular
        } else if policy == NSApplicationActivationPolicy::Accessory {
            Policy::Accessory
        } else {
            Policy::Prohibited
        },
    }
}

/// The running app `pid`, if any.
pub(crate) fn app(pid: i32) -> Option<RunningApp> {
    NSRunningApplication::runningApplicationWithProcessIdentifier(pid).map(|app| running(&app))
}

pub(crate) fn frontmost_pid() -> Option<i32> {
    NSWorkspace::sharedWorkspace()
        .frontmostApplication()
        .map(|app| app.processIdentifier())
}

/// The Info.plist of the bundle at `path`.
pub(crate) fn bundle(path: &Path) -> Option<BundleInfo> {
    let bundle = NSBundle::bundleWithPath(&NSString::from_str(path.to_str()?))?;
    let info = bundle.infoDictionary();
    let entry = |key: &str| {
        info.as_ref()
            .and_then(|info| info.objectForKey(&NSString::from_str(key)))
    };
    let text = |key: &str| {
        entry(key)
            .and_then(|value| value.downcast::<NSString>().ok())
            .map(|value| value.to_string())
            .filter(|value| !value.is_empty())
    };
    Some(BundleInfo {
        id: bundle.bundleIdentifier().map(|id| id.to_string()),
        name: text("CFBundleDisplayName").or_else(|| text("CFBundleName")),
        agent: ["LSUIElement", "LSBackgroundOnly"]
            .into_iter()
            .any(|key| entry(key).is_some_and(|value| truthy(&value))),
    })
}

fn truthy(value: &AnyObject) -> bool {
    if let Some(number) = value.downcast_ref::<NSNumber>() {
        return number.boolValue();
    }
    value
        .downcast_ref::<NSString>()
        .is_some_and(NSString::boolValue)
}

/// Why a launch or open failed.
pub(crate) type OpenFailure = String;

/// How long a launch may take before the open counts as failed.
const OPEN_TIMEOUT: Duration = Duration::from_secs(15);

/// Launches or reopens the app at `path`; its pid once it runs.
pub(crate) fn open_app(path: &Path, activate: bool) -> Result<i32, OpenFailure> {
    let url = file_url(path)?;
    let configuration = configuration(activate);
    wait_opened(|handler| {
        NSWorkspace::sharedWorkspace().openApplicationAtURL_configuration_completionHandler(
            &url,
            &configuration,
            Some(handler),
        );
    })
}

/// Opens `target` (a path or URL) in its default app, or in the app at
/// `app`; the pid of the app that opened it.
pub(crate) fn open_document(
    target: &str,
    app: Option<&Path>,
    activate: bool,
) -> Result<i32, OpenFailure> {
    let url = document_url(target)?;
    let configuration = configuration(activate);
    match app {
        Some(app) => {
            let app = file_url(app)?;
            let urls = NSArray::from_retained_slice(&[url]);
            wait_opened(|handler| {
                NSWorkspace::sharedWorkspace()
                    .openURLs_withApplicationAtURL_configuration_completionHandler(
                        &urls,
                        &app,
                        &configuration,
                        Some(handler),
                    );
            })
        }
        None => wait_opened(|handler| {
            NSWorkspace::sharedWorkspace().openURL_configuration_completionHandler(
                &url,
                &configuration,
                Some(handler),
            );
        }),
    }
}

/// Selects `path` in Finder, which comes in front.
pub(crate) fn reveal(path: &Path) -> Result<(), OpenFailure> {
    let url = file_url(path)?;
    NSWorkspace::sharedWorkspace()
        .activateFileViewerSelectingURLs(&NSArray::from_retained_slice(&[url]));
    Ok(())
}

fn configuration(activate: bool) -> Retained<NSWorkspaceOpenConfiguration> {
    let configuration = NSWorkspaceOpenConfiguration::configuration();
    configuration.setActivates(activate);
    configuration.setPromptsUserIfNeeded(false);
    configuration.setAddsToRecentItems(false);
    configuration
}

type Handler = block2::DynBlock<dyn Fn(*mut NSRunningApplication, *mut NSError)>;

/// Runs `open` with a completion handler and waits for its answer.
fn wait_opened(open: impl FnOnce(&Handler)) -> Result<i32, OpenFailure> {
    let (sender, answer) = mpsc::sync_channel(1);
    let handler = RcBlock::new(move |app: *mut NSRunningApplication, error: *mut NSError| {
        // SAFETY: AppKit passes a live app or null, and a live error or null,
        // for the duration of the handler.
        let (app, error) = unsafe { (app.as_ref(), error.as_ref()) };
        let result = match (app, error) {
            (Some(app), None) => Ok(app.processIdentifier()),
            (_, Some(error)) => Err(error.localizedDescription().to_string()),
            (None, None) => Err("the open finished without an application".to_owned()),
        };
        sender.try_send(result).ok();
    });
    open(&handler);
    answer
        .recv_timeout(OPEN_TIMEOUT)
        .unwrap_or_else(|_| Err("the open did not finish in time".to_owned()))
}

fn file_url(path: &Path) -> Result<Retained<NSURL>, OpenFailure> {
    let text = path
        .to_str()
        .ok_or_else(|| format!("{} is not valid UTF-8", path.display()))?;
    Ok(NSURL::fileURLWithPath(&NSString::from_str(text)))
}

/// An existing path as a file URL, else a URL with a scheme.
fn document_url(target: &str) -> Result<Retained<NSURL>, OpenFailure> {
    let path = Path::new(target);
    if path.exists() {
        return file_url(path);
    }
    NSURL::URLWithString(&NSString::from_str(target))
        .ok_or_else(|| format!("{target:?} is neither an existing path nor a URL"))
}

fn url_path(url: &NSURL) -> Option<PathBuf> {
    url.path().map(|path| PathBuf::from(path.to_string()))
}
