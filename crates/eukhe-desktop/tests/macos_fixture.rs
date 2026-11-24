//! Live test of the macOS backend against a fixture app this test builds
//! and launches (`tests/fixtures/macos_fixture.m`), and no other app: every
//! step goes to the fixture window in the background, under
//! `Takeover::Refuse`.
#![cfg(target_os = "macos")]

use std::fs;
use std::io::{BufRead, BufReader};
use std::num::NonZeroU32;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use eukhe_desktop::{
    Access, ActReport, Desktop, Effect, FindQuery, Focus, FoundNode, ImageCaps, ObserveOptions,
    SessionOptions, Step, Takeover, TreeOptions, WindowFilter, WindowId, WindowSelector,
};
use serde_json::json;

/// The fixture's process name, which the window list shows as its app.
const APP: &str = "eukhe-desktop-fixture";
const WAIT: Duration = Duration::from_secs(5);

/// The launched fixture; killed when dropped.
struct Fixture {
    child: Child,
    window: WindowId,
}

impl Drop for Fixture {
    fn drop(&mut self) {
        self.child.kill().ok();
        self.child.wait().ok();
    }
}

fn scratch() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("eukhe-desktop-live-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap_or_else(|error| panic!("{}: {error}", dir.display()));
    dir
}

fn launch(dir: &Path) -> Fixture {
    let binary = dir.join(APP);
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/macos_fixture.m");
    let built = Command::new("xcrun")
        .args(["clang", "-fobjc-arc", "-framework", "AppKit", "-o"])
        .arg(&binary)
        .arg(&source)
        .status()
        .unwrap_or_else(|error| panic!("xcrun clang: {error}"));
    assert!(built.success(), "the fixture did not build");
    let mut child = Command::new(&binary)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap_or_else(|error| panic!("{}: {error}", binary.display()));
    let mut line = String::new();
    if let Some(stdout) = child.stdout.take() {
        BufReader::new(stdout).read_line(&mut line).ok();
    }
    let number = line.trim().strip_prefix("ready ").map(str::to_owned);
    let fixture = Fixture {
        child,
        window: WindowId::new(number.as_deref().unwrap_or_default()),
    };
    assert!(number.is_some(), "the fixture did not start: {line:?}");
    fixture
}

/// Polls `read` until it gives a value, at most [`WAIT`].
fn wait_for<T>(mut read: impl FnMut() -> Option<T>) -> Option<T> {
    let deadline = Instant::now() + WAIT;
    loop {
        if let Some(value) = read() {
            return Some(value);
        }
        if Instant::now() >= deadline {
            return None;
        }
        thread::sleep(Duration::from_millis(100));
    }
}

fn query(role: Option<&str>, title: Option<&str>, value: Option<&str>) -> FindQuery {
    FindQuery {
        role: role.map(str::to_owned),
        title: title.map(str::to_owned),
        value: value.map(str::to_owned),
        limit: None,
    }
}

fn confirmed(report: &ActReport) -> bool {
    report
        .steps
        .iter()
        .all(|effect| matches!(effect, Effect::Confirmed { .. }))
}

fn steps(steps: serde_json::Value) -> Vec<Step> {
    serde_json::from_value(steps).unwrap_or_else(|error| panic!("{error}"))
}

fn permission(name: &str) -> String {
    format!(
        "{name} is not granted. macOS charges it to the app that launched this test \
         (the terminal or IDE running cargo, or the test binary {} when none did): enable \
         it in System Settings > Privacy & Security > {name}",
        std::env::current_exe().map_or_else(|_| "?".into(), |path| path.display().to_string())
    )
}

#[test]
#[ignore = "needs a logged-in macOS desktop, Xcode's clang, and Accessibility (Screen Recording for the screenshot) for the app running the tests; run with --ignored"]
#[allow(
    clippy::too_many_lines,
    reason = "one fixture launch drives every step in order"
)]
fn the_backend_drives_the_fixture_window_in_the_background() {
    let dir = scratch();
    let desktop = Desktop::open(SessionOptions {
        input_lock: dir.join("input.lock"),
        holder: "eukhe-desktop live test".to_owned(),
    })
    .unwrap_or_else(|error| panic!("{error}"));
    let read = desktop.read();
    let capabilities = read
        .capabilities()
        .unwrap_or_else(|error| panic!("{error}"));
    println!("{capabilities:?}");
    assert_eq!(
        capabilities.accessibility,
        Access::Granted,
        "{}",
        permission("Accessibility")
    );

    let fixture = launch(&dir);
    let selector = || WindowSelector::Id(fixture.window.clone());
    let focused_before = read
        .windows(WindowFilter::default())
        .unwrap_or_default()
        .into_iter()
        .find(|window| window.focus == Focus::Focused)
        .map(|window| window.id);

    // Listed, under its process name.
    let window = wait_for(|| read.window(selector()).ok())
        .unwrap_or_else(|| panic!("the fixture window {} is not listed", fixture.window));
    assert_eq!(window.app, APP);

    // Observed: the tree carries refs; the screenshot is a PNG.
    let observation = read
        .observe(
            selector(),
            ObserveOptions {
                screenshot: (capabilities.capture == Access::Granted).then_some(ImageCaps {
                    max_width: NonZeroU32::new(1280).unwrap_or(NonZeroU32::MIN),
                    max_height: NonZeroU32::new(896).unwrap_or(NonZeroU32::MIN),
                }),
                tree: Some(TreeOptions::default()),
            },
        )
        .unwrap_or_else(|error| panic!("{error}"));
    let tree = observation.tree.unwrap_or_else(|| panic!("no tree"));
    println!("{}", tree.text);
    assert!(tree.text.contains("Press Me") && tree.text.contains("[ref=e"));
    match observation.screenshot {
        Some(screenshot) => assert!(screenshot.png.starts_with(b"\x89PNG")),
        None => println!("{}", permission("Screen Recording")),
    }

    let find = |query: FindQuery| -> Vec<FoundNode> {
        read.find(selector(), query)
            .unwrap_or_else(|error| panic!("{error}"))
    };
    let button = find(query(Some("button"), Some("Press Me"), None))
        .first()
        .map_or_else(|| panic!("no button"), |node| node.reference);
    let field = find(query(Some("textfield"), None, None))
        .first()
        .map_or_else(|| panic!("no text field"), |node| node.reference);
    let status = |text: &str| {
        wait_for(|| (!find(query(None, None, Some(text))).is_empty()).then_some(())).is_some()
    };
    let exec = desktop.exec(Takeover::Refuse);
    let act = |list: serde_json::Value| -> ActReport {
        let report = exec
            .act(selector(), steps(list))
            .unwrap_or_else(|error| panic!("{error}"));
        println!("{report:?}");
        report
    };

    // Pressed and written in the background, then read back.
    let report = act(json!([
        {"type": "press", "target": button},
        {"type": "set_value", "target": field, "value": "hello"},
    ]));
    assert!(confirmed(&report), "{report:?}");
    assert!(status("Pressed 1"), "the press did not land");
    assert!(
        !find(query(Some("textfield"), None, Some("hello"))).is_empty(),
        "the field does not read the written value"
    );

    // Typed into the field: AX insertion at its selection.
    let report = act(json!([{"type": "type", "text": " world", "into": field}]));
    assert!(confirmed(&report), "{report:?}");

    // The menu bar, read and pressed with the window made key in its app.
    let items = read
        .menu_items(selector(), vec!["Fixture".to_owned()])
        .unwrap_or_else(|error| panic!("{error}"));
    assert!(items.iter().any(|item| item.title == "Mark"), "{items:?}");
    let report = act(json!([{"type": "menu", "path": ["Fixture", "Mark"]}]));
    assert!(confirmed(&report), "{report:?}");
    assert!(status("Marked"), "the menu command did not run");

    // A background click on the button's center, through SkyLight.
    let report = act(json!([{"type": "click", "at": button}]));
    assert!(confirmed(&report), "{report:?}");
    assert!(status("Pressed 2"), "the click did not land");

    // The user's focus never moved, and the fixture never took the front.
    let fixture_window = read
        .window(selector())
        .unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(fixture_window.focus, Focus::Unfocused);
    let focused_after = read
        .windows(WindowFilter::default())
        .unwrap_or_default()
        .into_iter()
        .find(|window| window.focus == Focus::Focused)
        .map(|window| window.id);
    assert_eq!(focused_before, focused_after);

    drop(fixture);
    desktop.close().unwrap_or_else(|error| panic!("{error}"));
    fs::remove_dir_all(&dir).ok();
}
