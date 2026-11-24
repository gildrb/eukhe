//! Live test of the Linux backend against the GTK 3 fixture on a private
//! Xvfb display and AT-SPI bus; `tests/fixtures/run-linux-live.sh` sets
//! them up and runs it.
#![cfg(target_os = "linux")]

use std::thread;
use std::time::{Duration, Instant};

use eukhe_desktop::{
    ClickCount, Desktop, Done, Effect, ElementRef, FindQuery, FramePoint, ImageCaps, KeyTarget,
    MenuPath, Modifiers, MouseButton, ObserveOptions, PointTarget, SelectPart, SessionOptions,
    Step, Takeover, TextSelectRequest, TreeOptions, Window, WindowFilter, WindowSelector,
};

const TITLE: &str = "eukhe fixture";

fn fixture() -> WindowSelector {
    WindowSelector::Filter(WindowFilter {
        app: None,
        title: Some(TITLE.to_owned()),
    })
}

fn open() -> Desktop {
    let lock = std::env::temp_dir().join(format!("eukhe-desktop-live-{}.lock", std::process::id()));
    Desktop::open(SessionOptions {
        input_lock: lock,
        holder: "linux-live".to_owned(),
    })
    .unwrap_or_else(|error| panic!("the session opens: {error}"))
}

/// The fixture's window, once it shows.
fn fixture_window(desktop: &Desktop) -> Window {
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        match desktop.read().window(fixture()) {
            Ok(window) => return window,
            Err(error) if Instant::now() > deadline => panic!("no fixture window: {error}"),
            Err(_) => thread::sleep(Duration::from_millis(200)),
        }
    }
}

fn find(desktop: &Desktop, role: &str, title: Option<&str>) -> Vec<eukhe_desktop::FoundNode> {
    desktop
        .read()
        .find(
            fixture(),
            FindQuery {
                role: Some(role.to_owned()),
                title: title.map(str::to_owned),
                value: None,
                limit: None,
            },
        )
        .unwrap_or_else(|error| panic!("find {role} {title:?}: {error}"))
}

/// Waits until a label reading exactly `text` shows: the fixture's echo of
/// an effect.
fn shows(desktop: &Desktop, text: &str) {
    let deadline = Instant::now() + Duration::from_secs(5);
    while !find(desktop, "statictext", Some(text))
        .iter()
        .any(|label| label.title.as_deref() == Some(text))
    {
        assert!(
            Instant::now() < deadline,
            "the fixture never showed {text:?}"
        );
        thread::sleep(Duration::from_millis(100));
    }
}

fn confirmed(report: &eukhe_desktop::ActReport) {
    for effect in &report.steps {
        assert!(
            matches!(
                effect,
                Effect::Confirmed {
                    done: Done::Delivered
                }
            ),
            "step not confirmed: {effect:?}"
        );
    }
}

/// The fixture's screenshot and tree, checked.
fn observe_fixture(desktop: &Desktop, window: &Window) {
    let caps = ImageCaps {
        max_width: 4096.try_into().unwrap_or(std::num::NonZeroU32::MIN),
        max_height: 4096.try_into().unwrap_or(std::num::NonZeroU32::MIN),
    };
    let observed = desktop
        .read()
        .observe(
            fixture(),
            ObserveOptions {
                screenshot: Some(caps),
                tree: Some(TreeOptions::default()),
            },
        )
        .unwrap_or_else(|error| panic!("observe: {error}"));
    let screenshot = observed
        .screenshot
        .unwrap_or_else(|| panic!("a screenshot"));
    assert_eq!(
        (screenshot.size.width, screenshot.size.height),
        (window.bounds.width, window.bounds.height)
    );
    assert!(screenshot.png.starts_with(b"\x89PNG"));
    let tree = observed.tree.unwrap_or_else(|| panic!("a tree"));
    println!("{}", tree.text);
    assert!(
        tree.text.contains("button \"Press me\" [ref=e"),
        "{}",
        tree.text
    );
    assert!(tree.text.contains("textfield [ref=e"), "{}", tree.text);
}

fn act(desktop: &Desktop, steps: Vec<Step>) -> eukhe_desktop::ActReport {
    act_with(desktop, Takeover::Refuse, steps)
}

fn act_with(desktop: &Desktop, takeover: Takeover, steps: Vec<Step>) -> eukhe_desktop::ActReport {
    desktop
        .exec(takeover)
        .act(fixture(), steps)
        .unwrap_or_else(|error| panic!("act: {error}"))
}

fn select(desktop: &Desktop, entry: ElementRef, text: &str, part: SelectPart) -> Effect {
    let mut report = act(
        desktop,
        vec![Step::SelectText {
            target: entry,
            request: TextSelectRequest {
                text: text.to_owned(),
                prefix: String::new(),
                suffix: String::new(),
                part,
            },
        }],
    );
    report.steps.pop().unwrap_or_else(|| panic!("no effect"))
}

/// Writes, selects in and types into the entry, all through AT-SPI.
fn edit_entry(desktop: &Desktop, entry: ElementRef) {
    confirmed(&act(
        desktop,
        vec![Step::SetValue {
            target: entry,
            value: "hello".to_owned(),
        }],
    ));
    shows(desktop, "entry hello");

    match select(desktop, entry, "ell", SelectPart::Text) {
        Effect::Confirmed {
            done: Done::Selected { selection },
        } => assert_eq!(
            (selection.start, selection.length, selection.text.as_str()),
            (1, 3, "ell")
        ),
        other => panic!("selection not confirmed: {other:?}"),
    }
    let caret = select(desktop, entry, "hello", SelectPart::End);
    assert!(matches!(caret, Effect::Confirmed { .. }), "{caret:?}");

    // Background text goes in at the caret, without keys or focus.
    confirmed(&act(
        desktop,
        vec![Step::Type {
            text: " world".to_owned(),
            into: KeyTarget::Element(entry),
        }],
    ));
    shows(desktop, "entry hello world");
}

/// Reads the menu bar and a menu without opening a popup, then runs a
/// command.
fn run_menu(desktop: &Desktop) {
    let titles = |path: Vec<String>| -> Vec<String> {
        desktop
            .read()
            .menu_items(fixture(), path)
            .unwrap_or_else(|error| panic!("menu: {error}"))
            .into_iter()
            .map(|item| item.title)
            .collect()
    };
    assert_eq!(titles(Vec::new()), ["File"]);
    assert_eq!(titles(vec!["File".to_owned()]), ["Open…", "Wrap"]);
    let path = MenuPath::try_from(vec!["File".to_owned(), "Open".to_owned()])
        .unwrap_or_else(|error| panic!("menu path: {error}"));
    confirmed(&act(desktop, vec![Step::Menu { path }]));
    shows(desktop, "menu Open");
}

#[test]
#[ignore = "needs Xvfb, an AT-SPI bus and the GTK 3 fixture: run tests/fixtures/run-linux-live.sh"]
fn the_fixture_is_listed_read_captured_and_driven() {
    let desktop = open();
    let window = fixture_window(&desktop);
    assert!(window.pid.is_some(), "the fixture names its process");
    let roster = desktop
        .read()
        .roster()
        .unwrap_or_else(|error| panic!("roster: {error}"));
    assert!(roster.iter().any(|entry| entry.id == window.id));
    observe_fixture(&desktop, &window);

    let button = find(&desktop, "button", Some("Press me"))
        .pop()
        .unwrap_or_else(|| panic!("the button"));
    let entry = find(&desktop, "textfield", None)
        .pop()
        .unwrap_or_else(|| panic!("the entry"));

    // The button's own action, through AT-SPI.
    confirmed(&act(
        &desktop,
        vec![Step::Press {
            target: button.reference,
        }],
    ));
    shows(&desktop, "clicks 1");

    edit_entry(&desktop, entry.reference);

    // A background click on a pixel of the last screenshot, through the
    // session's own pointer.
    click(&desktop, &window, &button);
    shows(&desktop, "clicks 2");

    // Background keys through the session's own keyboard into the entry
    // its click focused: a shifted key, and one the layout lacks.
    click(&desktop, &window, &entry);
    confirmed(&act(
        &desktop,
        vec![Step::Type {
            text: "!é".to_owned(),
            into: KeyTarget::Focused,
        }],
    ));
    shows(&desktop, "entry hello world!é");

    // A key for an element without keyboard focus has no background route;
    // the takeover policy reruns it in the foreground.
    click(&desktop, &window, &button);
    shows(&desktop, "clicks 3");
    let backspace = || {
        vec![Step::Key {
            chord: "backspace"
                .parse()
                .unwrap_or_else(|error| panic!("{error}")),
            into: KeyTarget::Element(entry.reference),
        }]
    };
    let refused = act(&desktop, backspace());
    assert!(
        matches!(
            refused.steps.as_slice(),
            [Effect::Refused {
                reason: eukhe_desktop::Refusal::BackgroundUnavailable { .. }
            }]
        ),
        "{refused:?}"
    );
    confirmed(&act_with(&desktop, Takeover::Fallback, backspace()));
    shows(&desktop, "entry hello world!");

    run_menu(&desktop);
    desktop
        .close()
        .unwrap_or_else(|error| panic!("close: {error}"));
}

/// Clicks the center of `node` as a pixel of the window's last screenshot.
fn click(desktop: &Desktop, window: &Window, node: &eukhe_desktop::FoundNode) {
    let center = node
        .bounds
        .unwrap_or_else(|| panic!("bounds of {}", node.reference))
        .center();
    let pixel = FramePoint {
        x: center.x - f64::from(window.bounds.x),
        y: center.y - f64::from(window.bounds.y),
    };
    confirmed(&act(
        desktop,
        vec![Step::Click {
            at: PointTarget::Pixel(pixel),
            button: MouseButton::Left,
            count: ClickCount::SINGLE,
            modifiers: Modifiers::NONE,
        }],
    ));
}
