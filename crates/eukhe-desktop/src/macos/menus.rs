//! The menu bar through accessibility: listing a level, and pressing a
//! command with its window key inside its app (port of omp
//! `crates/natives/src/desktop/macos/ax/menus.rs`).

use std::time::Duration;

use super::ax;
use super::ffi::ax::{AxHandle, Names, Read, Value};
use super::ffi::quartz::Source;
use super::ffi::sky::Spi;
use super::guard;
use super::input::{self, Purpose, Target};
use crate::ax::Availability;
use crate::backend::Delivery;
use crate::control::Sent;
use crate::error::{Error, Refusal};
use crate::keys::{Chord, Key, Modifier, Modifiers};
use crate::menus::{self, Check, MenuError, MenuItem, Submenu};
use crate::types::{DeliveryMode, Window};

/// How long a command may take to read enabled once its window is key:
/// `AppKit` revalidates menus on its own schedule after an activation.
const SETTLE_TIMEOUT: Duration = Duration::from_millis(1500);
const SETTLE_POLL: Duration = Duration::from_millis(100);

const ITEM_ATTRIBUTES: [&str; 6] = [
    "AXTitle",
    "AXEnabled",
    "AXMenuItemMarkChar",
    "AXMenuItemCmdChar",
    "AXMenuItemCmdModifiers",
    "AXChildren",
];

/// One menu level: the item elements and what each reads as.
struct Level {
    elements: Vec<AxHandle>,
    items: Vec<MenuItem>,
}

/// The items of the menu `path` opens; `[]` is the menu bar.
pub(super) fn items(pid: i32, path: &[String]) -> Result<Vec<MenuItem>, Error> {
    Ok(level(pid, path)?.items)
}

fn level(pid: i32, path: &[String]) -> Result<Level, Error> {
    let names = Names::new(&ITEM_ATTRIBUTES);
    let bar = match ax::application(pid).read("AXMenuBar") {
        Ok(Some(Value::Element(bar))) => bar,
        Ok(_) => {
            return Err(Error::Refused(Refusal::Ax {
                detail: "the app shows no menu bar".into(),
            }))
        }
        Err(code) => return Err(ax::refused(code, "reading the menu bar")),
    };
    let mut current = describe(&names, children(&bar)?, &[]);
    let mut resolved: Vec<String> = Vec::with_capacity(path.len());
    for label in path {
        let index = menus::match_label(&current.items, label)?;
        let element = current.elements.swap_remove(index);
        resolved.push(current.items.swap_remove(index).title);
        let menu = children(&element)?.into_iter().next();
        let elements = match menu {
            Some(menu) => children(&menu)?,
            None => Vec::new(),
        };
        current = describe(&names, elements, &resolved);
    }
    Ok(current)
}

fn children(element: &AxHandle) -> Result<Vec<AxHandle>, Error> {
    match element.read("AXChildren") {
        Ok(Some(Value::Elements(children))) => Ok(children),
        Ok(_) => Ok(Vec::new()),
        Err(code) => Err(ax::refused(code, "reading a menu")),
    }
}

/// The named items of `elements`; separators drop out.
fn describe(names: &Names, elements: Vec<AxHandle>, path: &[String]) -> Level {
    let mut level = Level {
        elements: Vec::with_capacity(elements.len()),
        items: Vec::with_capacity(elements.len()),
    };
    for element in elements {
        let values = element.read_many(names);
        let Some(item) = item(&values, path) else {
            continue;
        };
        level.elements.push(element);
        level.items.push(item);
    }
    level
}

fn text(read: Option<&Read>) -> Option<&str> {
    match read {
        Some(Ok(Some(Value::Text(text)))) => Some(text),
        Some(Ok(_) | Err(_)) | None => None,
    }
}

fn item(values: &[Read], path: &[String]) -> Option<MenuItem> {
    let title = text(values.first()).filter(|title| !title.trim().is_empty())?;
    let mut item_path = Vec::with_capacity(path.len() + 1);
    item_path.extend_from_slice(path);
    item_path.push(title.to_owned());
    Some(MenuItem {
        title: title.to_owned(),
        path: item_path,
        availability: match values.get(1) {
            Some(Ok(Some(Value::Bool(false)))) => Availability::Disabled,
            Some(Ok(_) | Err(_)) | None => Availability::Enabled,
        },
        check: match text(values.get(2)) {
            Some(mark) if !mark.is_empty() => Check::Checked,
            Some(_) | None => Check::Unchecked,
        },
        submenu: match values.get(5) {
            Some(Ok(Some(Value::Elements(children)))) if !children.is_empty() => Submenu::Opens,
            Some(Ok(_) | Err(_)) | None => Submenu::Leaf,
        },
        shortcut: shortcut(text(values.get(3)), values.get(4)),
    })
}

/// `AXMenuItemCmdModifiers` bits: Shift 1, Option 2, Control 4, and 8 for
/// no Command.
fn shortcut(key: Option<&str>, modifiers: Option<&Read>) -> Option<String> {
    let mut characters = key?.chars();
    let character = characters.next()?.to_lowercase().next()?;
    if characters.next().is_some() || character.is_control() {
        return None;
    }
    let bits = match modifiers {
        Some(Ok(Some(Value::Int(bits)))) => *bits,
        Some(Ok(_) | Err(_)) | None => 0,
    };
    let held = [
        (1, Modifier::Shift),
        (2, Modifier::Alt),
        (4, Modifier::Ctrl),
    ]
    .into_iter()
    .filter(|(bit, _)| bits & bit != 0)
    .fold(Modifiers::NONE, |held, (_, modifier)| held.with(modifier));
    let held = if bits & 8 == 0 {
        held.with(Modifier::Meta)
    } else {
        held
    };
    Some(
        Chord {
            modifiers: held,
            key: Some(Key::Char(character)),
        }
        .to_string(),
    )
}

/// The element of the command `path` names (exact native titles).
fn command(pid: i32, path: &[String]) -> Result<(AxHandle, MenuItem), Error> {
    let (last, parents) = path.split_last().ok_or(MenuError::PathLength)?;
    let mut level = level(pid, parents)?;
    let index = menus::match_label(&level.items, last)?;
    Ok((
        level.elements.swap_remove(index),
        level.items.swap_remove(index),
    ))
}

/// Waits for a command `AppKit` shows disabled until it revalidates its
/// menus for the new key window.
fn enabled(element: &AxHandle, item: MenuItem) -> Result<(), Error> {
    let reads_enabled = || !matches!(element.read("AXEnabled"), Ok(Some(Value::Bool(false))));
    if guard::wait_for(SETTLE_TIMEOUT, SETTLE_POLL, reads_enabled) {
        return Ok(());
    }
    Err(MenuError::Disabled { path: item.path }.into())
}

fn perform(element: &AxHandle) -> Result<(), Error> {
    element
        .perform("AXPress")
        .map_err(|code| ax::after_send(code, "pressing the menu command"))
}

/// Presses the command `path` names for `window`: in the background its
/// window is made key inside its app first, as commands dispatch through
/// the key window.
pub(super) fn press(
    spi: &Spi,
    source: &Source,
    window: &Window,
    path: &[String],
    delivery: &Delivery<'_>,
) -> Result<(), Error> {
    let target = Target::of(window)?;
    match delivery.mode {
        DeliveryMode::Background => {
            if !spi.background_input() {
                return Err(Error::Refused(Refusal::BackgroundUnavailable {
                    detail: "the SkyLight input routes are unavailable".into(),
                }));
            }
            guard::watch(spi, target.pid, |visit| {
                let app = window.app.as_str();
                delivery.before_press(Sent::Nothing)?;
                guard::still_behind(spi, target.pid, app, visit, Sent::Nothing)?;
                input::make_key(spi, source, &target, Purpose::Menu)?;
                input::await_key_window(spi, &target)?;
                let (element, item) = command(target.pid, path)?;
                enabled(&element, item)?;
                delivery.before_press(Sent::Nothing)?;
                guard::still_behind(spi, target.pid, app, visit, Sent::Nothing)?;
                perform(&element)
            })
        }
        DeliveryMode::Takeover => input::takeover(spi, &target, delivery, |foreground| {
            let (element, item) = command(target.pid, path)?;
            enabled(&element, item)?;
            foreground.check(Sent::Nothing)?;
            perform(&element)
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(clippy::unnecessary_wraps, reason = "a read as the batch gives it")]
    fn text(text: &str) -> Read {
        Ok(Some(Value::Text(text.to_owned())))
    }

    #[test]
    fn an_item_reads_its_state_check_submenu_and_shortcut() {
        let values = [
            text("Save As…"),
            Ok(Some(Value::Bool(true))),
            text("✓"),
            text("S"),
            Ok(Some(Value::Int(1))),
            Ok(Some(Value::Elements(Vec::new()))),
        ];
        let item = item(&values, &["File".to_owned()]).unwrap_or_else(|| panic!("no item"));
        assert_eq!(item.path, ["File", "Save As…"]);
        assert_eq!(item.check, Check::Checked);
        assert_eq!(item.submenu, Submenu::Leaf);
        assert_eq!(item.shortcut.as_deref(), Some("shift+meta+s"));
    }

    #[test]
    fn a_separator_is_no_item_and_a_no_command_shortcut_drops_meta() {
        assert_eq!(item(&[text("")], &[]), None);
        assert_eq!(
            shortcut(Some("x"), Some(&Ok(Some(Value::Int(4 | 8))))).as_deref(),
            Some("ctrl+x")
        );
        assert_eq!(shortcut(Some("\u{8}"), None), None);
    }
}
