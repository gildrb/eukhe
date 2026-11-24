//! A window's menu bar read and pressed through AT-SPI, without opening any
//! popup (port of omp `crates/natives/src/desktop/linux/ax/menus.rs`).

use atspi::proxy::action::ActionProxyBlocking;
use atspi::State;

use super::{after_request, read, refused, A11y, AxHandle};
use crate::ax::Availability;
use crate::backend::Delivery;
use crate::control::Sent;
use crate::error::Error;
use crate::menus::{self, Check, MenuItem, Submenu};

const NODE_LIMIT: usize = 2048;
const DEPTH_LIMIT: usize = 32;

fn menu_role(role: atspi::Role) -> bool {
    matches!(
        role,
        atspi::Role::Menu
            | atspi::Role::MenuItem
            | atspi::Role::CheckMenuItem
            | atspi::Role::RadioMenuItem
    )
}

/// A submenu's container: GTK's `Menu`, and the `PopupMenu` a Qt menu bar
/// item holds its items in.
fn submenu_role(role: atspi::Role) -> bool {
    matches!(role, atspi::Role::Menu | atspi::Role::PopupMenu)
}

/// Chrome a menu bar sits in; anything else below the window is content.
fn container_role(role: atspi::Role) -> bool {
    matches!(
        role,
        atspi::Role::Panel | atspi::Role::Filler | atspi::Role::RootPane | atspi::Role::LayeredPane
    )
}

/// The items of the menu `path` leads to; `[]` lists the menu bar.
pub(in crate::linux) fn menu_items(
    a11y: &A11y,
    root: &AxHandle,
    path: &[String],
) -> Result<Vec<MenuItem>, Error> {
    let containers = if path.is_empty() {
        menu_bars(a11y, root)?
    } else {
        let (item, object) = resolve(a11y, root, path)?;
        match item.submenu {
            Submenu::Opens => vec![object],
            Submenu::Leaf => return Err(refused("the menu path ends at a command, not a submenu")),
        }
    };
    level(a11y, &containers, path).map(|(items, _)| items)
}

/// Presses the command `path` names.
pub(in crate::linux) fn menu_press(
    a11y: &A11y,
    root: &AxHandle,
    path: &[String],
    delivery: &Delivery<'_>,
) -> Result<(), Error> {
    let (item, object) = resolve(a11y, root, path)?;
    menus::require_command(&item)?;
    let action: ActionProxyBlocking<'_> = read(a11y.proxy(&object))?;
    let names = a11y.action_names(&object)?;
    let index = command_index(names.iter().map(String::as_str))
        .ok_or_else(|| refused("the menu command has no single declared activation action"))?;
    delivery.before_press(Sent::Nothing)?;
    match action.do_action(index) {
        Ok(true) => Ok(()),
        Ok(false) => Err(refused("the application refused the menu command")),
        Err(error) => Err(after_request(error.into())),
    }
}

fn command_index<'a>(names: impl Iterator<Item = &'a str>) -> Option<i32> {
    const COMMANDS: [&str; 7] = [
        "click", "press", "activate", "invoke", "toggle", "check", "uncheck",
    ];
    let mut candidates = names.enumerate().filter(|(_, name)| {
        COMMANDS
            .iter()
            .any(|command| name.eq_ignore_ascii_case(command))
    });
    match (candidates.next(), candidates.next()) {
        (Some((index, _)), None) => i32::try_from(index).ok(),
        (None, _) | (Some(_), Some(_)) => None,
    }
}

/// Children whose parent link names `object` back: a detached popup or
/// another frame's menu never becomes a command target.
fn menu_children(a11y: &A11y, object: &AxHandle) -> Result<Vec<AxHandle>, Error> {
    let proxy = a11y.accessible(object)?;
    let children = read(proxy.get_children())?;
    if children.len() > NODE_LIMIT {
        return Err(refused("the menu has more items than one read takes"));
    }
    children
        .iter()
        .map(|child| {
            let child = AxHandle::of(child)
                .filter(|child| child != object && child.bus == object.bus)
                .ok_or_else(|| refused("a menu child belongs to another application"))?;
            let parent = read(a11y.accessible(&child)?.parent())?;
            match AxHandle::of(&parent) {
                Some(parent) if parent == *object => Ok(child),
                Some(_) | None => Err(refused("a menu child names another parent")),
            }
        })
        .collect()
}

fn menu_bars(a11y: &A11y, root: &AxHandle) -> Result<Vec<AxHandle>, Error> {
    let mut pending = vec![(root.clone(), 0usize)];
    let mut seen: Vec<AxHandle> = Vec::new();
    let mut bars = Vec::new();
    while let Some((object, depth)) = pending.pop() {
        if depth > DEPTH_LIMIT || seen.len() >= NODE_LIMIT || seen.contains(&object) {
            return Err(refused("menu discovery passed its bounds or found a cycle"));
        }
        let role = read(a11y.accessible(&object)?.get_role())?;
        if role == atspi::Role::MenuBar {
            bars.push(object);
            continue;
        }
        // Menus are chrome: content and nested windows are not searched.
        if object != *root && !container_role(role) {
            seen.push(object);
            continue;
        }
        let children = menu_children(a11y, &object)?;
        seen.push(object);
        pending.extend(children.into_iter().rev().map(|child| (child, depth + 1)));
    }
    if bars.is_empty() {
        return Err(refused(
            "the window exposes no accessible menu bar; global or detached menus are not bound to it",
        ));
    }
    Ok(bars)
}

/// The items of `containers`, with the element of each.
fn level(
    a11y: &A11y,
    containers: &[AxHandle],
    path: &[String],
) -> Result<(Vec<MenuItem>, Vec<AxHandle>), Error> {
    let mut items = Vec::new();
    let mut objects = Vec::new();
    for container in containers {
        let owner = a11y.accessible(container)?;
        let owner_role = read(owner.get_role())?;
        let owner_name = read(owner.name())?;
        let children = menu_children(a11y, container)?;
        // Some toolkits wrap a submenu in one intermediate menu object.
        let inner = match children.as_slice() {
            [only] if owner_role != atspi::Role::MenuBar => unwrapped(a11y, only, &owner_name)?,
            _ => None,
        };
        let children = inner.unwrap_or(children);
        for object in children {
            if objects.len() >= NODE_LIMIT {
                return Err(refused("the menu has more items than one read takes"));
            }
            let proxy = a11y.accessible(&object)?;
            let role = read(proxy.get_role())?;
            if role == atspi::Role::Separator {
                continue;
            }
            if !menu_role(role) {
                return Err(refused("the menu holds a control that is no menu item"));
            }
            let title = read(proxy.name())?;
            let states = read(proxy.get_state())?;
            if states.contains(State::Defunct) {
                return Err(refused("a menu item is defunct"));
            }
            let mut opens = role == atspi::Role::Menu;
            for child in menu_children(a11y, &object)? {
                let child_role = read(a11y.accessible(&child)?.get_role())?;
                opens |= menu_role(child_role) || submenu_role(child_role);
            }
            let shortcut = read(a11y.proxy::<ActionProxyBlocking<'_>>(&object))
                .and_then(|action| read(action.get_key_binding(0)))
                .ok()
                .and_then(|binding| accelerator(&binding).map(str::to_owned));
            let mut item_path = Vec::with_capacity(path.len() + 1);
            item_path.extend_from_slice(path);
            item_path.push(title.clone());
            items.push(MenuItem {
                title,
                path: item_path,
                availability: if states.contains(State::Enabled)
                    || states.contains(State::Sensitive)
                {
                    Availability::Enabled
                } else {
                    Availability::Disabled
                },
                check: if states.contains(State::Checked) {
                    Check::Checked
                } else {
                    Check::Unchecked
                },
                submenu: if opens { Submenu::Opens } else { Submenu::Leaf },
                shortcut,
            });
            objects.push(object);
        }
    }
    if items.is_empty() {
        return Err(refused(
            "the menu's items are absent or unreadable without opening its popup",
        ));
    }
    Ok((items, objects))
}

/// The items inside `only` when it is a submenu wrapper: a menu without a
/// name of its own, or with its owner's.
fn unwrapped(
    a11y: &A11y,
    only: &AxHandle,
    owner_name: &str,
) -> Result<Option<Vec<AxHandle>>, Error> {
    let child = a11y.accessible(only)?;
    let name = read(child.name())?;
    if submenu_role(read(child.get_role())?) && (name.is_empty() || name == owner_name) {
        return menu_children(a11y, only).map(Some);
    }
    Ok(None)
}

/// The item `path` names and its element, matched level by level.
fn resolve(a11y: &A11y, root: &AxHandle, path: &[String]) -> Result<(MenuItem, AxHandle), Error> {
    let mut containers = menu_bars(a11y, root)?;
    let mut walked: Vec<String> = Vec::with_capacity(path.len());
    for (depth, label) in path.iter().enumerate() {
        let (mut items, mut objects) = level(a11y, &containers, &walked)?;
        let index = menus::match_label(&items, label)?;
        let item = items.swap_remove(index);
        let object = objects.swap_remove(index);
        if depth + 1 == path.len() {
            return Ok((item, object));
        }
        match (item.availability, item.submenu) {
            (Availability::Disabled, _) => {
                return Err(menus::MenuError::Disabled { path: item.path }.into());
            }
            (Availability::Enabled, Submenu::Leaf) => {
                return Err(refused(
                    "the menu path runs through a command, not a submenu",
                ));
            }
            (Availability::Enabled, Submenu::Opens) => {}
        }
        walked = item.path;
        containers = vec![object];
    }
    Err(refused("a menu path names at least one item"))
}

/// The accelerator of an ATK key binding `mnemonic;full mnemonic;accelerator`.
fn accelerator(binding: &str) -> Option<&str> {
    binding
        .split(';')
        .nth(2)
        .map(str::trim)
        .filter(|accelerator| !accelerator.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_command_has_exactly_one_declared_activation() {
        assert_eq!(command_index(std::iter::empty()), None);
        assert_eq!(command_index(["show", "open"].into_iter()), None);
        assert_eq!(command_index(["click", "activate"].into_iter()), None);
        assert_eq!(command_index(["show", "aCtIvAtE"].into_iter()), Some(1));
    }

    #[test]
    fn the_accelerator_is_the_third_field_of_a_key_binding() {
        assert_eq!(accelerator("o;<Alt>f:o;<Primary>o"), Some("<Primary>o"));
        assert_eq!(accelerator("o;<Alt>f:o;"), None);
        assert_eq!(accelerator(""), None);
    }
}
