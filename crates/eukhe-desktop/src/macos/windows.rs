//! The window list and the on-screen roster from the window server's
//! records (port of the listing in omp
//! `crates/natives/src/desktop/macos/capture.rs` and `roster.rs`).

use super::ffi::quartz::{Rect, WindowRecord};
use crate::geometry::GlobalRect;
use crate::roster::{Listing, RosterWindow};
use crate::types::{Focus, Pid, Window, WindowId};

/// Windows smaller than this on either side are never listed.
const MIN_WINDOW_EDGE: u32 = 16;

/// Whether capture is granted, which decides whether a record's sharing
/// state means anything: without it every window reads as unshared.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CaptureGrant {
    Granted,
    Denied,
}

/// A rectangle as whole logical points; `None` past `i32`/`u32`.
pub(super) fn global_rect(rect: Rect) -> Option<GlobalRect> {
    let whole = |value: f64, low: f64, high: f64| {
        let value = value.round();
        (value.is_finite() && value >= low && value <= high).then_some(value)
    };
    let x = whole(rect.x, f64::from(i32::MIN), f64::from(i32::MAX))?;
    let y = whole(rect.y, f64::from(i32::MIN), f64::from(i32::MAX))?;
    let width = whole(rect.width, 0.0, f64::from(u32::MAX))?;
    let height = whole(rect.height, 0.0, f64::from(u32::MAX))?;
    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "each value was rounded and checked to fit its type above"
    )]
    Some(GlobalRect {
        x: x as i32,
        y: y as i32,
        width: width as u32,
        height: height as u32,
    })
}

/// Whether a window list includes `record`: shared with capture, on screen,
/// at least [`MIN_WINDOW_EDGE`] on each side, and named.
pub(super) fn listed(record: &WindowRecord, grant: CaptureGrant) -> Option<GlobalRect> {
    let shared = match grant {
        CaptureGrant::Granted => !matches!(record.sharing, None | Some(0)),
        CaptureGrant::Denied => true,
    };
    let named = !matches!(
        (record.title.as_str(), record.owner.as_str()),
        ("", "") | ("StatusIndicator", "Window Server")
    );
    let bounds = global_rect(record.bounds)?;
    (shared
        && named
        && record.onscreen
        && bounds.width >= MIN_WINDOW_EDGE
        && bounds.height >= MIN_WINDOW_EDGE)
        .then_some(bounds)
}

/// The listed windows, front to back. The front app's focused window
/// (`ax_focused`, when listed) holds focus, else its frontmost window.
pub(super) fn windows(
    records: Vec<WindowRecord>,
    grant: CaptureGrant,
    front: Option<i32>,
    ax_focused: Option<u32>,
) -> Vec<Window> {
    let shown: Vec<(WindowRecord, GlobalRect)> = records
        .into_iter()
        .filter_map(|record| {
            let bounds = listed(&record, grant)?;
            Some((record, bounds))
        })
        .collect();
    let mut active = shown
        .iter()
        .filter(|(record, _)| Some(record.pid) == front)
        .map(|(record, _)| record.id);
    let focused = match ax_focused {
        Some(id) => active.find(|active| *active == id),
        None => active.next(),
    };
    shown
        .into_iter()
        .map(|(record, bounds)| Window {
            id: window_id(record.id),
            pid: u32::try_from(record.pid).ok().map(Pid),
            bounds,
            focus: if Some(record.id) == focused {
                Focus::Focused
            } else {
                Focus::Unfocused
            },
            title: record.title,
            app: record.owner,
        })
        .collect()
}

/// Every on-screen record as a roster row, front to back.
pub(super) fn roster(records: Vec<WindowRecord>, grant: CaptureGrant) -> Vec<RosterWindow> {
    records
        .into_iter()
        .filter(|record| record.onscreen)
        .filter_map(|record| {
            let listing = match listed(&record, grant) {
                Some(_) => Listing::Listed,
                None => Listing::Unlisted,
            };
            Some(RosterWindow {
                id: window_id(record.id),
                pid: Pid(u32::try_from(record.pid).ok()?),
                bounds: global_rect(record.bounds)?,
                layer: record.layer,
                alpha: record.alpha,
                listing,
                app: record.owner,
                title: record.title,
            })
        })
        .collect()
}

pub(super) fn window_id(id: u32) -> WindowId {
    WindowId::new(&id.to_string())
}

/// The window server id a listed window carries.
pub(super) fn server_id(window: &Window) -> Option<u32> {
    window.id.as_str().parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(id: u32, pid: i32, title: &str, owner: &str) -> WindowRecord {
        WindowRecord {
            id,
            pid,
            layer: 0,
            alpha: 1.0,
            onscreen: true,
            sharing: Some(1),
            bounds: Rect {
                x: 10.4,
                y: -20.6,
                width: 300.0,
                height: 200.0,
            },
            title: title.to_owned(),
            owner: owner.to_owned(),
        }
    }

    #[test]
    fn tiny_unnamed_unshared_and_offscreen_windows_stay_unlisted() {
        let mut tiny = record(1, 7, "a", "App");
        tiny.bounds.width = 10.0;
        let unnamed = record(2, 7, "", "");
        let indicator = record(3, 7, "StatusIndicator", "Window Server");
        let mut unshared = record(4, 7, "b", "App");
        unshared.sharing = Some(0);
        let mut hidden = record(5, 7, "c", "App");
        hidden.onscreen = false;
        for record in [&tiny, &unnamed, &indicator, &unshared, &hidden] {
            assert_eq!(listed(record, CaptureGrant::Granted), None, "{record:?}");
        }
        // Without capture every window reads unshared, so sharing says nothing.
        assert!(listed(&unshared, CaptureGrant::Denied).is_some());
        assert_eq!(
            listed(&record(6, 7, "d", "App"), CaptureGrant::Granted),
            Some(GlobalRect {
                x: 10,
                y: -21,
                width: 300,
                height: 200
            })
        );
    }

    #[test]
    fn the_front_apps_focused_window_holds_focus_else_its_frontmost() {
        let records = || {
            vec![
                record(1, 5, "other", "Other"),
                record(2, 7, "back", "App"),
                record(3, 7, "front", "App"),
            ]
        };
        let focused = |ax: Option<u32>| -> Vec<u32> {
            windows(records(), CaptureGrant::Granted, Some(7), ax)
                .iter()
                .filter(|window| window.focus == Focus::Focused)
                .filter_map(server_id)
                .collect()
        };
        assert_eq!(focused(Some(3)), [3]);
        assert_eq!(focused(None), [2]);
        // A focused window the list leaves out marks nothing.
        assert_eq!(focused(Some(9)), Vec::<u32>::new());
    }

    #[test]
    fn the_roster_keeps_unlisted_windows_and_marks_them() {
        let mut menu = record(4, 7, "", "");
        menu.layer = 101;
        let rows = roster(vec![record(1, 7, "a", "App"), menu], CaptureGrant::Granted);
        let marks: Vec<(i32, Listing)> = rows.iter().map(|row| (row.layer, row.listing)).collect();
        assert_eq!(marks, [(0, Listing::Listed), (101, Listing::Unlisted)]);
    }
}
