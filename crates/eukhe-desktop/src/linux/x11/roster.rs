//! Every window the X server shows, popups and panels included (port of
//! omp `crates/natives/src/desktop/roster.rs`, its X11 part).

use x11rb::protocol::xproto::{ConnectionExt as _, MapState, WindowClass};

use super::{Kind, XError, XWindow, X11};
use crate::error::Error;
use crate::roster::{Listing, RosterWindow};

/// The layer a window of `kind` sits in, as the roster names layers.
fn layer(kind: Kind, override_redirect: bool) -> i32 {
    if override_redirect {
        return 101;
    }
    match kind {
        Kind::Desktop => -1,
        Kind::Normal | Kind::Dialog => 0,
        Kind::Utility | Kind::Toolbar | Kind::Splash => 3,
        Kind::Dock => 20,
        Kind::Menu | Kind::Tooltip | Kind::Notification | Kind::DragIcon => 101,
    }
}

/// Opacity from `_NET_WM_OPACITY`, where `0xffff_ffff` is opaque.
fn alpha(opacity: Option<u32>) -> f64 {
    opacity.map_or(1.0, |opacity| f64::from(opacity) / f64::from(u32::MAX))
}

/// Mapped top-level windows with a process, front to back. Windows naming
/// no process are left out.
pub(crate) fn window_roster() -> Result<Vec<RosterWindow>, Error> {
    let x = X11::open()?;
    let listed = x.windows()?;
    let tree = x
        .conn
        .query_tree(x.root)
        .map_err(XError::from)?
        .reply()
        .map_err(XError::from)?;
    Ok(tree
        .children
        .into_iter()
        .rev()
        .filter_map(|frame| {
            let frame = XWindow(frame);
            let attributes = x.conn.get_window_attributes(frame.0).ok()?.reply().ok()?;
            if attributes.map_state != MapState::VIEWABLE
                || attributes.class == WindowClass::INPUT_ONLY
            {
                return None;
            }
            let client = x.client_of(frame);
            let pid = x.pid(client)?;
            let placed = x.placed(client).ok()?;
            let id = client.id();
            let listing = if listed.iter().any(|window| window.id == id) {
                Listing::Listed
            } else {
                Listing::Unlisted
            };
            Some(RosterWindow {
                pid,
                app: x.app(client, Some(pid)),
                title: x.title(client),
                bounds: placed,
                layer: layer(x.kind(client), attributes.override_redirect),
                alpha: alpha(x.cardinal(client.0, x.atoms._NET_WM_WINDOW_OPACITY)),
                listing,
                id,
            })
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn popups_sit_above_panels_above_windows() {
        assert_eq!(layer(Kind::Normal, false), 0);
        assert_eq!(layer(Kind::Utility, false), 3);
        assert_eq!(layer(Kind::Normal, true), 101);
        assert!(alpha(Some(0)) < 0.01);
        assert!((alpha(None) - 1.0).abs() < f64::EPSILON);
    }
}
