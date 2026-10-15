//! The web app's files, embedded in the binary (plain HTML, CSS and JS:
//! no build step, no Node toolchain).

/// One embedded file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Asset {
    pub(crate) content_type: &'static str,
    pub(crate) body: &'static str,
}

const INDEX: Asset = Asset {
    content_type: "text/html; charset=utf-8",
    body: include_str!("../web/index.html"),
};

const STYLE: Asset = Asset {
    content_type: "text/css; charset=utf-8",
    body: include_str!("../web/app.css"),
};

const SCRIPT: Asset = Asset {
    content_type: "text/javascript; charset=utf-8",
    body: include_str!("../web/app.js"),
};

const ICON: Asset = Asset {
    content_type: "image/svg+xml",
    body: include_str!("../web/icon.svg"),
};

/// The file a request path names. The app may sit under a path prefix
/// (a forwarder that mounts it at `/eukhe/`), so the last segment
/// decides: every page refers to its files relatively.
pub(crate) fn lookup(path: &str) -> Option<Asset> {
    let name = path.rsplit('/').next().unwrap_or_default();
    match name {
        "" | "index.html" => Some(INDEX),
        "app.css" => Some(STYLE),
        "app.js" => Some(SCRIPT),
        "icon.svg" => Some(ICON),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn paths_resolve_by_their_last_segment() {
        assert_eq!(lookup("/"), Some(INDEX));
        assert_eq!(lookup("/eukhe/"), Some(INDEX));
        assert_eq!(lookup("/eukhe/app.js"), Some(SCRIPT));
        assert_eq!(lookup("/app.css"), Some(STYLE));
        assert_eq!(lookup("/icon.svg"), Some(ICON));
        assert_eq!(lookup("/eukhe"), None);
        assert_eq!(lookup("/secrets.txt"), None);
    }
}
