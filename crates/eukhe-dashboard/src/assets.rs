//! The web app's files, embedded in the binary (plain HTML, CSS, JS,
//! fonts and icons: no build step, no Node toolchain). `build.rs`
//! generates the table from every file under `web/`.

/// One embedded file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Asset {
    /// The path under `web/`, `/`-separated.
    pub(crate) path: &'static str,
    pub(crate) content_type: &'static str,
    /// The quoted entity tag: a hash of the path and the bytes.
    pub(crate) etag: &'static str,
    pub(crate) body: &'static [u8],
}

include!(concat!(env!("OUT_DIR"), "/web_assets.rs"));

/// The file a request path names. The app may sit under a path prefix
/// (a forwarder that mounts it at `/eukhe/`), and every page refers to
/// its files relatively, so the longest embedded path that ends the
/// request path at a segment boundary decides (`/eukhe/js/pages/turn.js`
/// is `js/pages/turn.js`, never `js/turn.js`). A path that ends in `/`
/// names `index.html`.
pub(crate) fn lookup(path: &str) -> Option<Asset> {
    let path = if path.ends_with('/') {
        "/index.html"
    } else {
        path
    };
    FILES
        .iter()
        .filter(|asset| {
            path.strip_suffix(asset.path)
                .is_some_and(|prefix| prefix.ends_with('/'))
        })
        .max_by_key(|asset| asset.path.len())
        .copied()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn named(path: &str) -> Asset {
        *FILES
            .iter()
            .find(|asset| asset.path == path)
            .expect("an embedded file")
    }

    #[test]
    fn paths_resolve_by_their_longest_embedded_suffix() {
        let index = named("index.html");
        assert_eq!(lookup("/"), Some(index));
        assert_eq!(lookup("/eukhe/"), Some(index));
        assert_eq!(lookup("/eukhe/index.html"), Some(index));
        assert_eq!(lookup("/eukhe/icon.svg"), Some(named("icon.svg")));
        assert_eq!(
            lookup("/eukhe/fonts/inter.woff2"),
            Some(named("fonts/inter.woff2"))
        );
        assert_eq!(lookup("/eukhe"), None);
        assert_eq!(lookup("/secrets.txt"), None);
        // A segment boundary: `xicon.svg` is not `icon.svg`.
        assert_eq!(lookup("/xicon.svg"), None);
    }

    #[test]
    fn nested_files_win_over_shorter_names() {
        let nested: Vec<Asset> = FILES
            .iter()
            .copied()
            .filter(|asset| asset.path.contains('/'))
            .collect();
        assert!(!nested.is_empty());
        for asset in nested {
            assert_eq!(lookup(&format!("/prefix/{}", asset.path)), Some(asset));
        }
    }
}
