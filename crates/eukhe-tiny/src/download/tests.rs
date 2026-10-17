use std::collections::HashMap;
use std::path::Path;

use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

use super::*;
use crate::catalog::files_state;

const MODEL_ID: &str = "test-model";

/// One response of the mock server.
struct Route {
    body: Vec<u8>,
    /// The `Content-Length` it declares; more than `body` cuts it short.
    declared: usize,
    /// Runs before the response goes out.
    before: Option<Box<dyn Fn() + Send + Sync>>,
}

impl Route {
    fn whole(body: &[u8]) -> Route {
        Route {
            body: body.to_vec(),
            declared: body.len(),
            before: None,
        }
    }
}

/// Serves `routes` by path on a loopback port (404 otherwise), one request
/// per connection; returns the base URL.
async fn serve(routes: HashMap<String, Route>) -> String {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let base = format!("http://{}", listener.local_addr().unwrap());
    let routes = std::sync::Arc::new(routes);
    tokio::spawn(async move {
        loop {
            let (mut socket, _) = listener.accept().await.unwrap();
            let routes = routes.clone();
            tokio::spawn(async move {
                let mut head = Vec::new();
                let mut buf = [0u8; 1024];
                while !head.windows(4).any(|window| window == b"\r\n\r\n") {
                    let read = socket.read(&mut buf).await.unwrap();
                    assert_ne!(read, 0, "request head cut short");
                    head.extend_from_slice(&buf[..read]);
                }
                let head = String::from_utf8(head).unwrap();
                let path = head.split(' ').nth(1).unwrap();
                let response = match routes.get(path) {
                    Some(route) => {
                        if let Some(before) = &route.before {
                            before();
                        }
                        let mut response = format!(
                            "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                            route.declared
                        )
                        .into_bytes();
                        response.extend_from_slice(&route.body);
                        response
                    }
                    None => {
                        b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
                            .to_vec()
                    }
                };
                // The client may hang up first (it rejects an overlong body).
                if socket.write_all(&response).await.is_ok() {
                    socket.shutdown().await.ok();
                }
            });
        }
    });
    base
}

fn sha256_hex(body: &[u8]) -> String {
    format!("{:x}", Sha256::digest(body))
}

const CONFIG: &[u8] = br#"{"model_type":"test"}"#;
const CONFIG_SHA256: &str = "69e683f430bd66f59c9ef0f4931624f59db5c3246a40a7c6ceffa4661a36d24c";
/// Large enough to arrive in several chunks.
static WEIGHTS: [u8; 300_000] = [7; 300_000];
const WEIGHTS_SHA256: &str = "08f166476de183f7a1b2874d544d37912aaf8d19b92013e1aafe233ba231024a";
const LEXICON: &[u8] = br#"{"hello":"h@lO"}"#;
const LEXICON_SHA256: &str = "543fe368f34077947b05b7abae66b8a21abad1461b6f7dc796e16c2ea78ef779";
/// The sha256 of none of the bodies.
const OTHER_SHA256: &str = "d9298a10d1b0735837dc4bd85dac641b0f3cef27a47e5d53a54f2f3f5b2fcffa";

const REVISION: &str = "0123456789abcdef0123456789abcdef01234567";
const REVISION_PATH: &str = "resolve/0123456789abcdef0123456789abcdef01234567";

/// The test model: two model files (one in a subdir) and a dataset file.
fn good_files() -> [ModelFile; 3] {
    [
        ModelFile {
            repo: "test/model",
            repo_kind: RepoKind::Model,
            revision: REVISION,
            path: "config.json",
            size: CONFIG.len() as u64,
            sha256: CONFIG_SHA256,
        },
        ModelFile {
            repo: "test/model",
            repo_kind: RepoKind::Model,
            revision: REVISION,
            path: "onnx/model.onnx",
            size: WEIGHTS.len() as u64,
            sha256: WEIGHTS_SHA256,
        },
        ModelFile {
            repo: "test/lexicon",
            repo_kind: RepoKind::Dataset,
            revision: REVISION,
            path: "us_gold.json",
            size: LEXICON.len() as u64,
            sha256: LEXICON_SHA256,
        },
    ]
}

fn good_routes() -> HashMap<String, Route> {
    HashMap::from([
        (
            format!("/test/model/{REVISION_PATH}/config.json"),
            Route::whole(CONFIG),
        ),
        (
            format!("/test/model/{REVISION_PATH}/onnx/model.onnx"),
            Route::whole(&WEIGHTS),
        ),
        (
            format!("/datasets/test/lexicon/{REVISION_PATH}/us_gold.json"),
            Route::whole(LEXICON),
        ),
    ])
}

/// Every regular file under `dir`, relative, sorted, with its contents.
fn tree(dir: &Path) -> Vec<(String, Vec<u8>)> {
    fn walk(root: &Path, dir: &Path, out: &mut Vec<(String, Vec<u8>)>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                walk(root, &path, out);
            } else {
                let relative = path
                    .strip_prefix(root)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned();
                out.push((relative, std::fs::read(&path).unwrap()));
            }
        }
    }
    let mut out = Vec::new();
    walk(dir, dir, &mut out);
    out.sort();
    out
}

fn installed_tree() -> Vec<(String, Vec<u8>)> {
    vec![
        ("config.json".to_owned(), CONFIG.to_vec()),
        ("onnx/model.onnx".to_owned(), WEIGHTS.to_vec()),
        ("us_gold.json".to_owned(), LEXICON.to_vec()),
    ]
}

/// The top-level entries of the models dir (staging dirs included).
fn models_entries(home: &TinyHome) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(&home.models)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    names
}

async fn fetch_quietly(
    home: &TinyHome,
    files: &[ModelFile],
    base: &str,
) -> Result<Downloaded, DownloadError> {
    download_files(home, MODEL_ID, files, base, &mut |_| {}).await
}

fn state(home: &TinyHome, files: &[ModelFile]) -> InstallState {
    files_state(&home.model_dir(MODEL_ID), files)
}

#[tokio::test]
async fn good_download_installs_every_file_verified() {
    let temp = tempfile::tempdir().unwrap();
    let home = TinyHome::under(temp.path());
    let files = good_files();
    let base = serve(good_routes()).await;

    let mut verified = Vec::new();
    let mut last_receiving = HashMap::new();
    let outcome = download_files(&home, MODEL_ID, &files, &base, &mut |event| match event {
        Progress::Receiving {
            file,
            received,
            total,
        } => {
            last_receiving.insert(file, (received, total));
        }
        Progress::Verified { file, sha256 } => verified.push((file, sha256)),
    })
    .await
    .unwrap();

    assert_eq!(outcome, Downloaded::Installed);
    assert_eq!(state(&home, &files), InstallState::Installed);
    assert_eq!(models_entries(&home), vec![MODEL_ID.to_owned()]);
    assert_eq!(tree(&home.model_dir(MODEL_ID)), installed_tree());
    assert_eq!(
        verified,
        vec![
            ("config.json", CONFIG_SHA256),
            ("onnx/model.onnx", WEIGHTS_SHA256),
            ("us_gold.json", LEXICON_SHA256),
        ]
    );
    assert_eq!(
        last_receiving,
        HashMap::from([
            ("config.json", (CONFIG.len() as u64, CONFIG.len() as u64)),
            (
                "onnx/model.onnx",
                (WEIGHTS.len() as u64, WEIGHTS.len() as u64)
            ),
            ("us_gold.json", (LEXICON.len() as u64, LEXICON.len() as u64)),
        ])
    );

    // Installed: skipped without a request (nothing listens on port 9).
    let again = fetch_quietly(&home, &files, "http://127.0.0.1:9")
        .await
        .unwrap();
    assert_eq!(again, Downloaded::AlreadyInstalled);
}

#[tokio::test]
async fn checksum_mismatch_installs_nothing() {
    let temp = tempfile::tempdir().unwrap();
    let home = TinyHome::under(temp.path());
    let mut files = good_files();
    files[1].sha256 = OTHER_SHA256;
    let base = serve(good_routes()).await;

    let error = fetch_quietly(&home, &files, &base).await.unwrap_err();

    let DownloadError::Checksum {
        file,
        expected,
        actual,
    } = error
    else {
        panic!("expected a checksum error, got {error:?}");
    };
    assert_eq!(
        (file, expected, actual),
        ("onnx/model.onnx", OTHER_SHA256, sha256_hex(&WEIGHTS))
    );
    assert_eq!(models_entries(&home), Vec::<String>::new());
    assert_eq!(state(&home, &files), InstallState::Missing);
}

/// A staging dir that cannot be removed after a failed download leaves the
/// download's own error as the result (the cleanup failure is logged).
#[tokio::test]
async fn a_failed_cleanup_keeps_the_download_error() {
    use std::os::unix::fs::PermissionsExt;

    let temp = tempfile::tempdir().unwrap();
    let home = TinyHome::under(temp.path());
    let mut files = good_files();
    files[2].sha256 = OTHER_SHA256;
    let mut routes = good_routes();
    let models = home.models.clone();
    // While the last file downloads, the models dir stops taking removals:
    // the staging dir in it cannot go.
    routes.insert(
        format!("/datasets/test/lexicon/{REVISION_PATH}/us_gold.json"),
        Route {
            before: Some(Box::new(move || {
                std::fs::set_permissions(&models, std::fs::Permissions::from_mode(0o500)).unwrap();
            })),
            ..Route::whole(LEXICON)
        },
    );
    let base = serve(routes).await;

    let result = fetch_quietly(&home, &files, &base).await;
    std::fs::set_permissions(&home.models, std::fs::Permissions::from_mode(0o700)).unwrap();

    let error = result.unwrap_err();
    let DownloadError::Checksum {
        file,
        expected,
        actual,
    } = error
    else {
        panic!("expected a checksum error, got {error:?}");
    };
    assert_eq!(
        (file, expected, actual, models_entries(&home)),
        (
            "us_gold.json",
            OTHER_SHA256,
            sha256_hex(LEXICON),
            vec![format!(".staging-{MODEL_ID}-{}", std::process::id())]
        )
    );
}

#[tokio::test]
async fn shorter_body_is_rejected() {
    let temp = tempfile::tempdir().unwrap();
    let home = TinyHome::under(temp.path());
    let mut routes = good_routes();
    routes.insert(
        format!("/test/model/{REVISION_PATH}/config.json"),
        Route::whole(&CONFIG[..5]),
    );
    let base = serve(routes).await;

    let error = fetch_quietly(&home, &good_files(), &base)
        .await
        .unwrap_err();

    let DownloadError::Size {
        file,
        expected,
        actual,
    } = error
    else {
        panic!("expected a size error, got {error:?}");
    };
    assert_eq!(
        (file, expected, actual),
        ("config.json", CONFIG.len() as u64, 5)
    );
    assert_eq!(models_entries(&home), Vec::<String>::new());
}

#[tokio::test]
async fn longer_body_is_rejected() {
    let temp = tempfile::tempdir().unwrap();
    let home = TinyHome::under(temp.path());
    let mut routes = good_routes();
    let long = [LEXICON, b"extra"].concat();
    routes.insert(
        format!("/datasets/test/lexicon/{REVISION_PATH}/us_gold.json"),
        Route::whole(&long),
    );
    let base = serve(routes).await;

    let error = fetch_quietly(&home, &good_files(), &base)
        .await
        .unwrap_err();

    let DownloadError::Size {
        file,
        expected,
        actual,
    } = error
    else {
        panic!("expected a size error, got {error:?}");
    };
    assert_eq!(
        (file, expected, actual),
        ("us_gold.json", LEXICON.len() as u64, long.len() as u64)
    );
    assert_eq!(models_entries(&home), Vec::<String>::new());
}

#[tokio::test]
async fn interrupted_transfer_installs_nothing() {
    let temp = tempfile::tempdir().unwrap();
    let home = TinyHome::under(temp.path());
    let mut routes = good_routes();
    routes.insert(
        format!("/test/model/{REVISION_PATH}/onnx/model.onnx"),
        Route {
            body: WEIGHTS[..100_000].to_vec(),
            declared: WEIGHTS.len(),
            before: None,
        },
    );
    let base = serve(routes).await;

    let error = fetch_quietly(&home, &good_files(), &base)
        .await
        .unwrap_err();

    let DownloadError::Transfer { url, .. } = error else {
        panic!("expected a transfer error, got {error:?}");
    };
    assert_eq!(
        url,
        format!("{base}/test/model/{REVISION_PATH}/onnx/model.onnx")
    );
    assert_eq!(models_entries(&home), Vec::<String>::new());
}

#[tokio::test]
async fn missing_file_is_an_http_status_error() {
    let temp = tempfile::tempdir().unwrap();
    let home = TinyHome::under(temp.path());
    let mut routes = good_routes();
    routes.remove(&format!(
        "/datasets/test/lexicon/{REVISION_PATH}/us_gold.json"
    ));
    let base = serve(routes).await;

    let error = fetch_quietly(&home, &good_files(), &base)
        .await
        .unwrap_err();

    let DownloadError::Status { url, status } = error else {
        panic!("expected a status error, got {error:?}");
    };
    assert_eq!(
        (url, status),
        (
            format!("{base}/datasets/test/lexicon/{REVISION_PATH}/us_gold.json"),
            404
        )
    );
    assert_eq!(models_entries(&home), Vec::<String>::new());
}

#[tokio::test]
async fn partial_install_is_replaced_only_on_success() {
    let temp = tempfile::tempdir().unwrap();
    let home = TinyHome::under(temp.path());
    let install_dir = home.model_dir(MODEL_ID);
    std::fs::create_dir_all(&install_dir).unwrap();
    std::fs::write(install_dir.join("config.json"), b"stale").unwrap();
    let base = serve(good_routes()).await;

    let mut bad_files = good_files();
    bad_files[0].sha256 = OTHER_SHA256;
    fetch_quietly(&home, &bad_files, &base).await.unwrap_err();
    assert_eq!(models_entries(&home), vec![MODEL_ID.to_owned()]);
    assert_eq!(
        tree(&install_dir),
        vec![("config.json".to_owned(), b"stale".to_vec())]
    );

    let outcome = fetch_quietly(&home, &good_files(), &base).await.unwrap();
    assert_eq!(outcome, Downloaded::Installed);
    assert_eq!(models_entries(&home), vec![MODEL_ID.to_owned()]);
    assert_eq!(tree(&install_dir), installed_tree());
}
