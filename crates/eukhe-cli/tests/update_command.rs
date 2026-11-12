//! `eukhe update` against a local release stub (`EUKHE_RELEASES_URL`): an
//! install laid out as install.sh lays it out, a fake release (tarball,
//! SHA256SUMS, release.json), and the installs the command refuses.

use std::collections::{BTreeMap, HashMap};
use std::io::{BufRead, BufReader, Write};
use std::net::TcpListener;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use base64::Engine as _;
use sha2::{Digest, Sha256};

const OLD: &str = "0.10.1";
const NEW: &str = "0.10.2";

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const PLATFORM: &str = "linux-x64";
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const PLATFORM: &str = "linux-arm64";
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const PLATFORM: &str = "darwin-arm64";

/// One route of the stub: the body, and how many bytes of it to send
/// before the connection closes (the header always names the whole body).
#[derive(Clone)]
struct Route {
    body: Vec<u8>,
    sent: usize,
}

/// An HTTP/1.1 server on a loopback port that answers fixed routes, one
/// request per connection. Bound before the binary starts: ready at once.
struct Stub {
    port: u16,
}

impl Stub {
    fn start(routes: HashMap<String, Route>) -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let port = listener.local_addr().unwrap().port();
        let routes = Arc::new(routes);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(mut stream) = stream else { continue };
                let mut reader = BufReader::new(stream.try_clone().unwrap());
                let mut request = String::new();
                if reader.read_line(&mut request).is_err() {
                    continue;
                }
                let mut header = String::new();
                while reader.read_line(&mut header).is_ok_and(|n| n > 2) {
                    header.clear();
                }
                let path = request.split_whitespace().nth(1).unwrap_or("/").to_string();
                let reply = match routes.get(&path) {
                    Some(route) => {
                        let mut reply = format!(
                            "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                            route.body.len()
                        )
                        .into_bytes();
                        reply.extend_from_slice(&route.body[..route.sent]);
                        reply
                    }
                    None => {
                        b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
                            .to_vec()
                    }
                };
                let _ = stream.write_all(&reply);
            }
        });
        Self { port }
    }

    fn url(&self) -> String {
        format!("http://127.0.0.1:{}/releases", self.port)
    }
}

fn full(body: Vec<u8>) -> Route {
    let sent = body.len();
    Route { body, sent }
}

/// The payload files of `version`, each naming the version.
fn payload_files(version: &str) -> Vec<(&'static str, String)> {
    vec![
        ("eukhe", format!("#!/bin/sh\necho {version}\n")),
        ("package.json", format!("{{\"version\": \"{version}\"}}\n")),
        ("models.bundled.json", format!("models {version}\n")),
        ("mcp-services.bundled.json", format!("services {version}\n")),
        (
            "eukhe-runtime/pyproject.toml",
            format!("runtime {version}\n"),
        ),
        ("skills/demo/SKILL.md", format!("skill {version}\n")),
    ]
}

/// The release tarball of `version`: the payload at the archive root.
fn tarball(version: &str) -> Vec<u8> {
    let gz = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::fast());
    let mut archive = tar::Builder::new(gz);
    for (name, content) in payload_files(version) {
        let mut header = tar::Header::new_gnu();
        header.set_size(content.len() as u64);
        header.set_mode(if name == "eukhe" { 0o755 } else { 0o644 });
        header.set_cksum();
        archive
            .append_data(&mut header, name, content.as_bytes())
            .unwrap();
    }
    archive.into_inner().unwrap().finish().unwrap()
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// The routes of a release `version` whose SHA256SUMS lists `sum` for the
/// tarball (`None`: its real sum) and whose tarball route sends `sent`
/// bytes (`None`: all), and a pin (`/pin/release.json`) of the tarball's
/// real hash.
fn release(version: &str, sum: Option<&str>, sent: Option<usize>) -> HashMap<String, Route> {
    let digest = Sha256::digest(tarball(version));
    let hash = base64::engine::general_purpose::STANDARD.encode(digest);
    let mut routes = unpinned(version, sum, sent);
    routes.insert(
        "/pin/release.json".to_string(),
        full(pin(version, &hash).into_bytes()),
    );
    routes
}

/// The `nix/release.json` of `version` pinning the tarball by `hash`
/// (base64 sha256).
fn pin(version: &str, hash: &str) -> String {
    format!(
        "{{\"version\": \"{version}\", \"tag\": \"eukhe-v{version}\", \"assets\": {{\"system\": {{\"url\": \"https://example.invalid/releases/download/eukhe-v{version}/eukhe-{version}-{PLATFORM}.tar.gz\", \"hash\": \"sha256-{hash}\"}}}}}}\n"
    )
}

/// The release routes alone (see [`release`]).
fn unpinned(version: &str, sum: Option<&str>, sent: Option<usize>) -> HashMap<String, Route> {
    let tag = format!("eukhe-v{version}");
    let name = format!("eukhe-{version}-{PLATFORM}.tar.gz");
    let archive = tarball(version);
    let sums = format!(
        "{}  {name}\n",
        sum.map_or_else(|| sha256(&archive), str::to_string)
    );
    let json = format!("{{\"version\": \"{version}\", \"tag\": \"{tag}\", \"assets\": {{}}}}\n");
    let tar_route = Route {
        sent: sent.unwrap_or(archive.len()),
        body: archive,
    };
    HashMap::from([
        (
            "/releases/latest/download/release.json".to_string(),
            full(json.into_bytes()),
        ),
        (
            format!("/releases/download/{tag}/SHA256SUMS"),
            full(sums.into_bytes()),
        ),
        (format!("/releases/download/{tag}/{name}"), tar_route),
    ])
}

/// An install as install.sh leaves it: `root/eukhe-<OLD>` holding the real
/// binary (its package.json makes it report OLD) and `bin/eukhe`.
struct Install {
    dir: tempfile::TempDir,
}

impl Install {
    fn new() -> Self {
        let dir = tempfile::tempdir().unwrap();
        let install = Self { dir };
        let payload = install.root().join(format!("eukhe-{OLD}"));
        write_files(&payload, &payload_files(OLD));
        std::fs::copy(env!("CARGO_BIN_EXE_eukhe"), payload.join("eukhe")).unwrap();
        std::fs::create_dir_all(install.bin()).unwrap();
        install.write_launcher(&payload);
        install
    }

    fn base(&self) -> PathBuf {
        self.dir.path().canonicalize().unwrap()
    }

    fn root(&self) -> PathBuf {
        self.base().join("root")
    }

    fn bin(&self) -> PathBuf {
        self.base().join("bin")
    }

    fn write_launcher(&self, payload: &Path) {
        let launcher = self.bin().join("eukhe");
        std::fs::write(&launcher, launcher_script(payload)).unwrap();
        std::fs::set_permissions(&launcher, std::fs::Permissions::from_mode(0o755)).unwrap();
    }

    /// Runs `exe update <args>` against `releases`.
    fn run(&self, exe: &Path, args: &[&str], releases: &str) -> (i32, String, String) {
        let home = self.base().join("home");
        std::fs::create_dir_all(&home).unwrap();
        let path = format!(
            "{}:{}",
            self.bin().display(),
            std::env::var("PATH").unwrap_or_default()
        );
        let output = Command::new(exe)
            .arg("update")
            .args(args)
            .env_clear()
            .env("HOME", &home)
            .env("PATH", path)
            .env("EUKHE_RELEASES_URL", releases)
            .env(
                "EUKHE_RELEASE_PIN_URL",
                releases.replace("/releases", "/pin/release.json"),
            )
            .env("EUKHE_DAEMON_SOCKET", self.base().join("daemon.sock"))
            .env("MISE_DATA_DIR", self.base().join("mise"))
            .output()
            .unwrap();
        (
            output.status.code().unwrap_or(-1),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    }

    fn update(&self, args: &[&str], releases: &str) -> (i32, String, String) {
        self.run(&self.bin().join("eukhe"), args, releases)
    }

    /// Every file under the install (root and bin), with its content.
    fn tree(&self) -> BTreeMap<PathBuf, Vec<u8>> {
        let mut files = BTreeMap::new();
        walk(&self.root(), &self.base(), &mut files);
        walk(&self.bin(), &self.base(), &mut files);
        files
    }
}

fn launcher_script(payload: &Path) -> String {
    format!(
        "#!/bin/sh\n# eukhe launcher written by install.sh; the payload sits beside itself\nexec \"{}/eukhe\" \"$@\"\n",
        payload.display()
    )
}

fn write_files(dir: &Path, files: &[(&str, String)]) {
    for (name, content) in files {
        let path = dir.join(name);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, content).unwrap();
        if *name == "eukhe" {
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
    }
}

fn walk(dir: &Path, base: &Path, files: &mut BTreeMap<PathBuf, Vec<u8>>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            files.insert(path.strip_prefix(base).unwrap().to_path_buf(), Vec::new());
            walk(&path, base, files);
        } else {
            files.insert(
                path.strip_prefix(base).unwrap().to_path_buf(),
                std::fs::read(&path).unwrap(),
            );
        }
    }
}

#[test]
fn check_prints_both_versions() {
    let install = Install::new();
    let stub = Stub::start(release(NEW, None, None));
    assert_eq!(
        install.update(&["--check"], &stub.url()),
        (
            0,
            format!("Current version: {OLD}\nLatest release:  {NEW}\nUpdate available: run \"eukhe update\"\n"),
            String::new()
        )
    );
}

#[test]
fn an_update_installs_the_new_payload_and_switches_the_launcher() {
    let install = Install::new();
    let stub = Stub::start(release(NEW, None, None));
    let name = format!("eukhe-{NEW}-{PLATFORM}.tar.gz");
    let sum = sha256(&tarball(NEW));
    let new_payload = install.root().join(format!("eukhe-{NEW}"));
    assert_eq!(
        install.update(&[], &stub.url()),
        (
            0,
            format!(
                "Current version: {OLD}\nLatest release:  {NEW}\nDownloading {name}\nVerified sha256 {sum} against SHA256SUMS and nix/release.json\n  payload:  {}\n  launcher: {}\nUpdated eukhe {OLD} -> {NEW}\n",
                new_payload.display(),
                install.bin().join("eukhe").display()
            ),
            String::new()
        )
    );
    let tree = install.tree();
    let new_files: BTreeMap<PathBuf, Vec<u8>> = tree
        .iter()
        .filter(|(path, _)| path.starts_with(format!("root/eukhe-{NEW}")))
        .filter(|(_, content)| !content.is_empty())
        .map(|(path, content)| (path.clone(), content.clone()))
        .collect();
    let expected: BTreeMap<PathBuf, Vec<u8>> = payload_files(NEW)
        .into_iter()
        .map(|(name, content)| {
            (
                PathBuf::from(format!("root/eukhe-{NEW}/{name}")),
                content.into_bytes(),
            )
        })
        .collect();
    assert_eq!(new_files, expected);
    assert_eq!(
        std::fs::read_to_string(install.bin().join("eukhe")).unwrap(),
        launcher_script(&new_payload)
    );
    // The previous payload stays for a running daemon; no stage remains.
    let mut entries: Vec<String> = std::fs::read_dir(install.root())
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    entries.sort();
    assert_eq!(entries, [format!("eukhe-{OLD}"), format!("eukhe-{NEW}")]);
    let version = Command::new(install.bin().join("eukhe"))
        .arg("--version")
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&version.stdout), format!("{NEW}\n"));
}

#[test]
fn the_newest_release_already_installed_changes_nothing() {
    let install = Install::new();
    let stub = Stub::start(release(OLD, None, None));
    let before = install.tree();
    assert_eq!(
        install.update(&[], &stub.url()),
        (
            0,
            format!("Current version: {OLD}\nLatest release:  {OLD}\neukhe is up to date\n"),
            String::new()
        )
    );
    assert_eq!(install.tree(), before);
}

#[test]
fn a_checksum_mismatch_leaves_the_install_untouched() {
    let install = Install::new();
    // SHA256SUMS and the pin agree on a sum the tarball does not have.
    let wrong = "0".repeat(64);
    let mut routes = release(NEW, Some(&wrong), None);
    let zeros = base64::engine::general_purpose::STANDARD.encode([0u8; 32]);
    routes.insert(
        "/pin/release.json".to_string(),
        full(pin(NEW, &zeros).into_bytes()),
    );
    let stub = Stub::start(routes);
    let before = install.tree();
    let (code, _, stderr) = install.update(&[], &stub.url());
    assert_eq!(
        (code, stderr.lines().next().map(str::to_string)),
        (
            1,
            Some(format!(
                "Error: checksum mismatch for eukhe-{NEW}-{PLATFORM}.tar.gz"
            ))
        )
    );
    assert_eq!(install.tree(), before);
}

#[test]
fn a_hash_other_than_the_pinned_one_leaves_the_install_untouched() {
    let install = Install::new();
    let mut routes = release(NEW, None, None);
    let other = base64::engine::general_purpose::STANDARD.encode([0u8; 32]);
    routes.insert(
        "/pin/release.json".to_string(),
        full(pin(NEW, &other).into_bytes()),
    );
    let stub = Stub::start(routes);
    let before = install.tree();
    let (code, _, stderr) = install.update(&[], &stub.url());
    let url = stub.url().replace("/releases", "/pin/release.json");
    assert_eq!(
        (code, stderr.lines().next().map(str::to_string)),
        (
            1,
            Some(format!(
                "Error: eukhe-{NEW}-{PLATFORM}.tar.gz: the hash differs from {url}"
            ))
        )
    );
    assert_eq!(install.tree(), before);
}

#[test]
fn without_a_pin_to_fetch_sha256sums_alone_checks_the_tarball() {
    let install = Install::new();
    let stub = Stub::start(unpinned(NEW, None, None));
    let (code, stdout, stderr) = install.update(&[], &stub.url());
    let url = stub.url().replace("/releases", "/pin/release.json");
    assert_eq!(
        (
            code,
            stdout
                .lines()
                .any(|line| line.ends_with(" against SHA256SUMS")),
            stderr
        ),
        (
            0,
            true,
            format!("warning: {url} answered HTTP 404: SHA256SUMS verification only\n")
        )
    );
    assert_eq!(
        std::fs::read_to_string(install.bin().join("eukhe")).unwrap(),
        launcher_script(&install.root().join(format!("eukhe-{NEW}")))
    );
}

#[test]
fn an_interrupted_download_leaves_the_install_untouched() {
    let install = Install::new();
    let stub = Stub::start(release(NEW, None, Some(100)));
    let before = install.tree();
    let (code, _, stderr) = install.update(&[], &stub.url());
    let url = format!(
        "{}/download/eukhe-v{NEW}/eukhe-{NEW}-{PLATFORM}.tar.gz",
        stub.url()
    );
    assert_eq!(
        (
            code,
            stderr.starts_with(&format!("Error: download of {url} interrupted"))
        ),
        (1, true),
        "{stderr}"
    );
    assert_eq!(install.tree(), before);
}

#[test]
fn an_unreachable_release_server_fails_with_its_url() {
    let install = Install::new();
    // A port bound and closed again: nothing listens there.
    let port = TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port();
    let url = format!("http://127.0.0.1:{port}/releases");
    let (code, stdout, stderr) = install.update(&["--check"], &url);
    let reason = format!("Error: cannot reach {url}/latest/download/release.json: ");
    assert_eq!(
        (code, stdout, stderr.starts_with(&reason)),
        (1, String::new(), true),
        "{stderr}"
    );
}

#[test]
fn a_read_only_install_root_is_refused_with_the_installer_command() {
    let install = Install::new();
    let stub = Stub::start(release(NEW, None, None));
    let before = install.tree();
    std::fs::set_permissions(install.root(), std::fs::Permissions::from_mode(0o555)).unwrap();
    let result = install.update(&[], &stub.url());
    std::fs::set_permissions(install.root(), std::fs::Permissions::from_mode(0o755)).unwrap();
    assert_eq!(
        result,
        (
            1,
            String::new(),
            format!(
                "Error: {root} is not writable by this user. Update the install as a user that can write it:\n  curl -fsSL https://eukhe.com/install | EUKHE_INSTALL_ROOT={root} EUKHE_INSTALL_BIN_DIR={bin} sh\n",
                root = install.root().display(),
                bin = install.bin().display()
            )
        )
    );
    assert_eq!(install.tree(), before);
}

#[test]
fn managed_installs_are_refused_with_their_update_command() {
    let install = Install::new();
    let stub = Stub::start(release(NEW, None, None));
    let place = |relative: &str| {
        let exe = install.base().join(relative);
        std::fs::create_dir_all(exe.parent().unwrap()).unwrap();
        std::fs::copy(env!("CARGO_BIN_EXE_eukhe"), &exe).unwrap();
        exe
    };
    let mise = place("mise/installs/github-gildrb-eukhe/0.10.1/eukhe");
    let app = place("Eukhe.app/Contents/MacOS/eukhe");
    let results = [&mise, &app].map(|exe| install.run(exe, &[], &stub.url()));
    assert_eq!(
        results,
        [
            (
                1,
                String::new(),
                format!(
                    "Error: mise manages this eukhe ({}). Update it with:\n  mise upgrade github:gildrb/eukhe\n",
                    mise.display()
                )
            ),
            (
                1,
                String::new(),
                format!(
                    "Error: this eukhe ships inside {}. Update the app to update it.\n",
                    install.base().join("Eukhe.app").display()
                )
            ),
        ]
    );
    // The test binary itself is a cargo build in this checkout's target.
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap();
    let (code, stdout, stderr) =
        install.run(Path::new(env!("CARGO_BIN_EXE_eukhe")), &[], &stub.url());
    assert_eq!(
        (code, stdout, stderr),
        (
            1,
            String::new(),
            format!(
                "Error: this eukhe is a cargo build of {ws}. Update it with:\n  git -C {ws} pull && cargo build --release --manifest-path {ws}/Cargo.toml\n",
                ws = workspace.display()
            )
        )
    );
}
