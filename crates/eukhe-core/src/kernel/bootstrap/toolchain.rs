//! The kernel's pinned toolchain, in Eukhe's own directory
//! (`~/.eukhe/kernel`): one uv release, one standalone `CPython`, and the
//! kernel env made from it. `eukhe-runtime/kernel-toolchain.json` is the one
//! place that pins them (versions, download urls, sha256 of every archive);
//! it is embedded in the binary. Every kernel on every machine runs on that
//! `CPython`: no interpreter of the system or of `PATH` is ever looked at.
//!
//! [`ensure`] sets up what is absent, in the order the compiled Bend core
//! plans ([`super::setup`]): the uv archive is downloaded and checked
//! against its pinned sha256 before it is unpacked; uv installs the
//! interpreter from the pinned download list, checking the archive against
//! its pinned sha256; uv makes the env offline. A machine that has all
//! three makes no network request.

use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::io::Write as _;
use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::{LazyLock, Mutex, PoisonError};
use std::time::Duration;

use anyhow::{anyhow, bail, Context};
use sha2::{Digest, Sha256};

use super::dir_lock::acquire_bootstrap_lock;
use super::setup::{setup_steps, Have, SetupStep};

/// The pin file, embedded: a packaged binary carries its own pins.
const PIN_JSON: &str = include_str!("../../../../../eukhe-runtime/kernel-toolchain.json");

/// `EUKHE_KERNEL_DIR`: where the toolchain lives instead of
/// `~/.eukhe/kernel` (a test's or a packager's prepared directory). It
/// moves the directory only: the pins are the same.
const KERNEL_DIR_ENV: &str = "EUKHE_KERNEL_DIR";
/// Written into the env once `uv venv` returned: an env without it is
/// made again.
const ENV_READY: &str = ".eukhe-env-ready";
/// uv settings of the user's environment that reach Eukhe's uv; every
/// other `UV_*` variable is removed so it cannot change what is fetched.
const UV_ENV_KEPT: [&str; 3] = ["UV_CACHE_DIR", "UV_NATIVE_TLS", "UV_HTTP_TIMEOUT"];
/// The end of the name of a uv file being written.
const STAGED_SUFFIX: &str = ".part";
const CONNECT_TIMEOUT: Duration = Duration::from_secs(15);
const READ_TIMEOUT: Duration = Duration::from_secs(60);
/// How often a caller waiting for another setup shows that setup's stage.
const STAGE_POLL: Duration = Duration::from_millis(250);

#[derive(serde::Deserialize)]
struct Pin {
    uv: UvPin,
    python: PythonPin,
}

#[derive(serde::Deserialize)]
struct UvPin {
    version: String,
    /// The archive url, with `{version}` and `{target}`.
    url: String,
    /// The archive's sha256 by target triple.
    sha256: BTreeMap<String, String>,
}

#[derive(serde::Deserialize)]
struct PythonPin {
    version: String,
    /// uv's python-downloads list: one entry per platform, each with its
    /// url and sha256.
    downloads: serde_json::Value,
}

static PIN: LazyLock<Pin> = LazyLock::new(|| {
    serde_json::from_str(PIN_JSON)
        .expect("eukhe-runtime/kernel-toolchain.json parses (this module's tests read it)")
});

fn pin() -> &'static Pin {
    &PIN
}

/// The `major.minor.micro` of the one `CPython` every kernel runs on.
#[must_use]
pub fn pinned_python_version() -> &'static str {
    &pin().python.version
}

/// The version of the uv release Eukhe fetches for itself.
#[must_use]
pub fn pinned_uv_version() -> &'static str {
    &pin().uv.version
}

/// The uv release build for this machine: Linux takes the static musl
/// build, which runs on every Linux (glibc, musl, `NixOS`).
fn uv_target() -> Option<&'static str> {
    match (std::env::consts::OS, std::env::consts::ARCH) {
        ("macos", "aarch64") => Some("aarch64-apple-darwin"),
        ("macos", "x86_64") => Some("x86_64-apple-darwin"),
        ("linux", "aarch64") => Some("aarch64-unknown-linux-musl"),
        ("linux", "x86_64") => Some("x86_64-unknown-linux-musl"),
        _ => None,
    }
}

fn home_dir() -> PathBuf {
    eukhe_types::platform::home_dir().unwrap_or_else(|| PathBuf::from("/"))
}

pub(crate) fn expand_home(path: &str) -> PathBuf {
    if path == "~" {
        return home_dir();
    }
    match path.strip_prefix("~/") {
        Some(rest) => home_dir().join(rest),
        None => PathBuf::from(path),
    }
}

/// The managed env of earlier versions (`~/.eukhe/kernel-venv`), when it
/// is still on disk: nothing uses it any more.
#[must_use]
pub fn unused_kernel_venv() -> Option<PathBuf> {
    let dir = home_dir()
        .join(eukhe_types::platform::dirs::AGENT_DIR_NAME)
        .join("kernel-venv");
    dir.is_dir().then_some(dir)
}

/// Eukhe's kernel directory.
pub(crate) struct KernelDir(PathBuf);

impl KernelDir {
    /// `EUKHE_KERNEL_DIR`, else `~/.eukhe/kernel`, else (a home that
    /// cannot be written) `$XDG_DATA_HOME/eukhe/kernel`.
    pub(crate) fn resolve() -> anyhow::Result<Self> {
        if let Some(dir) = std::env::var(KERNEL_DIR_ENV)
            .ok()
            .filter(|dir| !dir.is_empty())
        {
            let dir = expand_home(&dir);
            std::fs::create_dir_all(&dir)
                .with_context(|| format!("{KERNEL_DIR_ENV}: cannot create {}", dir.display()))?;
            return Ok(Self(dir));
        }
        let primary = home_dir()
            .join(eukhe_types::platform::dirs::AGENT_DIR_NAME)
            .join("kernel");
        if std::fs::create_dir_all(&primary).is_ok() {
            return Ok(Self(primary));
        }
        let data_home = match std::env::var("XDG_DATA_HOME") {
            Ok(value) if !value.is_empty() => expand_home(&value),
            _ => home_dir().join(".local").join("share"),
        };
        let fallback = data_home.join("eukhe").join("kernel");
        std::fs::create_dir_all(&fallback).with_context(|| {
            format!(
                "cannot create the kernel directory at {} or {}",
                primary.display(),
                fallback.display()
            )
        })?;
        Ok(Self(fallback))
    }

    pub(crate) fn path(&self) -> &Path {
        &self.0
    }

    fn uv(&self) -> PathBuf {
        self.0.join("uv").join(&pin().uv.version).join("uv")
    }

    fn python_home(&self) -> PathBuf {
        self.0.join("python")
    }

    /// The pinned interpreter uv installed, if it is there: uv names the
    /// install `cpython-<version>-<platform>` and publishes it whole.
    fn python(&self) -> Option<PathBuf> {
        let prefix = format!("cpython-{}-", pin().python.version);
        std::fs::read_dir(self.python_home())
            .ok()?
            .filter_map(Result::ok)
            .filter(|entry| entry.file_name().to_string_lossy().starts_with(&prefix))
            .map(|entry| entry.path().join("bin").join("python3"))
            .find(|python| python.is_file())
    }

    /// The kernel env of the package lock `lock`: a lock change (a new
    /// Eukhe) starts a new, empty env, so an env only ever holds packages
    /// of one lock.
    fn env(&self, lock: &Path) -> anyhow::Result<PathBuf> {
        let mut key = Sha256::new();
        key.update(pin().python.version.as_bytes());
        key.update([0]);
        key.update(
            std::fs::read(lock)
                .with_context(|| format!("reading the package lock {}", lock.display()))?,
        );
        let key = format!("{:x}", key.finalize());
        Ok(self.0.join("envs").join(&key[..16]))
    }

    /// Where the packages of the project lock `project_lock` go: one
    /// directory per project, beside the env.
    pub(crate) fn project_packages(&self, project_lock: &Path) -> PathBuf {
        let key = format!(
            "{:x}",
            Sha256::digest(project_lock.as_os_str().as_encoded_bytes())
        );
        self.0
            .join("projects")
            .join(format!("{}-py{}", &key[..16], pin().python.version))
    }

    fn have(&self, env: &Path) -> Have {
        Have {
            uv: crate::platform::perms::is_executable(&self.uv()),
            python: self.python().is_some(),
            env: env.join(ENV_READY).is_file() && env_python(env).is_file(),
        }
    }

    fn ready(&self, env: &Path) -> Option<Toolchain> {
        let have = self.have(env);
        (have.uv && have.python && have.env).then(|| Toolchain {
            uv: self.uv(),
            python: env_python(env),
        })
    }
}

fn env_python(env: &Path) -> PathBuf {
    env.join("bin").join("python")
}

/// The toolchain on disk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Toolchain {
    /// Eukhe's uv.
    pub(crate) uv: PathBuf,
    /// The kernel env's interpreter: the pinned `CPython`.
    pub(crate) python: PathBuf,
}

/// The toolchain when all of it is on disk for the package lock `lock`,
/// without setting anything up and without network.
pub(crate) fn ready(lock: &Path) -> anyhow::Result<Option<Toolchain>> {
    let dir = KernelDir::resolve()?;
    let env = dir.env(lock)?;
    Ok(dir.ready(&env))
}

/// The stage of the setup this process runs, for the callers that wait
/// for it (a session's first cell behind the fetch its open started).
static STAGE: Mutex<String> = Mutex::new(String::new());

fn set_stage(message: &str) {
    message.clone_into(&mut STAGE.lock().unwrap_or_else(PoisonError::into_inner));
}

/// Clears the stage when the setup ends, on every path.
struct StageEnd;

impl Drop for StageEnd {
    fn drop(&mut self) {
        set_stage("");
    }
}

/// The toolchain for the package lock `lock`, set up when any of it is
/// absent: the pinned uv and the pinned interpreter are fetched (each
/// checked against its pinned sha256 before use), the env is made from
/// local files. `report` gets each stage. One setup runs at a time across
/// processes; a caller that waits for another's reports that one's stages.
///
/// # Errors
///
/// Returns an error when the kernel directory cannot be made, when a fetch
/// fails (no network, `EUKHE_OFFLINE`, a sha256 that does not match), or
/// when uv fails.
pub(crate) async fn ensure(
    lock: &Path,
    report: &(dyn Fn(&str) + Send + Sync),
) -> anyhow::Result<Toolchain> {
    let dir = KernelDir::resolve()?;
    let env = dir.env(lock)?;
    if let Some(toolchain) = dir.ready(&env) {
        return Ok(toolchain);
    }
    let _setup_lock = wait_for_setup_lock(&dir, report).await?;
    let _stage_end = StageEnd;
    for step in setup_steps(dir.have(&env)) {
        match step {
            SetupStep::FetchUv => {
                let what = format!("uv {}", pin().uv.version);
                stage(report, &format!("Fetching {what} for the Python kernel..."));
                refuse_offline(&what)?;
                fetch_uv(&dir).await?;
            }
            SetupStep::FetchPython => {
                let what = format!("Python {}", pin().python.version);
                stage(report, &format!("Fetching {what} for the kernel..."));
                refuse_offline(&what)?;
                fetch_python(&dir).await?;
            }
            SetupStep::MakeEnv => {
                stage(report, "Creating the kernel's Python environment...");
                make_env(&dir, &env).await?;
            }
        }
    }
    dir.ready(&env).ok_or_else(|| {
        anyhow!(
            "the kernel toolchain under {} is incomplete after its setup",
            dir.0.display()
        )
    })
}

fn stage(report: &(dyn Fn(&str) + Send + Sync), message: &str) {
    set_stage(message);
    report(message);
}

fn refuse_offline(what: &str) -> anyhow::Result<()> {
    if crate::packages::is_offline_mode_enabled() {
        bail!("EUKHE_OFFLINE is set and {what} is not fetched yet");
    }
    Ok(())
}

async fn wait_for_setup_lock(
    dir: &KernelDir,
    report: &(dyn Fn(&str) + Send + Sync),
) -> anyhow::Result<impl Drop> {
    let lock_base = dir.0.join("setup");
    let acquire = acquire_bootstrap_lock(&lock_base);
    tokio::pin!(acquire);
    let mut shown = String::new();
    loop {
        tokio::select! {
            lock = &mut acquire => return lock,
            () = tokio::time::sleep(STAGE_POLL) => {
                let mut stage = STAGE.lock().unwrap_or_else(PoisonError::into_inner).clone();
                if stage.is_empty() {
                    "Waiting for another Eukhe process to set up the Python kernel...".clone_into(&mut stage);
                }
                if stage != shown {
                    report(&stage);
                    shown = stage;
                }
            }
        }
    }
}

async fn download(url: &str) -> anyhow::Result<Vec<u8>> {
    let client = reqwest::Client::builder()
        .connect_timeout(CONNECT_TIMEOUT)
        .read_timeout(READ_TIMEOUT)
        .build()
        .context("building the HTTP client")?;
    let response = client
        .get(url)
        .send()
        .await
        .and_then(reqwest::Response::error_for_status)
        .with_context(|| format!("downloading {url}"))?;
    let body = response
        .bytes()
        .await
        .with_context(|| format!("downloading {url}"))?;
    Ok(body.to_vec())
}

/// Download the pinned uv release archive, check it against its pinned
/// sha256, then unpack its `uv` into the kernel directory.
async fn fetch_uv(dir: &KernelDir) -> anyhow::Result<()> {
    let uv = &pin().uv;
    let (os, arch) = (std::env::consts::OS, std::env::consts::ARCH);
    let target = uv_target().ok_or_else(|| anyhow!("Eukhe pins no uv build for {os} {arch}"))?;
    let pinned = uv
        .sha256
        .get(target)
        .ok_or_else(|| anyhow!("kernel-toolchain.json pins no sha256 for uv {target}"))?;
    let url = uv
        .url
        .replace("{version}", &uv.version)
        .replace("{target}", target);
    let archive = download(&url).await?;
    let actual = format!("{:x}", Sha256::digest(&archive));
    if actual != *pinned {
        bail!("{url} does not match its pinned sha256 (pinned {pinned}, got {actual}); nothing was unpacked");
    }
    let dest = dir.uv();
    tokio::task::spawn_blocking(move || unpack_uv(&archive, &dest))
        .await
        .context("unpacking uv")?
}

/// Write the archive's `uv` file to `dest`, published whole (written
/// beside it, then renamed). The caller holds the setup lock, so a staged
/// file already there is a dead attempt's: it is removed.
fn unpack_uv(archive: &[u8], dest: &Path) -> anyhow::Result<()> {
    let parent = dest.parent().unwrap_or(Path::new("/"));
    std::fs::create_dir_all(parent)?;
    for entry in std::fs::read_dir(parent)?.filter_map(Result::ok) {
        if entry.file_name().to_string_lossy().ends_with(STAGED_SUFFIX) {
            std::fs::remove_file(entry.path())?;
        }
    }
    let mut tar = tar::Archive::new(flate2::read::GzDecoder::new(archive));
    for entry in tar.entries().context("reading the uv archive")? {
        let mut entry = entry.context("reading the uv archive")?;
        if !entry.header().entry_type().is_file()
            || entry.path()?.file_name() != Some(OsStr::new("uv"))
        {
            continue;
        }
        let staged = parent.join(format!("uv.{}{STAGED_SUFFIX}", std::process::id()));
        let mut file = std::fs::File::create(&staged)?;
        std::io::copy(&mut entry, &mut file)?;
        file.flush()?;
        file.set_permissions(std::fs::Permissions::from_mode(0o755))?;
        drop(file);
        std::fs::rename(&staged, dest)?;
        return Ok(());
    }
    bail!("the uv archive holds no `uv` file")
}

/// `uv python install` of the pinned version from the pinned download
/// list: uv checks the archive against the list's sha256 before it
/// installs, and installs nothing outside the kernel directory.
async fn fetch_python(dir: &KernelDir) -> anyhow::Result<()> {
    let python = &pin().python;
    let downloads = dir.0.join("python-downloads.json");
    std::fs::write(&downloads, serde_json::to_vec_pretty(&python.downloads)?)
        .with_context(|| format!("writing {}", downloads.display()))?;
    run_uv(
        &dir.uv(),
        &[
            "python".into(),
            "install".into(),
            "--no-config".into(),
            "--no-bin".into(),
            "--install-dir".into(),
            dir.python_home().into_os_string(),
            "--python-downloads-json-url".into(),
            downloads.into_os_string(),
            OsString::from(&python.version),
        ],
    )
    .await?;
    if dir.python().is_none() {
        bail!(
            "uv installed no Python {} under {}",
            python.version,
            dir.python_home().display()
        );
    }
    Ok(())
}

/// `uv venv --offline` on the pinned interpreter: local files only.
async fn make_env(dir: &KernelDir, env: &Path) -> anyhow::Result<()> {
    let python = dir
        .python()
        .ok_or_else(|| anyhow!("the pinned Python is not under {}", dir.0.display()))?;
    run_uv(
        &dir.uv(),
        &[
            "venv".into(),
            "--no-config".into(),
            "--offline".into(),
            "--no-project".into(),
            "--clear".into(),
            "--python".into(),
            python.into_os_string(),
            env.as_os_str().to_owned(),
        ],
    )
    .await?;
    std::fs::write(env.join(ENV_READY), "")
        .with_context(|| format!("marking {} ready", env.display()))
}

/// Run Eukhe's uv with the user's `UV_*` settings removed (but
/// [`UV_ENV_KEPT`]) and no active venv.
///
/// # Errors
///
/// Returns an error naming the command and the end of uv's stderr when uv
/// does not start or exits unsuccessfully.
pub(crate) async fn run_uv(uv: &Path, args: &[OsString]) -> anyhow::Result<()> {
    let mut command = tokio::process::Command::new(uv);
    command
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true);
    for (name, _) in std::env::vars_os() {
        let name_text = name.to_string_lossy();
        if name_text.starts_with("UV_") && !UV_ENV_KEPT.contains(&&*name_text) {
            command.env_remove(&name);
        }
    }
    command.env_remove("VIRTUAL_ENV").env_remove("CONDA_PREFIX");
    let words: Vec<String> = args
        .iter()
        .take(2)
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect();
    let name = format!("uv {}", words.join(" "));
    let output = command
        .output()
        .await
        .with_context(|| format!("starting {} for `{name}`", uv.display()))?;
    if output.status.success() {
        return Ok(());
    }
    let stderr = String::from_utf8_lossy(&output.stderr);
    let lines: Vec<&str> = stderr
        .lines()
        .filter(|line| !line.trim().is_empty())
        .collect();
    let tail = lines[lines.len().saturating_sub(12)..].join("\n");
    bail!("`{name}` failed ({}):\n{tail}", output.status)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pin file names one uv release with a sha256 for every build
    /// Eukhe fetches, and one `CPython` with a download (url and sha256)
    /// for every platform: macOS and Linux, both architectures, the same
    /// version.
    #[test]
    fn the_pin_file_pins_every_platform_to_one_version() {
        let pin = pin();
        let hex64 = |text: &str| text.len() == 64 && text.bytes().all(|b| b.is_ascii_hexdigit());
        let targets: Vec<&str> = pin.uv.sha256.keys().map(String::as_str).collect();
        assert_eq!(
            targets,
            [
                "aarch64-apple-darwin",
                "aarch64-unknown-linux-musl",
                "x86_64-apple-darwin",
                "x86_64-unknown-linux-musl"
            ]
        );
        assert!(pin.uv.sha256.values().all(|sha| hex64(sha)));
        assert!(uv_target().is_some_and(|target| pin.uv.sha256.contains_key(target)));
        let downloads = pin.python.downloads.as_object().expect("an object");
        let mut platforms = Vec::new();
        let parts: Vec<u64> = pin
            .python
            .version
            .split('.')
            .map(|part| part.parse().expect("a number"))
            .collect();
        for (key, download) in downloads {
            assert!(
                key.starts_with(&format!("cpython-{}-", pin.python.version)),
                "{key}"
            );
            let field = |name: &str| download[name].as_str().unwrap_or_default().to_owned();
            assert_eq!(
                [&download["major"], &download["minor"], &download["patch"]]
                    .map(serde_json::Value::as_u64),
                [Some(parts[0]), Some(parts[1]), Some(parts[2])]
            );
            assert!(hex64(&field("sha256")), "{key}");
            assert!(
                field("url").starts_with(
                    "https://github.com/astral-sh/python-build-standalone/releases/download/"
                ) && field("url").contains(&format!("cpython-{}%2B", pin.python.version)),
                "{key}"
            );
            platforms.push(format!(
                "{}-{}-{}",
                field("os"),
                download["arch"]["family"].as_str().unwrap_or_default(),
                field("libc")
            ));
        }
        assert_eq!(
            platforms,
            [
                "darwin-aarch64-none",
                "darwin-x86_64-none",
                "linux-aarch64-gnu",
                "linux-aarch64-musl",
                "linux-x86_64-gnu",
                "linux-x86_64-musl"
            ]
        );
    }

    /// A uv archive unpacks to its `uv` file, executable; an archive
    /// without one is refused.
    #[test]
    fn the_uv_archive_unpacks_to_an_executable() -> anyhow::Result<()> {
        let dir = tempfile::tempdir()?;
        let archive = |files: &[(&str, &[u8])]| -> anyhow::Result<Vec<u8>> {
            let gz = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::fast());
            let mut tar = tar::Builder::new(gz);
            for (name, body) in files {
                let mut header = tar::Header::new_gnu();
                header.set_size(body.len() as u64);
                header.set_mode(0o644);
                header.set_cksum();
                tar.append_data(&mut header, name, *body)?;
            }
            Ok(tar.into_inner()?.finish()?)
        };
        let dest = dir.path().join("uv").join("1.0").join("uv");
        std::fs::create_dir_all(dest.parent().expect("a parent"))?;
        std::fs::write(dest.with_file_name("uv.1.part"), "a dead attempt's")?;
        unpack_uv(
            &archive(&[("uv-x/uvx", b"other"), ("uv-x/uv", b"#!/bin/sh\n")])?,
            &dest,
        )?;
        assert_eq!(std::fs::read(&dest)?, b"#!/bin/sh\n");
        assert!(crate::platform::perms::is_executable(&dest));
        assert_eq!(
            std::fs::read_dir(dest.parent().expect("a parent"))?.count(),
            1,
            "no staged file is left"
        );
        let error = unpack_uv(&archive(&[("uv-x/uvx", b"other")])?, &dest)
            .expect_err("no uv in the archive");
        assert_eq!(error.to_string(), "the uv archive holds no `uv` file");
        Ok(())
    }
}
