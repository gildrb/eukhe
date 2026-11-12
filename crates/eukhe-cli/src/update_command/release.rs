//! The newest release as the release workflow publishes it: `release.json`
//! (version and tag) on the latest `eukhe-v*` release, `SHA256SUMS` and
//! the platform tarballs `eukhe-<version>-<platform>.tar.gz` beside it.

use std::path::Path;
use std::time::Duration;

use anyhow::{anyhow, bail, Context, Result};
use base64::Engine as _;
use eukhe_bend::rules::semver::{series, Series};
use sha2::{Digest, Sha256};
use tokio::io::AsyncWriteExt;

/// A connection that stalls this long fails the request.
const READ_TIMEOUT: Duration = Duration::from_secs(60);
const CONNECT_TIMEOUT: Duration = Duration::from_secs(30);

/// The release platform of this build, as the tarball names it.
pub(super) const PLATFORM: Option<&str> = if cfg!(all(target_os = "linux", target_arch = "x86_64"))
{
    Some("linux-x64")
} else if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
    Some("linux-arm64")
} else if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
    Some("darwin-arm64")
} else {
    None
};

/// A published release.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Release {
    /// `X.Y.Z`.
    pub version: String,
    /// `eukhe-vX.Y.Z`.
    pub tag: String,
}

impl Release {
    /// The tarball of `platform`.
    pub(super) fn tarball(&self, platform: &str) -> String {
        format!("eukhe-{}-{platform}.tar.gz", self.version)
    }
}

/// The fields of `release.json` this command reads.
#[derive(serde::Deserialize)]
struct ReleaseJson {
    version: String,
    tag: String,
}

/// The fields of the pinned `nix/release.json` this command reads.
#[derive(serde::Deserialize)]
struct PinJson {
    version: String,
    assets: std::collections::BTreeMap<String, PinAsset>,
}

#[derive(serde::Deserialize)]
struct PinAsset {
    url: String,
    /// `sha256-<base64>`.
    hash: String,
}

/// What the pinned `nix/release.json` says of a release's tarball.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Pin {
    /// It pins this release, with the same sha256.
    Same,
    /// It pins another version (named): only SHA256SUMS checks the tarball.
    OtherVersion(String),
    /// It could not be fetched or read (why): only SHA256SUMS checks the
    /// tarball.
    Unavailable(String),
}

/// The releases of one repository (`https://github.com/<repo>/releases`, or
/// a mirror of its layout), and the `nix/release.json` its main branch
/// pins.
pub(super) struct Releases {
    http: reqwest::Client,
    base: String,
    pin: String,
}

impl Releases {
    pub(super) fn new(base: &str, pin: &str, running: &str) -> Result<Self> {
        let http = reqwest::Client::builder()
            .user_agent(format!("eukhe/{running}"))
            .connect_timeout(CONNECT_TIMEOUT)
            .read_timeout(READ_TIMEOUT)
            .build()
            .context("cannot start the HTTP client")?;
        Ok(Self {
            http,
            base: base.trim_end_matches('/').to_string(),
            pin: pin.to_string(),
        })
    }

    /// Checks `sha256`, the sum SHA256SUMS lists for `file` of `release`,
    /// against the hash `nix/release.json` on main pins, as install.sh
    /// does: a pin of this release with another hash fails; a pin of
    /// another version, or none to fetch, leaves SHA256SUMS alone.
    #[tracing::instrument(skip_all, fields(file))]
    pub(super) async fn pin(&self, release: &Release, file: &str, sha256: &str) -> Result<Pin> {
        let url = &self.pin;
        let body = match self.get(url).await {
            Ok(response) => match response.bytes().await {
                Ok(body) => body,
                Err(error) => return Ok(Pin::Unavailable(format!("cannot read {url}: {error}"))),
            },
            Err(error) => return Ok(Pin::Unavailable(format!("{error:#}"))),
        };
        let json: PinJson = match serde_json::from_slice(&body) {
            Ok(json) => json,
            Err(error) => {
                return Ok(Pin::Unavailable(format!(
                    "{url} is not a release.json: {error}"
                )))
            }
        };
        if json.version != release.version {
            return Ok(Pin::OtherVersion(json.version));
        }
        let hash = json
            .assets
            .into_values()
            .find(|asset| asset.url.rsplit('/').next() == Some(file))
            .map(|asset| asset.hash)
            .ok_or_else(|| anyhow!("{url} pins {} without a hash for {file}", release.version))?;
        let pinned = hash
            .strip_prefix("sha256-")
            .and_then(|digest| {
                base64::engine::general_purpose::STANDARD
                    .decode(digest)
                    .ok()
            })
            .ok_or_else(|| anyhow!("{url} pins {file} with a malformed hash {hash:?}"))?;
        let listed: Vec<u8> = (0..sha256.len())
            .step_by(2)
            .map(|at| u8::from_str_radix(&sha256[at..at + 2], 16))
            .collect::<Result<_, _>>()
            .with_context(|| format!("SHA256SUMS lists {file} with a malformed sum {sha256:?}"))?;
        if pinned != listed {
            bail!(
                "{file}: the hash differs from {url}\n  pinned     {hash}\n  SHA256SUMS {sha256}"
            );
        }
        Ok(Pin::Same)
    }

    /// The newest release: `latest/download/release.json`.
    #[tracing::instrument(skip_all)]
    pub(super) async fn latest(&self) -> Result<Release> {
        let url = format!("{}/latest/download/release.json", self.base);
        let body = self
            .get(&url)
            .await?
            .bytes()
            .await
            .with_context(|| format!("cannot read {url}"))?;
        let json: ReleaseJson = serde_json::from_slice(&body)
            .with_context(|| format!("{url} is not a release.json"))?;
        let version_ok = matches!(series(&json.version, &json.version), Ok(Series::Of));
        if !version_ok || json.tag != format!("eukhe-v{}", json.version) {
            bail!(
                "{url} names no release version: version {:?}, tag {:?}",
                json.version,
                json.tag
            );
        }
        Ok(Release {
            version: json.version,
            tag: json.tag,
        })
    }

    /// The sha256 that the release's `SHA256SUMS` lists for `file`.
    #[tracing::instrument(skip_all, fields(file))]
    pub(super) async fn checksum(&self, release: &Release, file: &str) -> Result<String> {
        let url = format!("{}/download/{}/SHA256SUMS", self.base, release.tag);
        let sums = self
            .get(&url)
            .await?
            .text()
            .await
            .with_context(|| format!("cannot read {url}"))?;
        let listed = sums.lines().find_map(|line| {
            let (sum, name) = line.split_once(char::is_whitespace)?;
            (name.trim_start().trim_start_matches('*') == file).then(|| sum.to_ascii_lowercase())
        });
        match listed {
            Some(sum) if sum.len() == 64 && sum.bytes().all(|b| b.is_ascii_hexdigit()) => Ok(sum),
            Some(sum) => bail!("SHA256SUMS lists {file} with a malformed sum {sum:?}"),
            None => bail!("{file} is not listed in {url}"),
        }
    }

    /// Streams `file` of `release` to `target`; fails unless its sha256 is
    /// `sha256`.
    #[tracing::instrument(skip_all, fields(file))]
    pub(super) async fn download(
        &self,
        release: &Release,
        file: &str,
        sha256: &str,
        target: &Path,
    ) -> Result<()> {
        let url = format!("{}/download/{}/{file}", self.base, release.tag);
        let mut response = self.get(&url).await?;
        let mut out = tokio::fs::File::create(target)
            .await
            .with_context(|| format!("cannot create {}", target.display()))?;
        let mut hasher = Sha256::new();
        while let Some(chunk) = response
            .chunk()
            .await
            .with_context(|| format!("download of {url} interrupted"))?
        {
            hasher.update(&chunk);
            out.write_all(&chunk)
                .await
                .with_context(|| format!("cannot write {}", target.display()))?;
        }
        out.sync_all()
            .await
            .with_context(|| format!("cannot write {}", target.display()))?;
        let actual = format!("{:x}", hasher.finalize());
        if actual != sha256 {
            bail!("checksum mismatch for {file}\n  expected {sha256} (SHA256SUMS)\n  actual   {actual}");
        }
        Ok(())
    }

    async fn get(&self, url: &str) -> Result<reqwest::Response> {
        let response = self
            .http
            .get(url)
            .send()
            .await
            .with_context(|| format!("cannot reach {url}"))?;
        let status = response.status();
        if !status.is_success() {
            bail!("{url} answered HTTP {}", status.as_u16());
        }
        Ok(response)
    }
}
