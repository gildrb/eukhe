//! `eukhe tiny-models download`: fetch, verify, install.
//!
//! The files of a model stream into `<models>/.staging-<id>-<pid>/`, each
//! hashed while it is written and checked against its pinned size and
//! sha256, then fsynced. Only a complete, verified set is installed: the
//! staging dir is renamed to `<models>/<id>` (an earlier incomplete install
//! is moved aside first and removed after). A failure removes the staging
//! dir and leaves any earlier install as it was.

use std::path::{Path, PathBuf};
use std::time::Duration;

use sha2::{Digest, Sha256};
use tokio::io::AsyncWriteExt;

use crate::catalog::{files_state, CatalogModel, InstallState, ModelFile, RepoKind};
use crate::paths::TinyHome;

/// The production download host.
pub const HUGGING_FACE: &str = "https://huggingface.co";

/// The longest wait for the next bytes of a response.
const READ_TIMEOUT: Duration = Duration::from_secs(60);

/// Download progress, reported per file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Progress {
    /// `received` of `total` bytes of `file` are written.
    Receiving {
        file: &'static str,
        received: u64,
        total: u64,
    },
    /// `file` matched its pinned size and sha256.
    Verified {
        file: &'static str,
        sha256: &'static str,
    },
}

/// What a download did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Downloaded {
    /// Fetched, verified and installed.
    Installed,
    /// Every file was already present with its pinned size; nothing fetched.
    AlreadyInstalled,
}

/// Why a download failed. Nothing is installed after any of them.
#[derive(Debug, thiserror::Error)]
pub enum DownloadError {
    #[error("cannot build the HTTP client: {0}")]
    Client(#[source] reqwest::Error),
    #[error("{url}: {source}")]
    Transfer {
        url: String,
        #[source]
        source: reqwest::Error,
    },
    #[error("{url}: HTTP {status}")]
    Status { url: String, status: u16 },
    #[error("{file}: expected {expected} bytes, received {actual}")]
    Size {
        file: &'static str,
        expected: u64,
        actual: u64,
    },
    #[error("{file}: sha256 {actual} does not match the pinned {expected}")]
    Checksum {
        file: &'static str,
        expected: &'static str,
        actual: String,
    },
    #[error("{}: {source}", path.display())]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

/// Fetches every file of `model` from `base_url` (production:
/// [`HUGGING_FACE`]), verifies each against its pin, and installs the set
/// atomically under [`TinyHome::model_dir`]. An installed model is skipped.
///
/// # Errors
/// A transfer, HTTP status, size, checksum or file-system failure; nothing
/// is installed then and an earlier install dir stays as it was.
#[tracing::instrument(skip_all, fields(model = model.id, base_url))]
pub async fn download(
    home: &TinyHome,
    model: &CatalogModel,
    base_url: &str,
    progress: &mut (dyn FnMut(Progress) + Send),
) -> Result<Downloaded, DownloadError> {
    download_files(home, model.id, model.files, base_url, progress).await
}

/// [`download`] of the model `id` made of `files`.
#[tracing::instrument(skip_all, fields(model = id, base_url))]
pub(crate) async fn download_files(
    home: &TinyHome,
    id: &str,
    files: &[ModelFile],
    base_url: &str,
    progress: &mut (dyn FnMut(Progress) + Send),
) -> Result<Downloaded, DownloadError> {
    let target = home.model_dir(id);
    match files_state(&target, files) {
        InstallState::Installed => return Ok(Downloaded::AlreadyInstalled),
        InstallState::Missing | InstallState::Partial { .. } => {}
    }
    create_dir_all(&home.models).await?;
    let staging = home
        .models
        .join(format!(".staging-{id}-{}", std::process::id()));
    // A staging dir of this pid can only be the leftover of a crashed run.
    remove_dir_all_if_present(&staging).await?;
    create_dir_all(&staging).await?;
    let fetched = fetch_all(&staging, files, base_url.trim_end_matches('/'), progress).await;
    let installed = match fetched {
        Ok(()) => install(home, id, files, &staging).await,
        Err(error) => Err(error),
    };
    match installed {
        Ok(outcome) => Ok(outcome),
        Err(error) => {
            // The download's own error is the one to report; the warning
            // names the staging dir left behind.
            if let Err(cleanup) = remove_dir_all_if_present(&staging).await {
                tracing::warn!(
                    "cannot remove the staging dir {}: {cleanup}",
                    staging.display()
                );
            }
            Err(error)
        }
    }
}

/// Fetches and verifies every file into `staging`, fsyncing files and the
/// directories that hold them.
async fn fetch_all(
    staging: &Path,
    files: &[ModelFile],
    base_url: &str,
    progress: &mut (dyn FnMut(Progress) + Send),
) -> Result<(), DownloadError> {
    let client = reqwest::Client::builder()
        .read_timeout(READ_TIMEOUT)
        .build()
        .map_err(DownloadError::Client)?;
    let mut dirs = vec![staging.to_path_buf()];
    for file in files {
        let target = staging.join(file.path);
        for dir in target.ancestors().skip(1).take_while(|dir| *dir != staging) {
            if !dirs.iter().any(|known| known == dir) {
                create_dir_all(dir).await?;
                dirs.push(dir.to_path_buf());
            }
        }
        let prefix = match file.repo_kind {
            RepoKind::Model => "",
            RepoKind::Dataset => "datasets/",
        };
        let url = format!(
            "{base_url}/{prefix}{}/resolve/{}/{}",
            file.repo, file.revision, file.path
        );
        fetch(&client, file, &url, &target, progress).await?;
        progress(Progress::Verified {
            file: file.path,
            sha256: file.sha256,
        });
    }
    for dir in &dirs {
        sync_dir(dir).await?;
    }
    Ok(())
}

/// Streams one file to `target`, hashing as it writes; rejects a size or
/// sha256 other than the pin.
#[tracing::instrument(skip_all, fields(file = file.path))]
async fn fetch(
    client: &reqwest::Client,
    file: &ModelFile,
    url: &str,
    target: &Path,
    progress: &mut (dyn FnMut(Progress) + Send),
) -> Result<(), DownloadError> {
    let transfer = |source| DownloadError::Transfer {
        url: url.to_owned(),
        source,
    };
    let io = |source| DownloadError::Io {
        path: target.to_path_buf(),
        source,
    };
    let mut response = client.get(url).send().await.map_err(transfer)?;
    if !response.status().is_success() {
        return Err(DownloadError::Status {
            url: url.to_owned(),
            status: response.status().as_u16(),
        });
    }
    let mut out = tokio::fs::File::create(target).await.map_err(io)?;
    let mut hasher = Sha256::new();
    let mut received: u64 = 0;
    progress(Progress::Receiving {
        file: file.path,
        received,
        total: file.size,
    });
    while let Some(chunk) = response.chunk().await.map_err(transfer)? {
        received += chunk.len() as u64;
        if received > file.size {
            return Err(DownloadError::Size {
                file: file.path,
                expected: file.size,
                actual: received,
            });
        }
        hasher.update(&chunk);
        out.write_all(&chunk).await.map_err(io)?;
        progress(Progress::Receiving {
            file: file.path,
            received,
            total: file.size,
        });
    }
    if received != file.size {
        return Err(DownloadError::Size {
            file: file.path,
            expected: file.size,
            actual: received,
        });
    }
    let actual = format!("{:x}", hasher.finalize());
    if actual != file.sha256 {
        return Err(DownloadError::Checksum {
            file: file.path,
            expected: file.sha256,
            actual,
        });
    }
    out.flush().await.map_err(io)?;
    out.sync_all().await.map_err(io)
}

/// Renames the verified `staging` dir to the model's install dir. An
/// existing install dir is moved aside first and removed once the new one
/// is in place; one that became complete meanwhile (a concurrent download)
/// is kept and `staging` is dropped.
async fn install(
    home: &TinyHome,
    id: &str,
    files: &[ModelFile],
    staging: &Path,
) -> Result<Downloaded, DownloadError> {
    let target = home.model_dir(id);
    let aside = home
        .models
        .join(format!(".replaced-{id}-{}", std::process::id()));
    let replacing = match tokio::fs::symlink_metadata(&target).await {
        Ok(_) => true,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
        Err(source) => {
            return Err(DownloadError::Io {
                path: target,
                source,
            })
        }
    };
    if replacing {
        if files_state(&target, files) == InstallState::Installed {
            remove_dir_all_if_present(staging).await?;
            return Ok(Downloaded::AlreadyInstalled);
        }
        remove_dir_all_if_present(&aside).await?;
        rename(&target, &aside).await?;
    }
    if let Err(error) = rename(staging, &target).await {
        if replacing {
            rename(&aside, &target).await?;
        }
        return Err(error);
    }
    sync_dir(&home.models).await?;
    if replacing {
        remove_dir_all_if_present(&aside).await?;
    }
    Ok(Downloaded::Installed)
}

async fn create_dir_all(path: &Path) -> Result<(), DownloadError> {
    tokio::fs::create_dir_all(path)
        .await
        .map_err(|source| DownloadError::Io {
            path: path.to_path_buf(),
            source,
        })
}

async fn rename(from: &Path, to: &Path) -> Result<(), DownloadError> {
    tokio::fs::rename(from, to)
        .await
        .map_err(|source| DownloadError::Io {
            path: from.to_path_buf(),
            source,
        })
}

async fn remove_dir_all_if_present(path: &Path) -> Result<(), DownloadError> {
    match tokio::fs::remove_dir_all(path).await {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(source) => Err(DownloadError::Io {
            path: path.to_path_buf(),
            source,
        }),
    }
}

/// Makes the entries of `dir` durable.
async fn sync_dir(dir: &Path) -> Result<(), DownloadError> {
    let io = |source| DownloadError::Io {
        path: dir.to_path_buf(),
        source,
    };
    tokio::fs::File::open(dir)
        .await
        .map_err(io)?
        .sync_all()
        .await
        .map_err(io)
}

#[cfg(test)]
#[path = "download/tests.rs"]
mod tests;
