//! Local user-authored MCP service sources (`mcp-services.json`, ENG-6108):
//! a bounded read of one local JSON file of service entries validated
//! against the same contract as the catalog. Port of
//! `packages/ai/src/mcp/local-catalog.ts`.
//!
//! The loader is deliberately narrow: a bounded read of a regular file +
//! JSON parse + structural validation — no execution, no network, no
//! credential access. A local file can never masquerade as trusted:
//! provenance may only claim the `user` source, `legacyBuiltin` and
//! `metadata-reviewed` review status cannot be self-asserted, audit-derived
//! `setup.readiness` cannot be self-asserted, and ids colliding with the
//! compiled built-ins are refused (no silent override/rebind of reserved
//! ids). Errors are visible and bounded: they name the file and entry index
//! and never echo raw input values.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use super::catalog_schema::{
    CatalogEntryError, McpServiceEntry, ProvenanceSource, VerificationStatus,
};

/// Maximum accepted local source file size.
pub const MAX_LOCAL_CATALOG_BYTES: u64 = 256 * 1024;
/// Maximum accepted entries per local source file.
pub const MAX_LOCAL_CATALOG_ENTRIES: usize = 50;
/// The local read chunk (bounds how far an oversized read can go).
const READ_CHUNK: usize = 64 * 1024;

/// Validated local entries in file order (ids unique and non-reserved).
#[derive(Debug, Clone, Default)]
pub struct LocalCatalogLoadResult {
    pub entries: Vec<McpServiceEntry>,
    /// The path entries were loaded from; `None` when the file is absent.
    pub path: Option<PathBuf>,
}

/// Envelope of a local source file: `version` (exactly 1) and `entries`.
#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct LocalCatalogFile {
    version: u8,
    entries: Vec<McpServiceEntry>,
}

/// Why a local service source was refused. Never echoes raw input values:
/// a JSON failure keeps only its position, since the parser's text can
/// quote the input.
#[derive(Debug, thiserror::Error)]
pub enum LocalCatalogError {
    #[error(
        "Local service source {} is not a regular file; directories, FIFOs and devices are refused",
        path.display()
    )]
    NotRegularFile { path: PathBuf },
    #[error("Local service source {} could not be read", path.display())]
    Read {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("Local service source {} exceeds the maximum of {max_bytes} bytes", path.display())]
    TooLarge { path: PathBuf, max_bytes: u64 },
    #[error(
        "Local service source {} is not valid JSON (parse error near line {line} column {column})",
        path.display()
    )]
    Json {
        path: PathBuf,
        line: usize,
        column: usize,
    },
    #[error("Local service source {} has an unsupported version; expected 1", path.display())]
    UnsupportedVersion { path: PathBuf },
    #[error(
        "Local service source {} has {count} entries; the maximum is {MAX_LOCAL_CATALOG_ENTRIES}",
        path.display()
    )]
    TooManyEntries { path: PathBuf, count: usize },
    /// Entry `index` of the file breaks a rule; the fault's text follows
    /// the entry's position directly.
    #[error("Local service source {}, entry {index}{fault}", path.display())]
    Entry {
        path: PathBuf,
        index: usize,
        #[source]
        fault: LocalEntryFault,
    },
}

/// The rule a local entry breaks. Each text continues `…, entry <index>`.
#[derive(Debug, thiserror::Error)]
pub enum LocalEntryFault {
    #[error(": {0}")]
    Invalid(#[source] CatalogEntryError),
    #[error(" ({id}): local entries may only carry provenance source \"user\"")]
    ForeignProvenance { id: String },
    #[error(" ({id}): local entries need at least one provenance record with source \"user\"")]
    NoProvenance { id: String },
    #[error(
        " ({id}): local entries cannot claim legacyBuiltin; it is reserved for Prime built-ins"
    )]
    LegacyBuiltin { id: String },
    #[error(
        " ({id}): local entries cannot claim \"{status}\"; local sources are always unverified"
    )]
    Verified { id: String, status: &'static str },
    #[error(
        " ({id}): local entries cannot claim setup.readiness; readiness is a Prime audit assessment"
    )]
    Readiness { id: String },
    #[error(": duplicate local id \"{id}\"")]
    Duplicate { id: String },
    #[error(
        ": id \"{id}\" collides with the bundled catalog entry for \"{label}\"; local sources cannot shadow or rebind built-ins -- pick another id"
    )]
    Reserved { id: String, label: String },
}

/// Load and validate one local service source file. A missing file is not an
/// error and yields zero entries; every problem with an existing file is a
/// returned error naming the path (and entry index where applicable).
///
/// `reserved` maps every id this installation already owns (compiled
/// built-ins plus the remote/bundled catalog) to its label; a local entry
/// colliding with any of them is refused — local sources cannot shadow or
/// rebind reserved ids.
pub fn load_local_service_catalog(
    path: &Path,
    reserved: &HashMap<String, String>,
) -> Result<LocalCatalogLoadResult, LocalCatalogError> {
    if !path.exists() {
        return Ok(LocalCatalogLoadResult::default());
    }
    // Vanished between the existence check and stat: treat as absent —
    // the caller re-resolves on the next refresh.
    let Ok(metadata) = std::fs::metadata(path) else {
        return Ok(LocalCatalogLoadResult::default());
    };
    // Only regular files (symlinks to regular files included): FIFOs,
    // sockets and devices are refused so a special file never hangs the read.
    if !metadata.is_file() {
        return Err(LocalCatalogError::NotRegularFile {
            path: path.to_path_buf(),
        });
    }
    let bytes = read_bounded(path, MAX_LOCAL_CATALOG_BYTES)?;
    let file: LocalCatalogFile =
        serde_json::from_slice(&bytes).map_err(|error| LocalCatalogError::Json {
            path: path.to_path_buf(),
            line: error.line(),
            column: error.column(),
        })?;
    if file.version != 1 {
        return Err(LocalCatalogError::UnsupportedVersion {
            path: path.to_path_buf(),
        });
    }
    if file.entries.len() > MAX_LOCAL_CATALOG_ENTRIES {
        return Err(LocalCatalogError::TooManyEntries {
            path: path.to_path_buf(),
            count: file.entries.len(),
        });
    }
    let mut entries = Vec::with_capacity(file.entries.len());
    let mut seen_local = std::collections::HashSet::new();
    for (index, entry) in file.entries.iter().enumerate() {
        let refuse = |fault| {
            Err(LocalCatalogError::Entry {
                path: path.to_path_buf(),
                index,
                fault,
            })
        };
        if let Err(error) = entry.validate() {
            return refuse(LocalEntryFault::Invalid(error));
        }
        let id = entry.server.clone();
        if entry
            .provenance
            .iter()
            .any(|prov| prov.source != ProvenanceSource::User)
        {
            return refuse(LocalEntryFault::ForeignProvenance { id });
        }
        if entry.provenance.is_empty() {
            return refuse(LocalEntryFault::NoProvenance { id });
        }
        // Review status and legacy-builtin trust cannot be self-asserted.
        if entry.legacy_builtin {
            return refuse(LocalEntryFault::LegacyBuiltin { id });
        }
        if entry.verification.status != VerificationStatus::Unverified {
            return refuse(LocalEntryFault::Verified {
                id,
                status: match entry.verification.status {
                    VerificationStatus::MetadataReviewed => "metadata-reviewed",
                    VerificationStatus::Unverified => "unverified",
                },
            });
        }
        if entry.setup.readiness.is_some() {
            return refuse(LocalEntryFault::Readiness { id });
        }
        if !seen_local.insert(id.clone()) {
            return refuse(LocalEntryFault::Duplicate { id });
        }
        if let Some(label) = reserved.get(&id) {
            return refuse(LocalEntryFault::Reserved {
                id,
                label: label.clone(),
            });
        }
        entries.push(entry.clone());
    }
    Ok(LocalCatalogLoadResult {
        entries,
        path: Some(path.to_path_buf()),
    })
}

/// Bounded read: chunked until the running total exceeds `max_bytes`, so at
/// most `max_bytes` + one chunk is ever read before an oversized file is
/// refused from the read itself.
fn read_bounded(path: &Path, max_bytes: u64) -> Result<Vec<u8>, LocalCatalogError> {
    use std::io::Read;
    let unreadable = |source| LocalCatalogError::Read {
        path: path.to_path_buf(),
        source,
    };
    let file = std::fs::File::open(path).map_err(unreadable)?;
    let mut reader = std::io::BufReader::new(file);
    let mut chunks: Vec<u8> = Vec::new();
    let mut total: u64 = 0;
    loop {
        let mut chunk = vec![0u8; READ_CHUNK];
        let read = reader.read(&mut chunk).map_err(unreadable)?;
        if read == 0 {
            break;
        }
        total += read as u64;
        if total > max_bytes {
            return Err(LocalCatalogError::TooLarge {
                path: path.to_path_buf(),
                max_bytes,
            });
        }
        chunk.truncate(read);
        chunks.extend_from_slice(&chunk);
    }
    Ok(chunks)
}
