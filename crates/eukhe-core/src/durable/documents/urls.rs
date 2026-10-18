//! The `read` function's internal URLs (docs/tools.md S7): `repo://` and
//! `skill://` read a file or directory under their root through the
//! session's documents (anchorable like any read); `agent://` reads a
//! subagent's chat, `memory://` the chat memory, `mcp://` an MCP server's
//! resources (through the kernel, where the MCP client runs), and `ssh://`
//! a file of a host that `ssh.hosts` allows (through the user's own
//! `ssh`, [`super::ssh`]), as text. The path is confined by
//! [`Url::names`] and [`Url::remote`]: a `..` above the scheme's root is
//! an `escapes` rejection, never clamped; a file-backed read whose real
//! path leaves the root's real path through a symlink is one too.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_docs::{Located, Scheme, Url, UrlError};
use eukhe_durable::harness::types::ToolExecutionApi;
use serde::Deserialize;
use tokio::task::JoinError;

use super::contract::Function;
use super::requests::{
    read_rejection, read_reply, url_rejection, Done, Performed, ReadReply, Rejection,
};
use super::ssh::{SshError, SshRead};
use super::DocumentsHost;
use crate::durable::optchat::agent_chat;
use crate::durable::tool_surface::kernel_manager;
use crate::kernel::manager::McpResource;
use crate::memory::Zoomed;

/// How long one MCP server may take to list or read a resource.
const MCP_TIMEOUT_MS: u64 = 30_000;

/// One entry of an MCP server's resource listing (the kernel's
/// `mcp_resource` reply).
#[derive(Deserialize)]
struct ListedResource {
    uri: String,
    #[serde(default)]
    name: String,
    #[serde(rename = "mimeType")]
    mime_type: Option<String>,
    #[serde(default)]
    description: String,
}

/// One part of a read MCP resource: its text, or the size of its bytes.
#[derive(Deserialize)]
struct ResourcePart {
    uri: String,
    #[serde(rename = "mimeType")]
    mime_type: Option<String>,
    text: Option<String>,
    size: Option<u64>,
}

/// The file-backed roots.
#[derive(Clone, Copy)]
enum Root {
    /// `repo://`: the workspace root.
    Workspace,
    /// `skill://<name>`: the directory of the skill `name`.
    Skills,
}

impl Root {
    /// The file or directory `names` (root first) reach and the root its
    /// real path must stay under; `None` when no skill has the first name.
    fn locate(self, host: &DocumentsHost, names: &[&str]) -> Option<Located> {
        match self {
            Root::Workspace => Some(Located {
                root: host.workspace.clone(),
                path: joined(&host.workspace, names),
            }),
            Root::Skills => {
                let (name, rest) = names.split_first()?;
                let skill = host
                    .resources
                    .skills
                    .iter()
                    .find(|skill| skill.name == *name)?;
                Some(Located {
                    root: skill.base_dir.clone(),
                    path: if rest.is_empty() {
                        skill.file_path.clone()
                    } else {
                        joined(&skill.base_dir, rest)
                    },
                })
            }
        }
    }
}

fn joined(root: &Path, names: &[&str]) -> PathBuf {
    names
        .iter()
        .fold(root.to_path_buf(), |path, name| path.join(name))
}

fn rejection(reason: &'static str, message: &impl ToString) -> Rejection {
    Rejection::new(Function::Read, reason, message)
}

/// A URL the scheme's root does not serve: unknown scheme or escape.
pub(super) fn url_error(error: &UrlError) -> Rejection {
    rejection(url_rejection(error), error)
}

/// A count in a `memory://` path.
fn count(segment: &str) -> Result<u64, Rejection> {
    segment.parse().map_err(|_| {
        rejection(
            "arguments",
            &format!("memory://: `{segment}` is not a message id or line count"),
        )
    })
}

/// Read `url`. `cwd` shortens display paths; `api` is the tool call the
/// read runs in (`agent://` needs it: the subagents are its
/// conversation's). The outer error is a failed file worker.
#[tracing::instrument(name = "documents.read_url", skip_all, fields(scheme = url.scheme.name()))]
pub(super) async fn read(
    host: &Arc<DocumentsHost>,
    api: Option<Arc<dyn ToolExecutionApi>>,
    cwd: PathBuf,
    url: Url<'_>,
    cx: &Context,
) -> Result<Result<Performed, Rejection>, JoinError> {
    let zoomed = match url.scheme {
        Scheme::Repo => return file(host, cwd, url, Root::Workspace).await,
        Scheme::Skill => return file(host, cwd, url, Root::Skills).await,
        Scheme::Agent => async {
            let names = url.names().map_err(|error| url_error(&error))?;
            let [name] = names.as_slice() else {
                return Err(rejection(
                    "arguments",
                    &"agent://<name|id> names one subagent",
                ));
            };
            let Some(api) = api else {
                return Err(rejection(
                    "arguments",
                    &"agent:// reads the subagents of a tool call's conversation; there is none",
                ));
            };
            let text = agent_chat(&*api, api.conversation_id(), name, cx)
                .await
                .map_err(|error| rejection("io", &error))?;
            Ok(Zoomed {
                text,
                images: Vec::new(),
            })
        }
        .await,
        Scheme::Memory => {
            async {
                let names = url.names().map_err(|error| url_error(&error))?;
                let Some(memory) = host.memory.as_ref() else {
                    return Err(rejection("not_found", &"this session has no chat memory"));
                };
                let zoomed = match names.as_slice() {
                    [] => memory.render().await.map(|view| Zoomed {
                        text: view.text,
                        images: Vec::new(),
                    }),
                    [id] => memory.zoom(count(id)?, 1).await,
                    [id, lines] => match count(lines)? {
                        0 => {
                            return Err(rejection("arguments", &"memory://<id>/<n>: n starts at 1"))
                        }
                        lines => memory.zoom(count(id)?, lines).await,
                    },
                    [_, _, _, ..] => {
                        return Err(rejection("arguments", &"memory:// takes at most <id>/<n>"))
                    }
                };
                zoomed.map_err(|error| rejection("io", &format!("{error:#}")))
            }
            .await
        }
        Scheme::Mcp => {
            async {
                let Some(api) = api else {
                    return Err(rejection(
                        "arguments",
                        &"mcp:// reads through the read tool; in the kernel, `await mcp.read_resource(server, uri)`",
                    ));
                };
                let Some(deps) = host.deps.upgrade() else {
                    return Err(rejection("io", &"the session is closing"));
                };
                let (server, uri) = url.path.split_once('/').unwrap_or((url.path, ""));
                if !deps.generic_mcp_servers.iter().any(|known| known == server) {
                    return Err(rejection(
                        "not_found",
                        &format!(
                            "No MCP server {server} in this session; its servers: {}",
                            match deps.generic_mcp_servers.as_slice() {
                                [] => "none".to_owned(),
                                servers => servers.join(", "),
                            }
                        ),
                    ));
                }
                let request = if uri.is_empty() {
                    McpResource::List
                } else {
                    McpResource::Read { uri }
                };
                let manager = kernel_manager(&deps, &*api, cx)
                    .await
                    .map_err(|error| rejection("io", &error))?;
                let value = manager
                    .mcp_resource(server, request, MCP_TIMEOUT_MS)
                    .await
                    .map_err(|error| rejection("io", &error))?;
                let malformed = |error: serde_json::Error| {
                    rejection("io", &format!("mcp://{server}: malformed reply: {error}"))
                };
                let text = match request {
                    McpResource::List => {
                        let listed: Vec<ListedResource> =
                            serde_json::from_value(value).map_err(malformed)?;
                        if listed.is_empty() {
                            format!("mcp://{server} has no resources.")
                        } else {
                            listed
                                .iter()
                                .map(|resource| {
                                    format!(
                                        "mcp://{server}/{}\t{}\t{}\t{}",
                                        resource.uri,
                                        resource.name,
                                        resource.mime_type.as_deref().unwrap_or("-"),
                                        resource.description
                                    )
                                })
                                .collect::<Vec<_>>()
                                .join("\n")
                        }
                    }
                    McpResource::Read { .. } => {
                        let parts: Vec<ResourcePart> =
                            serde_json::from_value(value).map_err(malformed)?;
                        parts
                            .into_iter()
                            .map(|part| match (part.text, part.size) {
                                (Some(text), _) => text,
                                (None, size) => format!(
                                    "[binary resource {}: {} bytes, {}]",
                                    part.uri,
                                    size.unwrap_or(0),
                                    part.mime_type.as_deref().unwrap_or("unknown type")
                                ),
                            })
                            .collect::<Vec<_>>()
                            .join("\n")
                    }
                };
                Ok(Zoomed {
                    text,
                    images: Vec::new(),
                })
            }
            .await
        }
        Scheme::Ssh => {
            async {
                let remote = url.remote().map_err(|error| url_error(&error))?;
                let ssh_rejection = |error: SshError| rejection(error.reason(), &error);
                let Some(api) = api else {
                    return Err(ssh_rejection(SshError::NoCall));
                };
                let Some(deps) = host.deps.upgrade() else {
                    return Err(rejection("io", &"the session is closing"));
                };
                let authored = format!("ssh://{}", url.path);
                let read = SshRead::new(
                    OsStr::new("ssh"),
                    &authored,
                    remote,
                    &deps.settings.manager().get_ssh_hosts(),
                    deps.blocking_budget(),
                    api.truncation().max_bytes(),
                )
                .map_err(ssh_rejection)?;
                let text = read.run().await.map_err(ssh_rejection)?;
                Ok(Zoomed {
                    text,
                    images: Vec::new(),
                })
            }
            .await
        }
    };
    let authored = format!("{}://{}", url.scheme.name(), url.path);
    Ok(zoomed.map(|zoomed| Performed {
        done: Done::Read(ReadReply::text(authored, zoomed.text)),
        images: zoomed.images,
    }))
}

/// A file-backed URL under `root`, read on a blocking thread.
#[tracing::instrument(name = "documents.read_file_url", skip_all)]
async fn file(
    host: &Arc<DocumentsHost>,
    cwd: PathBuf,
    url: Url<'_>,
    root: Root,
) -> Result<Result<Performed, Rejection>, JoinError> {
    let host = Arc::clone(host);
    let (scheme, path) = (url.scheme, url.path.to_owned());
    tokio::task::spawn_blocking(move || {
        let url = Url {
            scheme,
            path: &path,
        };
        host.documents
            .read_under(&cwd, url, |names| root.locate(&host, names))
            .map(|view| Performed {
                done: Done::Read(read_reply(view)),
                images: Vec::new(),
            })
            .map_err(|error| rejection(read_rejection(&error), &error))
    })
    .await
}
