//! Worker LSP requests over real supervisor connections: typed answers and
//! typed errors cross the link, and an unknown worker is refused.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_lsp::LspHost;
use eukhe_types::lsp::{LspError, LspOp, LspRequest, LspResponse, LspTarget};
use eukhe_types::platform::transport::TransportStream;
use serde_json::Map;
use tempfile::TempDir;

use super::LinkLsp;
use crate::registry::ResidentWorker;
use crate::supervisor::{Supervisor, SupervisorOptions};

fn descriptor(dir: &Path, token: &str) -> eukhe_types::daemon::DaemonWorkerDescriptor {
    eukhe_types::daemon::DaemonWorkerDescriptor {
        version: 1,
        worker_id: format!("w-{token}"),
        pid: 4242,
        process_start_id: None,
        socket_path: dir
            .join(format!("{token}.sock"))
            .to_string_lossy()
            .to_string(),
        recovery_journal_path: dir
            .join(format!("{token}-recovery.jsonl"))
            .to_string_lossy()
            .to_string(),
        orphan_process_journal_path: None,
        supervisor_socket_path: dir.join("d.sock").to_string_lossy().to_string(),
        authentication_token: token.to_string(),
        worker_instance_id: None,
        root_active_session_id: format!("a-{token}"),
        owner_client_id: None,
        root_session_id: None,
        session_file: None,
        session_dir: None,
        created_at: "t".to_string(),
        updated_at: "t".to_string(),
        lifecycle: eukhe_types::daemon::DaemonWorkerLifecycle::Ready,
        create_command: eukhe_types::daemon::DurableDaemonCreateCommand {
            session_path: None,
            no_session: None,
            rest: Map::default(),
        },
        consecutive_failures: 0,
        stop_requested_at: None,
        archive_on_stop: None,
        last_failure_at: None,
        last_error: None,
        rest: Map::default(),
    }
}

/// A supervisor serving `d.sock` with worker `a` registered.
async fn serve(dir: &TempDir) -> (PathBuf, tokio::task::JoinHandle<()>) {
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).unwrap();
    let socket = dir.path().join("d.sock");
    let supervisor = Arc::new(
        Supervisor::new(SupervisorOptions {
            socket_path: socket.clone(),
            agent_dir,
        })
        .unwrap(),
    );
    supervisor
        .registry
        .insert(ResidentWorker::new(
            "w-a".to_owned(),
            descriptor(dir.path(), "a"),
            dir.path().join("a.json"),
        ))
        .await;
    let listener = tokio::net::UnixListener::bind(&socket).unwrap();
    let accept = tokio::spawn(async move {
        while let Ok((stream, _)) = listener.accept().await {
            let supervisor = Arc::clone(&supervisor);
            let stream: Box<dyn TransportStream> = Box::new(stream);
            tokio::spawn(async move { supervisor.handle_client(stream).await });
        }
    });
    (socket, accept)
}

#[tokio::test]
async fn typed_answers_and_errors_cross_the_link() {
    let dir = TempDir::new().unwrap();
    let (socket, accept) = serve(&dir).await;
    let project = dir.path().join("project");
    std::fs::create_dir_all(&project).unwrap();
    let notes = project.join("notes.txt");
    std::fs::write(&notes, "text").unwrap();
    let worker = LinkLsp::new(socket.clone(), "a".to_owned());
    let request = |op| LspRequest {
        root: project.clone(),
        op,
    };
    assert_eq!(
        worker.call(request(LspOp::Status)).await,
        Ok(LspResponse::Status(Vec::new()))
    );
    let hover = LspOp::Hover {
        target: LspTarget {
            path: notes.clone(),
            line: 1,
            symbol: "text".to_owned(),
        },
    };
    assert_eq!(
        worker.call(request(hover)).await,
        Err(LspError::NoServer {
            root: project.clone(),
            path: notes,
        })
    );
    let stranger = LinkLsp::new(socket, "nobody".to_owned());
    assert_eq!(
        stranger.call(request(LspOp::Status)).await,
        Err(LspError::Unreachable {
            reason: "Worker authentication failed".to_owned(),
        })
    );
    accept.abort();
}
