//! Where the tiny models live: installed files under
//! `<agent dir>/models/tiny/<id>/`, worker sockets, bind locks and logs
//! under `<agent dir>/run/tiny/`.

use std::io;
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::path::{Path, PathBuf};

/// The worker backend (one worker per model and backend).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Backend {
    /// ONNX Runtime (eukhe-tiny-onnx).
    Onnx,
}

impl Backend {
    #[must_use]
    pub fn id(self) -> &'static str {
        match self {
            Backend::Onnx => "onnx",
        }
    }

    /// Parses [`Backend::id`].
    #[must_use]
    pub fn parse(id: &str) -> Option<Backend> {
        match id {
            "onnx" => Some(Backend::Onnx),
            _ => None,
        }
    }
}

/// The two roots of the tiny-model files.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyHome {
    /// `<agent dir>/models/tiny`: one directory per installed model.
    pub models: PathBuf,
    /// `<agent dir>/run/tiny`: worker sockets, bind locks, logs.
    pub run: PathBuf,
    /// The agent dir both are under; a launched worker gets it.
    agent_dir: PathBuf,
}

impl TinyHome {
    /// The roots under an agent dir (`~/.eukhe`).
    #[must_use]
    pub fn under(agent_dir: &Path) -> TinyHome {
        TinyHome {
            models: agent_dir.join("models").join("tiny"),
            run: agent_dir.join("run").join("tiny"),
            agent_dir: agent_dir.to_path_buf(),
        }
    }

    /// The agent dir of [`TinyHome::under`].
    #[must_use]
    pub fn agent_dir(&self) -> &Path {
        &self.agent_dir
    }

    /// Creates the run dir and makes it, new or not, the user's only
    /// (0700): any process that reaches a worker socket in it may use it.
    pub(crate) fn create_run_dir(&self) -> io::Result<()> {
        std::fs::DirBuilder::new()
            .recursive(true)
            .mode(0o700)
            .create(&self.run)?;
        std::fs::set_permissions(&self.run, std::fs::Permissions::from_mode(0o700))
    }

    /// The install dir of a model.
    #[must_use]
    pub fn model_dir(&self, id: &str) -> PathBuf {
        self.models.join(id)
    }

    /// `<run>/<model>-<backend>` with `extension`.
    fn worker_file(&self, id: &str, backend: Backend, extension: &str) -> PathBuf {
        self.run.join(format!("{id}-{}.{extension}", backend.id()))
    }

    /// The worker's socket.
    #[must_use]
    pub fn socket(&self, id: &str, backend: Backend) -> PathBuf {
        self.worker_file(id, backend, "sock")
    }

    /// The lock a starting worker holds while it checks and binds.
    #[must_use]
    pub fn bind_lock(&self, id: &str, backend: Backend) -> PathBuf {
        self.worker_file(id, backend, "bind.lock")
    }

    /// The worker's log (its stderr).
    #[must_use]
    pub fn log(&self, id: &str, backend: Backend) -> PathBuf {
        self.worker_file(id, backend, "log")
    }
}
