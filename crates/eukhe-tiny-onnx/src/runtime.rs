//! ONNX Runtime, loaded at run time from the system library (CPU).

use std::path::{Path, PathBuf};
use std::sync::{Mutex, PoisonError};

use eukhe_tiny::{Device, EngineOptions, WorkerFailure};
use ort::environment::Environment;
use ort::session::builder::GraphOptimizationLevel;
use ort::session::Session;

/// The devices this engine runs on.
const CPU: &str = "cpu";

/// The process's ONNX Runtime environment, built by the first session: ort
/// allows one environment per process, ever (even after it is dropped), so
/// every [`Runtime`] shares it. Its library is the first runtime's.
static ENVIRONMENT: Mutex<Option<Environment>> = Mutex::new(None);

/// The runtime library the process's environment loads from.
pub(crate) struct Runtime {
    library: PathBuf,
}

impl Runtime {
    /// Checks the options; loads nothing.
    pub(crate) fn new(options: &EngineOptions) -> Result<Runtime, WorkerFailure> {
        match &options.device {
            Device::Cpu => {}
            Device::Other(word) => {
                return Err(WorkerFailure::Load {
                    message: format!("device `{word}` is not supported (only `{CPU}`)"),
                });
            }
        }
        let library = library_path(&options.runtime_library, std::env::var_os("ORT_DYLIB_PATH"));
        Ok(Runtime { library })
    }

    /// A CPU session of the ONNX file at `model` (loads the runtime first).
    pub(crate) fn session(&self, model: &Path) -> Result<Session, WorkerFailure> {
        let load = |message: String| WorkerFailure::Load { message };
        let environment = {
            let mut shared = ENVIRONMENT.lock().unwrap_or_else(PoisonError::into_inner);
            if let Some(environment) = &*shared {
                environment.clone()
            } else {
                let environment = ort::init_from(&self.library)
                    .map_err(|error| {
                        load(format!(
                            "ONNX Runtime library {}: {error}",
                            self.library.display()
                        ))
                    })?
                    .with_name("eukhe-tiny")
                    .build()
                    .map_err(|error| load(format!("ONNX Runtime environment: {error}")))?;
                shared.insert(environment).clone()
            }
        };
        Session::builder(&environment)
            .map_err(|error| load(error.to_string()))
            .and_then(|builder| {
                builder
                    .with_optimization_level(GraphOptimizationLevel::Level3)
                    .map_err(|error| load(error.to_string()))
            })
            .and_then(|mut builder| {
                builder
                    .commit_from_file(model)
                    .map_err(|error| load(format!("{}: {error}", model.display())))
            })
    }
}

fn library_path(option: &Path, env: Option<std::ffi::OsString>) -> PathBuf {
    if !option.as_os_str().is_empty() {
        return option.to_owned();
    }
    match env {
        Some(path) if !path.is_empty() => PathBuf::from(path),
        Some(_) | None => PathBuf::from(format!(
            "{}onnxruntime{}",
            std::env::consts::DLL_PREFIX,
            std::env::consts::DLL_SUFFIX
        )),
    }
}
