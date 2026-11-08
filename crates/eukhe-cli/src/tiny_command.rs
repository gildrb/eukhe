//! The S9 local-model commands: `translate` (role `translate`), `say`
//! (role `speech`), `transcribe` (role `dictation`), and the hidden
//! `tiny-worker` entry the tiny client spawns. A role resolves to the first
//! available model of its chain (`eukhe_core::tiny`); with none it fails
//! naming the chain and the download command. Speech and dictation are
//! local only; a translate chain may end on the default provider model.

use std::future::Future;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::settings::SettingsManager;
use eukhe_core::tiny::{
    run_text, Candidate, Pick, Role, RoleSettings, RoleUnavailable, TextBackends, TinyClient,
    TinyHome,
};
use eukhe_tiny::{CatalogModel, SpeakRequest, TranscribeRequest};
use eukhe_types::pi_ai::Model;

use crate::config::{get_agent_dir, APP_NAME};

/// The audio players `say` tries, in order.
const PLAYERS: [&str; 3] = ["pw-play", "paplay", "aplay"];

/// `eukhe tiny-worker <model> --backend onnx ...`: the shared worker of one
/// model (spawned by the tiny client, never by hand).
pub fn run_tiny_worker(args: &[String]) -> i32 {
    let runtime = match tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            eprintln!("Error: {error}");
            return 1;
        }
    };
    let code = runtime.block_on(eukhe_tiny::run_worker(args, eukhe_tiny_onnx::open));
    i32::from(code != ExitCode::SUCCESS)
}

/// What every role command reads: the settings, the tiny home, the client.
struct RoleContext {
    agent_dir: PathBuf,
    settings: SettingsManager,
    home: TinyHome,
    client: TinyClient,
}

impl RoleContext {
    fn open() -> Result<Self, TinyCommandError> {
        let cwd = std::env::current_dir().map_err(TinyCommandError::Cwd)?;
        Self::in_dirs(&cwd, get_agent_dir())
    }

    /// The settings of `cwd` and the tiny home and client of `agent_dir`.
    fn in_dirs(cwd: &Path, agent_dir: PathBuf) -> Result<Self, TinyCommandError> {
        let settings = SettingsManager::create(cwd, &agent_dir);
        let worker_exe = eukhe_core::tiny::worker_exe().map_err(TinyCommandError::WorkerExe)?;
        let client = eukhe_core::tiny::client(&agent_dir, settings.cvars(), worker_exe);
        Ok(Self {
            home: TinyHome::under(&agent_dir),
            agent_dir,
            settings,
            client,
        })
    }

    fn role_settings(&self, role: Role) -> RoleSettings {
        eukhe_core::tiny::role_settings(self.settings.cvars(), role)
    }

    /// The local model `role` resolves to (speech and dictation).
    fn local_model(&self, role: Role) -> Result<&'static CatalogModel, TinyCommandError> {
        let settings = self.role_settings(role);
        match eukhe_core::tiny::resolve(role, &settings, &self.home, "") {
            Pick::Use(candidate) => candidate
                .local_model()
                .ok_or(TinyCommandError::LocalOnly(role)),
            Pick::Unavailable => Err(RoleUnavailable::new(role, &settings, "").into()),
        }
    }
}

/// The usage line a malformed role command prints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
enum TinyUsage {
    #[error("Usage: {} translate <lang> <text...>", APP_NAME)]
    Translate,
    #[error("Usage: {} say <text...> [--out <file.wav>] [--voice <id>]", APP_NAME)]
    Say,
    #[error("Usage: {} transcribe <file.wav> [--language <code>]", APP_NAME)]
    Transcribe,
}

/// Why a role command (`translate`, `say`, `transcribe`, the TUI's
/// dictation transcriber) failed; [`exit`] prints it.
#[derive(Debug, thiserror::Error)]
enum TinyCommandError {
    #[error(transparent)]
    Usage(#[from] TinyUsage),
    #[error("Cannot read cwd: {0}")]
    Cwd(#[source] std::io::Error),
    #[error("Cannot find the {app} executable: {0}", app = APP_NAME)]
    WorkerExe(#[source] std::io::Error),
    /// The command's tokio runtime did not start.
    #[error("{0}")]
    Runtime(#[source] std::io::Error),
    #[error("the {} role takes local models only", .0.id())]
    LocalOnly(Role),
    #[error("{0}")]
    Unavailable(#[from] RoleUnavailable),
    #[error("{0}")]
    DefaultModel(#[source] eukhe_core::durable::ModelsError),
    #[error("{0}")]
    Run(#[from] eukhe_core::tiny::RoleRunError),
    #[error("{source} (model {model}; modelRoles.translate picks another)")]
    Translation {
        model: String,
        #[source]
        source: eukhe_tiny::TranslationError,
    },
    #[error("{0}")]
    Worker(#[from] eukhe_tiny::TinyError),
    #[error("{0}")]
    Audio(#[from] eukhe_tiny_onnx::AudioFileError),
    #[error("no audio player found ({}); write the speech to a file with --out <file.wav>", PLAYERS.join(", "))]
    NoPlayer,
    #[error("{} exited with {status}", .player.display())]
    PlayerExit {
        player: PathBuf,
        status: std::process::ExitStatus,
    },
    #[error("{}: {source}", .player.display())]
    PlayerSpawn {
        player: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

fn block_on<T>(future: impl Future<Output = T>) -> Result<T, TinyCommandError> {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(TinyCommandError::Runtime)?;
    Ok(runtime.block_on(future))
}

/// Prints `result`'s error and maps it to an exit code: a usage error
/// exits 2, everything else 1.
fn exit(result: Result<(), TinyCommandError>) -> i32 {
    match result {
        Ok(()) => 0,
        Err(error) => {
            eprintln!("Error: {error}");
            match error {
                TinyCommandError::Usage(_) => 2,
                _ => 1,
            }
        }
    }
}

/// `eukhe translate <lang> <text...>`.
pub fn run_translate_command(args: &[String]) -> i32 {
    exit(translate(args))
}

fn translate(args: &[String]) -> Result<(), TinyCommandError> {
    let (language, words) = args.split_first().ok_or(TinyUsage::Translate)?;
    let text = words.join(" ");
    if text.trim().is_empty() {
        return Err(TinyUsage::Translate.into());
    }
    let context = RoleContext::open()?;
    let settings = context.role_settings(Role::Translate);
    block_on(async {
        // Local models first; the default provider model only when the
        // chain gets that far.
        let (candidate, models, session) =
            match eukhe_core::tiny::resolve(Role::Translate, &settings, &context.home, "") {
                Pick::Use(candidate) => (candidate, None, None),
                Pick::Unavailable => {
                    let (models, session) = default_model(&context).await?;
                    let selector = session
                        .as_ref()
                        .map(eukhe_core::tiny::model_selector)
                        .unwrap_or_default();
                    match eukhe_core::tiny::resolve(
                        Role::Translate,
                        &settings,
                        &context.home,
                        &selector,
                    ) {
                        Pick::Use(candidate) => (candidate, Some(models), session),
                        Pick::Unavailable => {
                            return Err(
                                RoleUnavailable::new(Role::Translate, &settings, &selector).into()
                            )
                        }
                    }
                }
            };
        let backends = TextBackends {
            client: &context.client,
            models: models.as_ref(),
            session_model: session.as_ref(),
        };
        let reply = run_text(
            &candidate,
            eukhe_tiny::translate_request(language, &text),
            &backends,
        )
        .await?;
        let translation =
            eukhe_tiny::translation_text(language, &text, &reply).map_err(|source| {
                let model = match &candidate {
                    Candidate::Local(id) => format!("{}{id}", eukhe_tiny::LOCAL_PREFIX),
                    Candidate::Remote(selector) => selector.clone(),
                };
                TinyCommandError::Translation { model, source }
            })?;
        println!("{translation}");
        Ok(())
    })?
}

/// The model collection and the default provider model (the one a fresh
/// session would use), when one has credentials. The models.json errors
/// and a saved chat model that did not run go to stderr.
#[tracing::instrument(skip_all)]
async fn default_model(
    context: &RoleContext,
) -> Result<(eukhe_ai::models::Models, Option<Model>), TinyCommandError> {
    let loaded = eukhe_core::durable::create_models(&context.agent_dir);
    if !loaded.diagnostics.is_empty() {
        eprintln!(
            "Warning: errors loading models.json:\n{}",
            loaded.diagnostics.join("\n")
        );
    }
    let models = loaded.models;
    let resolved = eukhe_core::durable::resolve_session_model(
        &models,
        &context.settings,
        None,
        None,
        &BACKGROUND_CONTEXT,
    )
    .await
    .map_err(TinyCommandError::DefaultModel)?;
    if let Some(substitution) = resolved
        .as_ref()
        .and_then(|resolved| resolved.substituted.as_ref())
    {
        eprintln!("Warning: {}", substitution.missed());
    }
    let model = resolved
        .and_then(|resolved| models.get_model(&resolved.model.provider, &resolved.model.model_id));
    Ok((models, model))
}

/// `say` arguments.
#[derive(Debug, PartialEq)]
struct SayArgs {
    text: String,
    out: Option<PathBuf>,
    voice: Option<String>,
}

fn parse_say(args: &[String]) -> Result<SayArgs, TinyUsage> {
    let mut words = Vec::new();
    let mut out = None;
    let mut voice = None;
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--out" => out = Some(PathBuf::from(rest.next().ok_or(TinyUsage::Say)?)),
            "--voice" => voice = Some(rest.next().ok_or(TinyUsage::Say)?.clone()),
            _ => words.push(arg.as_str()),
        }
    }
    let text = words.join(" ");
    if text.trim().is_empty() {
        return Err(TinyUsage::Say);
    }
    Ok(SayArgs { text, out, voice })
}

/// `eukhe say <text...> [--out file.wav] [--voice id]`.
pub fn run_say_command(args: &[String]) -> i32 {
    exit(say(args))
}

fn say(args: &[String]) -> Result<(), TinyCommandError> {
    let args = parse_say(args)?;
    let context = RoleContext::open()?;
    let model = context.local_model(Role::Speech)?;
    let request = SpeakRequest {
        text: args.text,
        voice: args
            .voice
            .unwrap_or_else(|| eukhe_core::tiny::local_voice(context.settings.cvars())),
        speed: 1.0,
    };
    let audio = block_on(context.client.speak(model, request))??;
    match args.out {
        Some(out) => Ok(eukhe_tiny_onnx::write_wav(&out, &audio)?),
        None => play(&audio),
    }
}

/// The first of [`PLAYERS`] on `PATH`.
fn find_player(path: Option<&std::ffi::OsStr>) -> Option<PathBuf> {
    let dirs: Vec<PathBuf> = std::env::split_paths(path?).collect();
    PLAYERS.iter().find_map(|player| {
        dirs.iter()
            .map(|dir| dir.join(player))
            .find(|candidate| candidate.is_file())
    })
}

/// Plays `audio` through a temp WAV with the first player found.
fn play(audio: &eukhe_tiny::Audio) -> Result<(), TinyCommandError> {
    let Some(player) = find_player(std::env::var_os("PATH").as_deref()) else {
        return Err(TinyCommandError::NoPlayer);
    };
    let wav = std::env::temp_dir().join(format!("eukhe-say-{}.wav", std::process::id()));
    eukhe_tiny_onnx::write_wav(&wav, audio)?;
    let status = std::process::Command::new(&player).arg(&wav).status();
    let _ = std::fs::remove_file(&wav);
    match status {
        Ok(status) if status.success() => Ok(()),
        Ok(status) => Err(TinyCommandError::PlayerExit { player, status }),
        Err(source) => Err(TinyCommandError::PlayerSpawn { player, source }),
    }
}

/// `transcribe` arguments.
#[derive(Debug, PartialEq)]
struct TranscribeArgs {
    file: PathBuf,
    language: String,
}

fn parse_transcribe(args: &[String]) -> Result<TranscribeArgs, TinyUsage> {
    let mut file = None;
    let mut language = String::new();
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--language" => language.clone_from(rest.next().ok_or(TinyUsage::Transcribe)?),
            _ if file.is_none() => file = Some(PathBuf::from(arg)),
            _ => return Err(TinyUsage::Transcribe),
        }
    }
    Ok(TranscribeArgs {
        file: file.ok_or(TinyUsage::Transcribe)?,
        language,
    })
}

/// `eukhe transcribe <file.wav> [--language xx]`.
pub fn run_transcribe_command(args: &[String]) -> i32 {
    exit(transcribe(args))
}

fn transcribe(args: &[String]) -> Result<(), TinyCommandError> {
    let args = parse_transcribe(args)?;
    let cwd = std::env::current_dir().map_err(TinyCommandError::Cwd)?;
    let text = block_on(transcribe_file(
        cwd,
        get_agent_dir(),
        args.file,
        args.language,
    ))??;
    println!("{text}");
    Ok(())
}

/// The trimmed text of the WAV file `wav`, read by the `dictation` role's
/// local model (settings of `cwd` and `agent_dir`); `language` empty
/// detects the language.
#[tracing::instrument]
async fn transcribe_file(
    cwd: PathBuf,
    agent_dir: PathBuf,
    wav: PathBuf,
    language: String,
) -> Result<String, TinyCommandError> {
    let audio = eukhe_tiny_onnx::read_wav(&wav)?;
    let context = RoleContext::in_dirs(&cwd, agent_dir)?;
    let model = context.local_model(Role::Dictation)?;
    let transcript = context
        .client
        .transcribe(model, TranscribeRequest { audio, language })
        .await?;
    Ok(transcript.text.trim().to_owned())
}

/// The TUI's dictation transcriber: [`transcribe_file`] in the session's
/// cwd and agent dir, with the language detected.
pub(crate) struct RoleTranscriber {
    pub(crate) cwd: PathBuf,
    pub(crate) agent_dir: PathBuf,
}

impl eukhe_tui::dictation::Transcriber for RoleTranscriber {
    fn transcribe(&self, wav: PathBuf) -> eukhe_tui::dictation::DictationFuture<String> {
        let (cwd, agent_dir) = (self.cwd.clone(), self.agent_dir.clone());
        Box::pin(async move {
            transcribe_file(cwd, agent_dir, wav, String::new())
                .await
                .map_err(|error| eukhe_tui::dictation::DictationError::Backend(Box::new(error)))
        })
    }
}

#[cfg(test)]
mod tests;
