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
    run_text, Pick, Role, RoleSettings, RoleUnavailable, TextBackends, TinyClient, TinyHome,
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
    fn open() -> Result<Self, String> {
        let agent_dir = get_agent_dir();
        let cwd = std::env::current_dir().map_err(|error| format!("Cannot read cwd: {error}"))?;
        let settings = SettingsManager::create(&cwd, &agent_dir);
        let worker_exe = eukhe_core::tiny::worker_exe()
            .map_err(|error| format!("Cannot find the {APP_NAME} executable: {error}"))?;
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
    fn local_model(&self, role: Role) -> Result<&'static CatalogModel, String> {
        let settings = self.role_settings(role);
        match eukhe_core::tiny::resolve(role, &settings, &self.home, "") {
            Pick::Use(candidate) => match candidate.local_model() {
                Some(model) => Ok(model),
                None => Err(format!("the {} role takes local models only", role.id())),
            },
            Pick::Unavailable => Err(RoleUnavailable::new(role, &settings, "").to_string()),
        }
    }
}

fn block_on<T>(future: impl Future<Output = T>) -> Result<T, String> {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|error| error.to_string())?;
    Ok(runtime.block_on(future))
}

/// Prints `result`'s error and maps it to an exit code.
fn exit(result: Result<(), String>) -> i32 {
    match result {
        Ok(()) => 0,
        Err(error) => {
            eprintln!("Error: {error}");
            1
        }
    }
}

/// `eukhe translate <lang> <text...>`.
pub fn run_translate_command(args: &[String]) -> i32 {
    exit(translate(args))
}

fn translate(args: &[String]) -> Result<(), String> {
    let usage = || format!("Usage: {APP_NAME} translate <lang> <text...>");
    let (language, words) = args.split_first().ok_or_else(usage)?;
    let text = words.join(" ");
    if text.trim().is_empty() {
        return Err(usage());
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
                            return Err(RoleUnavailable::new(Role::Translate, &settings, &selector)
                                .to_string())
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
        .await
        .map_err(|error| error.to_string())?;
        println!("{}", eukhe_tiny::translation_text(&reply));
        Ok(())
    })?
}

/// The model collection and the default provider model (the one a fresh
/// session would use), when one has credentials.
#[tracing::instrument(skip_all)]
async fn default_model(
    context: &RoleContext,
) -> Result<(eukhe_ai::models::Models, Option<Model>), String> {
    let models = eukhe_core::durable::create_models(&context.agent_dir)
        .map_err(|error| error.to_string())?;
    let resolved = eukhe_core::durable::resolve_session_model(
        &models,
        &context.settings,
        None,
        None,
        &BACKGROUND_CONTEXT,
    )
    .await
    .map_err(|error| error.to_string())?;
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

fn parse_say(args: &[String]) -> Result<SayArgs, String> {
    let usage = || format!("Usage: {APP_NAME} say <text...> [--out <file.wav>] [--voice <id>]");
    let mut words = Vec::new();
    let mut out = None;
    let mut voice = None;
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--out" => out = Some(PathBuf::from(rest.next().ok_or_else(usage)?)),
            "--voice" => voice = Some(rest.next().ok_or_else(usage)?.clone()),
            _ => words.push(arg.as_str()),
        }
    }
    let text = words.join(" ");
    if text.trim().is_empty() {
        return Err(usage());
    }
    Ok(SayArgs { text, out, voice })
}

/// `eukhe say <text...> [--out file.wav] [--voice id]`.
pub fn run_say_command(args: &[String]) -> i32 {
    exit(say(args))
}

fn say(args: &[String]) -> Result<(), String> {
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
    let audio =
        block_on(context.client.speak(model, request))?.map_err(|error| error.to_string())?;
    match args.out {
        Some(out) => eukhe_tiny_onnx::write_wav(&out, &audio).map_err(|error| error.to_string()),
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
fn play(audio: &eukhe_tiny::Audio) -> Result<(), String> {
    let Some(player) = find_player(std::env::var_os("PATH").as_deref()) else {
        return Err(format!(
            "no audio player found ({}); write the speech to a file with --out <file.wav>",
            PLAYERS.join(", ")
        ));
    };
    let wav = std::env::temp_dir().join(format!("eukhe-say-{}.wav", std::process::id()));
    eukhe_tiny_onnx::write_wav(&wav, audio).map_err(|error| error.to_string())?;
    let status = std::process::Command::new(&player).arg(&wav).status();
    let _ = std::fs::remove_file(&wav);
    match status {
        Ok(status) if status.success() => Ok(()),
        Ok(status) => Err(format!("{} exited with {status}", player.display())),
        Err(error) => Err(format!("{}: {error}", player.display())),
    }
}

/// `transcribe` arguments.
#[derive(Debug, PartialEq)]
struct TranscribeArgs {
    file: PathBuf,
    language: String,
}

fn parse_transcribe(args: &[String]) -> Result<TranscribeArgs, String> {
    let usage = || format!("Usage: {APP_NAME} transcribe <file.wav> [--language <code>]");
    let mut file = None;
    let mut language = String::new();
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--language" => language.clone_from(rest.next().ok_or_else(usage)?),
            _ if file.is_none() => file = Some(PathBuf::from(arg)),
            _ => return Err(usage()),
        }
    }
    Ok(TranscribeArgs {
        file: file.ok_or_else(usage)?,
        language,
    })
}

/// `eukhe transcribe <file.wav> [--language xx]`.
pub fn run_transcribe_command(args: &[String]) -> i32 {
    exit(transcribe(args))
}

fn transcribe(args: &[String]) -> Result<(), String> {
    let args = parse_transcribe(args)?;
    let audio =
        eukhe_tiny_onnx::read_wav(Path::new(&args.file)).map_err(|error| error.to_string())?;
    let context = RoleContext::open()?;
    let model = context.local_model(Role::Dictation)?;
    let request = TranscribeRequest {
        audio,
        language: args.language,
    };
    let transcript =
        block_on(context.client.transcribe(model, request))?.map_err(|error| error.to_string())?;
    println!("{}", transcript.text.trim());
    Ok(())
}

#[cfg(test)]
mod tests;
