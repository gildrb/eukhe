//! Dictation into the editor draft: a key records
//! the microphone into a 16 kHz mono WAV file, the `dictation` role turns
//! the file into text, and the text goes into the draft at the cursor.
//!
//! Two actions start a take: `app.stt.pushToTalk` records while the key is
//! held (the terminal sends the key again at each auto-repeat; a gap ends
//! the hold), and `app.stt.toggle` records until its next press. Neither
//! has a default key. A take runs in its own task: recording, then
//! transcribing. Esc aborts the task; the temporary WAV file goes with it.
//!
//! The capture is a recorder program (`pw-record`, `parec` or `arecord`;
//! on macOS `sox` or `ffmpeg`) that writes raw 16-bit samples to its
//! stdout. No audio library links into the build.

use std::future::Future;
use std::path::{Path, PathBuf};
use std::pin::Pin;
use std::process::Stdio;
use std::sync::Arc;
use std::time::Duration;

use tokio::io::{AsyncReadExt, BufReader};
use tokio::sync::{mpsc, oneshot};

/// The sample rate of every take (the rate whisper reads).
pub const SAMPLE_RATE: u32 = 16_000;

/// The longest wait for the first auto-repeat of a held key: longer than
/// the usual key-repeat delays (X11 660 ms, GNOME 500 ms).
const HOLD_FIRST_REPEAT: Duration = Duration::from_millis(800);

/// The longest gap between two auto-repeats of a held key; a longer gap
/// is the release.
const HOLD_RELEASE: Duration = Duration::from_millis(300);

/// The boxed future of the dictation backends; the error is the text the
/// error row shows.
pub type DictationFuture<T> = Pin<Box<dyn Future<Output = Result<T, String>> + Send>>;

/// Records the microphone. An implementation captures from the default
/// input device until `stop` resolves (a dropped sender counts as a
/// resolve), then writes the take to `wav` as a 16 kHz mono 16-bit PCM
/// WAV file. A capture that ends by itself also writes the file and
/// succeeds; a capture that fails gives the reason. A dropped future
/// stops the capture and leaves no process behind.
pub trait Recorder: Send + Sync {
    fn record(&self, wav: PathBuf, stop: oneshot::Receiver<()>) -> DictationFuture<()>;
}

/// Turns a WAV file into text through the `dictation` role (the first
/// available model of its chain). An implementation reads `wav` and gives
/// the trimmed transcript (empty when it heard no speech), or the reason
/// it could not (no model of the chain installed, a worker failure).
pub trait Transcriber: Send + Sync {
    fn transcribe(&self, wav: PathBuf) -> DictationFuture<String>;
}

/// The dictation backends the interactive options carry.
#[derive(Clone)]
pub struct Dictation {
    pub recorder: Arc<dyn Recorder>,
    pub transcriber: Arc<dyn Transcriber>,
}

impl std::fmt::Debug for Dictation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Dictation").finish_non_exhaustive()
    }
}

/// How a take ends its recording.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Trigger {
    /// `app.stt.pushToTalk`: while the key is held.
    Hold,
    /// `app.stt.toggle`: until the next toggle press.
    Toggle,
}

/// A dictation key press for the take that records.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Signal {
    /// The push-to-talk key again: the hold goes on.
    Held,
    /// The toggle key: the recording ends.
    Stop,
}

/// What a take does now; the status line shows it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    Recording,
    Transcribing,
}

/// A step of a take, sent to the run loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DictationUpdate {
    pub(crate) take: u64,
    pub(crate) event: TakeEvent,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TakeEvent {
    /// The recording ended; the transcription runs.
    Transcribing,
    /// The trimmed transcript (empty: no speech heard).
    Transcript(String),
    /// Why the take failed.
    Failed(String),
}

/// Records and transcribes take `take`, then reports through `updates`.
/// The recording ends at the release of `trigger` (read from `signals`)
/// or when the recorder ends by itself. Dropping (aborting) the task
/// stops the recorder and removes the WAV file.
#[tracing::instrument(skip(backends, signals, updates))]
pub(crate) async fn run_take(
    backends: Dictation,
    take: u64,
    trigger: Trigger,
    mut signals: mpsc::UnboundedReceiver<Signal>,
    updates: mpsc::UnboundedSender<DictationUpdate>,
) {
    let send = |event| {
        // The run loop is gone only at exit: nothing is left to show.
        let _ = updates.send(DictationUpdate { take, event });
    };
    let wav = match tempfile::Builder::new()
        .prefix("eukhe-dictation-")
        .suffix(".wav")
        .tempfile()
    {
        Ok(file) => file,
        Err(error) => {
            send(TakeEvent::Failed(format!(
                "cannot make a temporary WAV file: {error}"
            )));
            return;
        }
    };
    let (stop_tx, stop_rx) = oneshot::channel();
    let recording = backends.recorder.record(wav.path().to_path_buf(), stop_rx);
    tokio::pin!(recording);
    let released = async {
        match trigger {
            // A push-to-talk repeat does not end a toggle take.
            Trigger::Toggle => while let Some(Signal::Held) = signals.recv().await {},
            Trigger::Hold => {
                let mut window = HOLD_FIRST_REPEAT;
                while let Ok(Some(Signal::Held)) =
                    tokio::time::timeout(window, signals.recv()).await
                {
                    window = HOLD_RELEASE;
                }
            }
        }
    };
    let recorded = tokio::select! {
        result = &mut recording => result,
        () = released => {
            // The recorder may have ended in the same instant: then
            // nothing listens, and its own result follows.
            let _ = stop_tx.send(());
            recording.await
        }
    };
    if let Err(error) = recorded {
        send(TakeEvent::Failed(error));
        return;
    }
    send(TakeEvent::Transcribing);
    match backends
        .transcriber
        .transcribe(wav.path().to_path_buf())
        .await
    {
        Ok(text) => send(TakeEvent::Transcript(text)),
        Err(error) => send(TakeEvent::Failed(error)),
    }
}

/// The bytes of a 16 kHz mono 16-bit PCM WAV file that holds `pcm`
/// (little-endian samples; an odd last byte is dropped).
#[must_use]
pub fn wav_bytes(pcm: &[u8]) -> Vec<u8> {
    let data = &pcm[..pcm.len() & !1];
    // A RIFF size is 32 bits: a take past it keeps its first 4 GiB.
    let data_len = u32::try_from(data.len())
        .unwrap_or(u32::MAX)
        .min(u32::MAX - 36)
        & !1;
    let mut bytes = Vec::with_capacity(44 + data.len());
    bytes.extend_from_slice(b"RIFF");
    bytes.extend_from_slice(&(36 + data_len).to_le_bytes());
    bytes.extend_from_slice(b"WAVEfmt ");
    bytes.extend_from_slice(&16u32.to_le_bytes());
    // PCM, one channel.
    bytes.extend_from_slice(&1u16.to_le_bytes());
    bytes.extend_from_slice(&1u16.to_le_bytes());
    bytes.extend_from_slice(&SAMPLE_RATE.to_le_bytes());
    bytes.extend_from_slice(&(SAMPLE_RATE * 2).to_le_bytes());
    // Block align, bits per sample.
    bytes.extend_from_slice(&2u16.to_le_bytes());
    bytes.extend_from_slice(&16u16.to_le_bytes());
    bytes.extend_from_slice(b"data");
    bytes.extend_from_slice(&data_len.to_le_bytes());
    bytes.extend_from_slice(&data[..data_len as usize]);
    bytes
}

/// One recorder program: it writes raw 16 kHz mono signed 16-bit
/// little-endian samples to its stdout until it is killed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecorderProgram {
    pub program: PathBuf,
    pub args: Vec<String>,
}

impl RecorderProgram {
    fn new(program: &str, args: &[&str]) -> Self {
        Self {
            program: PathBuf::from(program),
            args: args.iter().map(ToString::to_string).collect(),
        }
    }
}

/// The recorder that runs the first recorder program found on `PATH`.
/// The first program that starts is the one used: when it fails, the
/// take fails with its stderr; no other program is tried.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubprocessRecorder {
    pub programs: Vec<RecorderProgram>,
}

impl SubprocessRecorder {
    /// The recorder programs of this platform, in order.
    #[must_use]
    pub fn platform() -> Self {
        let programs = if cfg!(target_os = "macos") {
            vec![
                RecorderProgram::new(
                    "sox",
                    &[
                        "-q",
                        "-d",
                        "-t",
                        "raw",
                        "-r",
                        "16000",
                        "-c",
                        "1",
                        "-b",
                        "16",
                        "-e",
                        "signed-integer",
                        "-L",
                        "-",
                    ],
                ),
                RecorderProgram::new(
                    "ffmpeg",
                    &[
                        "-loglevel",
                        "error",
                        "-f",
                        "avfoundation",
                        "-i",
                        ":0",
                        "-ac",
                        "1",
                        "-ar",
                        "16000",
                        "-f",
                        "s16le",
                        "-",
                    ],
                ),
            ]
        } else {
            vec![
                RecorderProgram::new(
                    "pw-record",
                    &["--raw", "--rate=16000", "--channels=1", "--format=s16", "-"],
                ),
                RecorderProgram::new(
                    "parec",
                    &["--raw", "--format=s16le", "--rate=16000", "--channels=1"],
                ),
                RecorderProgram::new(
                    "arecord",
                    &["-q", "-t", "raw", "-f", "S16_LE", "-r", "16000", "-c", "1"],
                ),
            ]
        };
        Self { programs }
    }
}

impl Recorder for SubprocessRecorder {
    fn record(&self, wav: PathBuf, stop: oneshot::Receiver<()>) -> DictationFuture<()> {
        Box::pin(record_with(self.programs.clone(), wav, stop))
    }
}

/// [`SubprocessRecorder::record`]: start the first program found, read
/// its samples until `stop` or its exit, then write the WAV file.
#[tracing::instrument(skip(stop))]
async fn record_with(
    programs: Vec<RecorderProgram>,
    wav: PathBuf,
    stop: oneshot::Receiver<()>,
) -> Result<(), String> {
    let mut started = None;
    for candidate in &programs {
        match tokio::process::Command::new(&candidate.program)
            .args(&candidate.args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .kill_on_drop(true)
            .spawn()
        {
            Ok(child) => {
                started = Some((candidate, child));
                break;
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(format!(
                    "cannot start {}: {error}",
                    candidate.program.display()
                ))
            }
        }
    }
    let Some((candidate, mut child)) = started else {
        let names: Vec<String> = programs
            .iter()
            .map(|candidate| candidate.program.display().to_string())
            .collect();
        return Err(format!(
            "no audio recorder found; install one of: {}",
            names.join(", ")
        ));
    };
    let name = candidate.program.display().to_string();
    let (Some(stdout), Some(mut stderr)) = (child.stdout.take(), child.stderr.take()) else {
        return Err(format!("{name} has no output pipes"));
    };
    // The stderr pipe drains on its own task: a chatty recorder never
    // blocks on a full pipe.
    let stderr_text = tokio::spawn(async move {
        let mut text = Vec::new();
        let _ = stderr.read_to_end(&mut text).await;
        String::from_utf8_lossy(&text).trim().to_owned()
    });
    let mut stdout = BufReader::new(stdout);
    let mut pcm = Vec::new();
    tokio::pin!(stop);
    let ended_by_itself = loop {
        tokio::select! {
            read = stdout.read_buf(&mut pcm) => match read {
                Ok(0) => break true,
                Ok(_) => {}
                Err(error) => return Err(format!("cannot read {name}: {error}")),
            },
            _ = &mut stop => break false,
        }
    };
    if !ended_by_itself {
        child
            .start_kill()
            .map_err(|error| format!("cannot stop {name}: {error}"))?;
    }
    let status = child
        .wait()
        .await
        .map_err(|error| format!("cannot wait for {name}: {error}"))?;
    let stderr = stderr_text.await.unwrap_or_default();
    if ended_by_itself && !status.success() {
        return Err(if stderr.is_empty() {
            format!("{name} stopped: {status}")
        } else {
            format!("{name}: {stderr}")
        });
    }
    if pcm.len() < 2 {
        return Err(if stderr.is_empty() {
            format!("{name} recorded no audio")
        } else {
            format!("{name} recorded no audio: {stderr}")
        });
    }
    write_wav(&wav, &pcm).await
}

/// Writes `pcm` as the WAV file `wav`.
async fn write_wav(wav: &Path, pcm: &[u8]) -> Result<(), String> {
    tokio::fs::write(wav, wav_bytes(pcm))
        .await
        .map_err(|error| format!("cannot write {}: {error}", wav.display()))
}

#[cfg(test)]
mod tests;
