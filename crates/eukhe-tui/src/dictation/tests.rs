use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;

use super::*;

/// A recorder that waits for `stop`, then writes `pcm` as the take.
struct FakeRecorder {
    pcm: Vec<u8>,
}

impl Recorder for FakeRecorder {
    fn record(&self, wav: PathBuf, stop: oneshot::Receiver<()>) -> DictationFuture<()> {
        let pcm = self.pcm.clone();
        Box::pin(async move {
            let _ = stop.await;
            write_wav(&wav, &pcm).await
        })
    }
}

/// A transcriber that reads the take back: its text names the samples.
struct FakeTranscriber;

impl Transcriber for FakeTranscriber {
    fn transcribe(&self, wav: PathBuf) -> DictationFuture<String> {
        Box::pin(async move {
            let bytes = tokio::fs::read(&wav)
                .await
                .map_err(|error| error.to_string())?;
            let samples: Vec<String> = bytes[44..]
                .chunks(2)
                .map(|pair| i16::from_le_bytes([pair[0], pair[1]]).to_string())
                .collect();
            Ok(format!("samples {}", samples.join(" ")))
        })
    }
}

fn backends(recorder: impl Recorder + 'static) -> Dictation {
    Dictation {
        recorder: Arc::new(recorder),
        transcriber: Arc::new(FakeTranscriber),
    }
}

/// Every update of take 1 until the task ends.
async fn updates_of(
    task: tokio::task::JoinHandle<()>,
    mut updates: mpsc::UnboundedReceiver<DictationUpdate>,
) -> Vec<DictationUpdate> {
    task.await.expect("take task");
    let mut seen = Vec::new();
    while let Ok(update) = updates.try_recv() {
        seen.push(update);
    }
    seen
}

fn take_events(events: Vec<TakeEvent>) -> Vec<DictationUpdate> {
    events
        .into_iter()
        .map(|event| DictationUpdate { take: 1, event })
        .collect()
}

#[tokio::test]
async fn a_toggle_take_records_until_the_next_press_then_transcribes() {
    let (signals, signals_rx) = mpsc::unbounded_channel();
    let (updates, updates_rx) = mpsc::unbounded_channel();
    let task = tokio::spawn(run_take(
        backends(FakeRecorder {
            pcm: vec![1, 0, 2, 0, 0xff, 0xff],
        }),
        1,
        Trigger::Toggle,
        signals_rx,
        updates,
    ));
    // A push-to-talk repeat does not end a toggle take; the toggle does.
    signals.send(Signal::Held).expect("signal");
    signals.send(Signal::Stop).expect("signal");
    assert_eq!(
        updates_of(task, updates_rx).await,
        take_events(vec![
            TakeEvent::Transcribing,
            TakeEvent::Transcript("samples 1 2 -1".to_owned()),
        ])
    );
}

#[tokio::test]
async fn a_hold_take_ends_when_the_key_repeats_stop() {
    let (signals, signals_rx) = mpsc::unbounded_channel();
    let (updates, updates_rx) = mpsc::unbounded_channel();
    let task = tokio::spawn(run_take(
        backends(FakeRecorder { pcm: vec![7, 0] }),
        1,
        Trigger::Hold,
        signals_rx,
        updates,
    ));
    signals.send(Signal::Held).expect("signal");
    // No more repeats: the release window ends the recording. The sender
    // stays alive, so only the window can end it.
    let updates = updates_of(task, updates_rx).await;
    drop(signals);
    assert_eq!(
        updates,
        take_events(vec![
            TakeEvent::Transcribing,
            TakeEvent::Transcript("samples 7".to_owned()),
        ])
    );
}

/// A recorder that fails: the take reports the reason and never
/// transcribes.
struct BrokenRecorder;

impl Recorder for BrokenRecorder {
    fn record(&self, _wav: PathBuf, _stop: oneshot::Receiver<()>) -> DictationFuture<()> {
        Box::pin(async { Err("no capture device".to_owned()) })
    }
}

#[tokio::test]
async fn a_recorder_failure_ends_the_take_with_its_reason() {
    let (_signals, signals_rx) = mpsc::unbounded_channel();
    let (updates, updates_rx) = mpsc::unbounded_channel();
    let task = tokio::spawn(run_take(
        backends(BrokenRecorder),
        1,
        Trigger::Toggle,
        signals_rx,
        updates,
    ));
    assert_eq!(
        updates_of(task, updates_rx).await,
        take_events(vec![TakeEvent::Failed("no capture device".to_owned())])
    );
}

/// A recorder that reports its WAV path, then records until it is
/// dropped; the drop sets `dropped`.
struct EndlessRecorder {
    started: Mutex<Option<oneshot::Sender<PathBuf>>>,
    dropped: Arc<AtomicBool>,
}

struct DropFlag(Arc<AtomicBool>);

impl Drop for DropFlag {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

impl Recorder for EndlessRecorder {
    fn record(&self, wav: PathBuf, _stop: oneshot::Receiver<()>) -> DictationFuture<()> {
        let started = self.started.lock().expect("lock").take();
        let flag = DropFlag(Arc::clone(&self.dropped));
        Box::pin(async move {
            let _flag = flag;
            if let Some(started) = started {
                let _ = started.send(wav);
            }
            std::future::pending::<Result<(), String>>().await
        })
    }
}

#[tokio::test]
async fn an_aborted_take_stops_the_recorder_and_removes_the_wav() {
    let (started_tx, started_rx) = oneshot::channel();
    let dropped = Arc::new(AtomicBool::new(false));
    let (_signals, signals_rx) = mpsc::unbounded_channel();
    let (updates, mut updates_rx) = mpsc::unbounded_channel();
    let task = tokio::spawn(run_take(
        backends(EndlessRecorder {
            started: Mutex::new(Some(started_tx)),
            dropped: Arc::clone(&dropped),
        }),
        1,
        Trigger::Toggle,
        signals_rx,
        updates,
    ));
    let wav = started_rx.await.expect("recording started");
    let existed = wav.exists();
    task.abort();
    let aborted = task.await.expect_err("aborted").is_cancelled();
    assert_eq!(
        (
            existed,
            aborted,
            dropped.load(Ordering::SeqCst),
            wav.exists(),
            updates_rx.try_recv().ok()
        ),
        (true, true, true, false, None)
    );
}

#[test]
fn wav_bytes_frame_the_samples_as_16_khz_mono_pcm() {
    let mut expected = Vec::new();
    expected.extend_from_slice(b"RIFF");
    expected.extend_from_slice(&40u32.to_le_bytes());
    expected.extend_from_slice(b"WAVEfmt ");
    expected.extend_from_slice(&[16, 0, 0, 0, 1, 0, 1, 0]);
    expected.extend_from_slice(&16_000u32.to_le_bytes());
    expected.extend_from_slice(&32_000u32.to_le_bytes());
    expected.extend_from_slice(&[2, 0, 16, 0]);
    expected.extend_from_slice(b"data");
    expected.extend_from_slice(&4u32.to_le_bytes());
    expected.extend_from_slice(&[1, 0, 2, 0]);
    // The odd last byte is half a sample: it is dropped.
    assert_eq!(wav_bytes(&[1, 0, 2, 0, 9]), expected);
}

fn shell(script: &str) -> RecorderProgram {
    RecorderProgram {
        program: PathBuf::from("/bin/sh"),
        args: vec!["-c".to_owned(), script.to_owned()],
    }
}

fn missing(name: &str) -> RecorderProgram {
    RecorderProgram {
        program: PathBuf::from(format!("/nonexistent/{name}")),
        args: Vec::new(),
    }
}

/// Runs the subprocess recorder with `programs`, the stop never sent:
/// the result, and the WAV file when one was written.
async fn record_programs(programs: Vec<RecorderProgram>) -> (Result<(), String>, Option<Vec<u8>>) {
    let dir = tempfile::tempdir().expect("temp dir");
    let wav = dir.path().join("take.wav");
    let (_stop, stop_rx) = oneshot::channel();
    let result = SubprocessRecorder { programs }
        .record(wav.clone(), stop_rx)
        .await;
    (result, std::fs::read(&wav).ok())
}

#[cfg(unix)]
#[tokio::test]
async fn the_first_recorder_found_writes_its_samples_as_the_take() {
    assert_eq!(
        record_programs(vec![
            missing("eukhe-no-recorder"),
            shell(r"printf '\001\000\002\000'"),
        ])
        .await,
        (Ok(()), Some(wav_bytes(&[1, 0, 2, 0])))
    );
}

#[cfg(unix)]
#[tokio::test]
async fn a_failed_recorder_reports_its_stderr() {
    assert_eq!(
        record_programs(vec![
            shell("echo 'no capture device' >&2; exit 1"),
            shell(r"printf '\001\000'"),
        ])
        .await,
        (Err("/bin/sh: no capture device".to_owned()), None)
    );
}

#[cfg(unix)]
#[tokio::test]
async fn a_recorder_without_audio_is_an_error() {
    assert_eq!(
        record_programs(vec![shell("exit 0")]).await,
        (Err("/bin/sh recorded no audio".to_owned()), None)
    );
}

#[tokio::test]
async fn no_recorder_on_the_path_names_the_programs_to_install() {
    assert_eq!(
        record_programs(vec![missing("a-rec"), missing("b-rec")]).await,
        (
            Err(
                "no audio recorder found; install one of: /nonexistent/a-rec, /nonexistent/b-rec"
                    .to_owned()
            ),
            None
        )
    );
}
