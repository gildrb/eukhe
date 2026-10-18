//! The dictation keys (`app.stt.pushToTalk`, `app.stt.toggle`) and the
//! fold of a take's steps (docs/inference.md S9): a take records, then
//! transcribes; its text goes into the editor draft at the cursor. The
//! status line shows the phase; Esc cancels the take.

use serde_json::Value;
use tokio::sync::mpsc;

use super::cvar::CvarLineTarget;
use super::{AgentView, SessionUi, StatusKind};
use crate::dictation::{run_take, DictationUpdate, Phase, Signal, TakeEvent, Trigger};

/// The cvar that turns the dictation keys on.
const STT_ENABLED: &str = "stt.enabled";

/// The take that runs. Dropping it aborts its task: the recorder stops
/// and the temporary WAV file goes away.
pub(crate) struct DictationTake {
    id: u64,
    phase: Phase,
    signals: mpsc::UnboundedSender<Signal>,
    task: tokio::task::JoinHandle<()>,
}

impl Drop for DictationTake {
    fn drop(&mut self) {
        self.task.abort();
    }
}

impl SessionUi {
    /// Runs the dictation actions of key `id`: true when the key was a
    /// dictation key (or Esc during a take) and nothing else may run it.
    #[tracing::instrument(skip(self, view))]
    pub(crate) async fn handle_dictation_key(&mut self, id: &str, view: &mut AgentView) -> bool {
        let kb = view.editor.keybindings();
        let hold = kb.matches(id, "app.stt.pushToTalk");
        let toggle = kb.matches(id, "app.stt.toggle");
        let cancel = kb.matches(id, "app.input.clear");
        let trigger = if hold {
            Trigger::Hold
        } else if toggle {
            Trigger::Toggle
        } else {
            if cancel && self.dictation_take.is_some() {
                self.end_take(view);
                self.note("Dictation cancelled", view);
                return true;
            }
            return false;
        };
        if let Some(take) = &self.dictation_take {
            let signal = match (take.phase, trigger) {
                (Phase::Recording, Trigger::Hold) => Some(Signal::Held),
                (Phase::Recording, Trigger::Toggle) => Some(Signal::Stop),
                (Phase::Transcribing, Trigger::Hold | Trigger::Toggle) => None,
            };
            if let Some(signal) = signal {
                // The take reads its signals until its recording ends.
                let _ = take.signals.send(signal);
            }
            return true;
        }
        // A new take: only with backends and with `stt.enabled` on.
        let Some(backends) = self.dictation.clone() else {
            self.note_as("Dictation is not available here", StatusKind::Warning, view);
            return true;
        };
        let enabled = match self.send_cvar_line("", CvarLineTarget::Session).await {
            Ok(reply) => reply
                .values
                .iter()
                .any(|value| value.id == STT_ENABLED && value.value == Value::Bool(true)),
            Err(failure) => {
                self.error_row(&format!("Dictation: {failure}"), view);
                return true;
            }
        };
        if !enabled {
            self.note_as(
                "Dictation is off. Turn it on with /set stt.enabled true",
                StatusKind::Warning,
                view,
            );
            return true;
        }
        self.dictation_takes += 1;
        let id = self.dictation_takes;
        let (signals, signals_rx) = mpsc::unbounded_channel();
        let task = tokio::spawn(run_take(
            backends,
            id,
            trigger,
            signals_rx,
            self.dictation_updates.clone(),
        ));
        self.dictation_take = Some(DictationTake {
            id,
            phase: Phase::Recording,
            signals,
            task,
        });
        view.chrome.dictation = Some(Phase::Recording);
        self.dirty = true;
        true
    }

    /// Drops the take that runs (its task aborts) and clears its status.
    fn end_take(&mut self, view: &mut AgentView) {
        self.dictation_take = None;
        view.chrome.dictation = None;
        self.dirty = true;
    }

    /// Folds a step of a take: the status line follows the phase, the
    /// transcript goes into the draft, a failure shows as an error row.
    /// A step of a take that is no longer the current one is dropped.
    pub(crate) fn apply_dictation_update(&mut self, update: DictationUpdate, view: &mut AgentView) {
        let Some(take) = self
            .dictation_take
            .as_mut()
            .filter(|take| take.id == update.take)
        else {
            return;
        };
        match update.event {
            TakeEvent::Transcribing => {
                take.phase = Phase::Transcribing;
                view.chrome.dictation = Some(Phase::Transcribing);
                self.dirty = true;
            }
            TakeEvent::Transcript(text) => {
                self.end_take(view);
                if text.is_empty() {
                    self.note_as("Dictation heard no speech", StatusKind::Warning, view);
                } else {
                    view.editor.insert_text_at_cursor(&text);
                }
            }
            TakeEvent::Failed(error) => {
                self.end_take(view);
                self.error_row(&format!("Dictation failed: {error}"), view);
            }
        }
    }
}
