//! The model projection of one run's output, bounded once: an `ipython`
//! cell (its streamed chunks, then its result value, traceback, and
//! background output) or a user `!bash` command.
//!
//! Every chunk passes through one [`BoundedOutput`], bounded by the run's
//! [`Truncation`] (the call's, or the default bound for a user command).
//! While the output fits the bound it is kept whole. Past the bound it is
//! spilled to an artifact file in the session directory, and memory keeps
//! only the head (half the bound) and a window over the tail. The
//! projection is the head and the tail; one `output_bounded` diagnostic
//! names the omitted middle and the artifact, so the result stays within
//! the Harness's own bound: the kept bytes and the omitted bytes are every
//! byte of the output. Under the opt-out ([`Truncation::Off`]) the output
//! is kept whole.

use std::io::Write as _;
use std::path::{Path, PathBuf};

use eukhe_durable::harness::types::{
    LineSpan, OmittedAt, OmittedOutput, OutputRetain, ToolDiagnostic, ToolDiagnosticSeverity,
};
use eukhe_durable::harness::{bound_output, OutputLimits, Truncation};

/// The artifacts' directory in the session's storage directory.
const ARTIFACT_DIR: &str = "tool-output";

/// The kept head and the open artifact of an output past the bound.
struct Spilled {
    head: String,
    artifact: Result<(PathBuf, std::io::BufWriter<std::fs::File>), String>,
}

/// One run's output: whole while within the bound, then head, tail window,
/// and artifact.
pub struct BoundedOutput {
    /// The bound; `None` under the opt-out, which keeps everything.
    bound: Option<OutputLimits>,
    /// Where the full output goes once it passes the bound; `Err`: why it
    /// cannot be kept.
    artifact_path: Result<PathBuf, String>,
    /// All of the output within the bound; past it, a suffix holding the
    /// tail window.
    window: String,
    spilled: Option<Spilled>,
    bytes: u64,
    newlines: u64,
}

fn newlines(text: &str) -> u64 {
    text.bytes().filter(|&byte| byte == b'\n').count() as u64
}

/// Half of `bound`, keeping `retain`: the head or the tail of a spilled
/// output.
fn half(bound: OutputLimits, retain: OutputRetain) -> OutputLimits {
    OutputLimits {
        max_bytes: bound.max_bytes / 2,
        max_lines: bound.max_lines / 2,
        retain,
    }
}

impl BoundedOutput {
    /// An output bounded by `truncation` whose artifact, once it passes the
    /// bound, is `<storage_dir>/tool-output/<name>.txt`; a session without
    /// a storage directory keeps no artifact.
    #[must_use]
    pub fn in_session(storage_dir: Option<&Path>, name: &str, truncation: Truncation) -> Self {
        Self {
            bound: truncation.limits(),
            artifact_path: storage_dir
                .map(|dir| dir.join(ARTIFACT_DIR).join(format!("{name}.txt")))
                .ok_or_else(|| "the session has no storage directory".to_owned()),
            window: String::new(),
            spilled: None,
            bytes: 0,
            newlines: 0,
        }
    }

    /// The bytes of output so far, kept or not.
    #[must_use]
    pub fn bytes(&self) -> u64 {
        self.bytes
    }

    /// Append one chunk of the run's stdout or stderr.
    pub fn push(&mut self, text: &str) {
        self.bytes += text.len() as u64;
        self.newlines += newlines(text);
        self.window.push_str(text);
        let Some(bound) = self.bound else {
            return;
        };
        match &mut self.spilled {
            None => {
                let lines = self.newlines + u64::from(!self.window.ends_with('\n'));
                if self.bytes > bound.max_bytes as u64 || lines > bound.max_lines as u64 {
                    self.spill(bound);
                }
            }
            Some(spilled) => {
                if let Ok((_, file)) = &mut spilled.artifact {
                    if let Err(error) = file.write_all(text.as_bytes()) {
                        spilled.artifact = Err(format!("writing the full output failed: {error}"));
                    }
                }
                // Keep the tail window and the byte before it, so the window
                // can still find its first line.
                let tail = bound.max_bytes / 2;
                if self.window.len() > 2 * (tail + 1) {
                    let mut start = self.window.len() - (tail + 1);
                    while !self.window.is_char_boundary(start) {
                        start -= 1;
                    }
                    self.window.drain(..start);
                }
            }
        }
    }

    /// Append a part that starts on its own line (the result value, a
    /// traceback, background output); returns the lines it fills.
    pub fn push_part(&mut self, text: &str) -> LineSpan {
        if self.bytes > 0 && !self.window.ends_with('\n') {
            self.push("\n");
        }
        let first = self.newlines + 1;
        self.push(text);
        LineSpan {
            first,
            last: self.newlines + u64::from(!text.ends_with('\n')),
        }
    }

    fn spill(&mut self, bound: OutputLimits) {
        let head = bound_output(&self.window, &half(bound, OutputRetain::Head)).text;
        let artifact = self.artifact_path.clone().and_then(|path| {
            let opened = path
                .parent()
                .map_or(Ok(()), std::fs::create_dir_all)
                .and_then(|()| std::fs::File::create(&path))
                .map(std::io::BufWriter::new)
                .and_then(|mut file| file.write_all(self.window.as_bytes()).map(|()| file));
            opened
                .map(|file| (path.clone(), file))
                .map_err(|error| format!("saving it to {} failed: {error}", path.display()))
        });
        self.spilled = Some(Spilled { head, artifact });
    }

    /// The projection and its `output_bounded` diagnostic, when the output
    /// passed the bound.
    #[must_use]
    pub fn finish(mut self) -> (String, Option<ToolDiagnostic>) {
        self.projection()
    }

    /// The projection of the output so far (a detached run's partial
    /// output); the run keeps appending. The artifact is flushed, so the
    /// path the diagnostic names already holds everything so far.
    pub fn projection(&mut self) -> (String, Option<ToolDiagnostic>) {
        let (Some(Spilled { head, artifact }), Some(bound)) = (&mut self.spilled, self.bound)
        else {
            return (self.window.clone(), None);
        };
        let tail = bound_output(&self.window, &half(bound, OutputRetain::Tail)).text;
        let artifact = match artifact {
            Ok((path, file)) => file
                .flush()
                .map(|()| path.to_string_lossy().into_owned())
                .map_err(|error| format!("writing the full output failed: {error}")),
            Err(reason) => Err(reason.clone()),
        };
        let head = head.clone();
        let after_line = newlines(&head);
        let omitted = OmittedOutput {
            bytes: self.bytes - (head.len() + tail.len()) as u64,
            lines: self.newlines - after_line - newlines(&tail),
            at: OmittedAt::AfterLine(after_line),
        };
        let (message, artifact) = match artifact {
            Ok(path) => (
                "Output bounded to its head and tail.".to_owned(),
                Some(path),
            ),
            Err(reason) => (
                format!(
                    "Output bounded to its head and tail; the full output was not kept: {reason}."
                ),
                None,
            ),
        };
        let diagnostic = ToolDiagnostic {
            severity: ToolDiagnosticSeverity::Info,
            code: Some("output_bounded".to_owned()),
            message,
            omitted: Some(omitted),
            artifact,
            lines: None,
        };
        (head + &tail, Some(diagnostic))
    }
}

#[cfg(test)]
mod tests {
    use eukhe_types::output::{DEFAULT_MAX_BYTES, DEFAULT_MAX_LINES};

    use super::*;

    fn bounded(storage_dir: Option<&Path>, chunks: &[&str]) -> (String, Option<ToolDiagnostic>) {
        let mut output = BoundedOutput::in_session(storage_dir, "7", Truncation::default());
        for chunk in chunks {
            output.push(chunk);
        }
        output.finish()
    }

    #[test]
    fn output_within_the_bound_is_kept_whole_without_an_artifact() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let text = "line\n".repeat(DEFAULT_MAX_LINES as usize);
        assert_eq!(bounded(Some(dir.path()), &[&text]), (text, None));
        assert!(!dir.path().join(ARTIFACT_DIR).exists());
    }

    /// The end of a long output, where errors are, reaches the model; the
    /// whole output is in the artifact.
    #[test]
    fn long_output_keeps_head_and_tail_and_spills_everything() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let path = dir.path().join("tool-output").join("7.txt");
        let lines: Vec<String> = (1..=5000).map(|n| format!("{n}\n")).collect();
        let chunks: Vec<&str> = lines.iter().map(String::as_str).collect();
        let (text, diagnostic) = bounded(Some(dir.path()), &chunks);
        let all = lines.concat();
        let head = lines[..1000].concat();
        let tail = lines[4000..].concat();
        assert_eq!(
            (text, diagnostic),
            (
                format!("{head}{tail}"),
                Some(ToolDiagnostic {
                    severity: ToolDiagnosticSeverity::Info,
                    code: Some("output_bounded".to_owned()),
                    message: "Output bounded to its head and tail.".to_owned(),
                    omitted: Some(OmittedOutput {
                        bytes: (all.len() - head.len() - tail.len()) as u64,
                        lines: 3000,
                        at: OmittedAt::AfterLine(1000),
                    }),
                    artifact: Some(path.to_string_lossy().into_owned()),
                    lines: None,
                })
            )
        );
        assert_eq!(std::fs::read_to_string(&path).expect("artifact"), all);
    }

    #[test]
    fn a_session_without_storage_still_bounds_and_says_why_nothing_was_kept() {
        let big = "x".repeat(DEFAULT_MAX_BYTES as usize * 2);
        let (text, diagnostic) = bounded(None, &[&big]);
        assert_eq!(text.len(), DEFAULT_MAX_BYTES as usize);
        let diagnostic = diagnostic.expect("bounded");
        assert_eq!(
            (diagnostic.message.as_str(), diagnostic.artifact),
            (
                "Output bounded to its head and tail; the full output was not kept: the session has no storage directory.",
                None
            )
        );
    }

    /// The bound is the run's own: a call's limits bound it, and the opt-out
    /// keeps everything, kept plus omitted being every byte.
    #[test]
    fn the_runs_truncation_sets_the_bound_and_the_opt_out_keeps_everything() {
        let text = "x".repeat(100);
        let small = Truncation::On(OutputLimits {
            max_bytes: 40,
            max_lines: 10,
            retain: OutputRetain::Tail,
        });
        let mut capped = BoundedOutput::in_session(None, "7", small);
        capped.push(&text);
        let (kept, diagnostic) = capped.finish();
        let omitted = diagnostic.and_then(|diagnostic| diagnostic.omitted);
        assert_eq!(
            (
                kept.len() as u64 + omitted.map_or(0, |omitted| omitted.bytes),
                omitted.is_some()
            ),
            (100, true)
        );
        let mut whole = BoundedOutput::in_session(None, "7", Truncation::Off);
        let huge = "y".repeat(DEFAULT_MAX_BYTES as usize * 3);
        whole.push(&huge);
        assert_eq!(whole.finish(), (huge, None));
    }

    #[test]
    fn a_part_starts_on_its_own_line_and_reports_its_lines() {
        let mut output = BoundedOutput::in_session(None, "7", Truncation::default());
        output.push("cell");
        let span = output.push_part("late\nfrom a thread\n");
        assert_eq!(
            (span, output.finish()),
            (
                LineSpan { first: 2, last: 3 },
                ("cell\nlate\nfrom a thread\n".to_owned(), None)
            )
        );
    }
}
