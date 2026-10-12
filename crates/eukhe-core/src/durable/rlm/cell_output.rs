//! The model projection of one `ipython` cell's output, bounded once.
//!
//! Every chunk the cell streams, then its result value, traceback, and
//! background output, pass through one [`CellOutput`]. While the output fits
//! the default tool-result bound ([`DEFAULT_MAX_BYTES`],
//! [`DEFAULT_MAX_LINES`]) it is kept whole. Past the bound it is spilled to an
//! artifact file in the session directory, and memory keeps only the head
//! (half the bound) and a window over the tail. The projection is the head and
//! the tail; one `output_bounded` diagnostic names the omitted middle and the
//! artifact, so the result stays within the Harness's own bound.

use std::io::Write as _;
use std::path::PathBuf;

use eukhe_durable::harness::types::{
    OmittedAt, OmittedOutput, OutputRetain, ToolDiagnostic, ToolDiagnosticSeverity,
};
use eukhe_durable::harness::{bound_output, OutputLimits};
use eukhe_durable::{DEFAULT_MAX_BYTES, DEFAULT_MAX_LINES};

#[expect(
    clippy::cast_possible_truncation,
    reason = "the default bound is 50 KiB and 2000 lines"
)]
const HALF: (usize, usize) = (
    DEFAULT_MAX_BYTES as usize / 2,
    DEFAULT_MAX_LINES as usize / 2,
);

/// The kept head and the open artifact of an output past the bound.
struct Spilled {
    head: String,
    artifact: Result<(PathBuf, std::io::BufWriter<std::fs::File>), String>,
}

/// One cell's output: whole while within the bound, then head, tail window,
/// and artifact.
pub(crate) struct CellOutput {
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

fn limits(retain: OutputRetain) -> OutputLimits {
    OutputLimits {
        max_bytes: HALF.0,
        max_lines: HALF.1,
        retain,
    }
}

impl CellOutput {
    pub(crate) fn new(artifact_path: Result<PathBuf, String>) -> Self {
        Self {
            artifact_path,
            window: String::new(),
            spilled: None,
            bytes: 0,
            newlines: 0,
        }
    }

    /// Append one chunk of the cell's stdout or stderr.
    pub(crate) fn push(&mut self, text: &str) {
        self.bytes += text.len() as u64;
        self.newlines += newlines(text);
        self.window.push_str(text);
        match &mut self.spilled {
            None => {
                let lines = self.newlines + u64::from(!self.window.ends_with('\n'));
                if self.bytes > DEFAULT_MAX_BYTES || lines > DEFAULT_MAX_LINES {
                    self.spill();
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
                if self.window.len() > 2 * (HALF.0 + 1) {
                    let mut start = self.window.len() - (HALF.0 + 1);
                    while !self.window.is_char_boundary(start) {
                        start -= 1;
                    }
                    self.window.drain(..start);
                }
            }
        }
    }

    /// Append a part that starts on its own line (the result value, a
    /// traceback, background output).
    pub(crate) fn push_part(&mut self, text: &str) {
        if self.bytes > 0 && !self.window.ends_with('\n') {
            self.push("\n");
        }
        self.push(text);
    }

    fn spill(&mut self) {
        let head = bound_output(&self.window, &limits(OutputRetain::Head)).text;
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
    pub(crate) fn finish(self) -> (String, Option<ToolDiagnostic>) {
        let Some(Spilled { head, artifact }) = self.spilled else {
            return (self.window, None);
        };
        let tail = bound_output(&self.window, &limits(OutputRetain::Tail)).text;
        let artifact = artifact.and_then(|(path, mut file)| {
            file.flush()
                .map(|()| path.to_string_lossy().into_owned())
                .map_err(|error| format!("writing the full output failed: {error}"))
        });
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
        };
        (head + &tail, Some(diagnostic))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bounded(path: Result<PathBuf, String>, chunks: &[&str]) -> (String, Option<ToolDiagnostic>) {
        let mut output = CellOutput::new(path);
        for chunk in chunks {
            output.push(chunk);
        }
        output.finish()
    }

    #[test]
    fn output_within_the_bound_is_kept_whole_without_an_artifact() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let path = dir.path().join("out.txt");
        let text = "line\n".repeat(DEFAULT_MAX_LINES as usize);
        assert_eq!(bounded(Ok(path.clone()), &[&text]), (text, None));
        assert!(!path.exists());
    }

    /// The end of a long output, where errors are, reaches the model; the
    /// whole output is in the artifact.
    #[test]
    fn long_output_keeps_head_and_tail_and_spills_everything() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let path = dir.path().join("tool-output").join("7.txt");
        let lines: Vec<String> = (1..=5000).map(|n| format!("{n}\n")).collect();
        let chunks: Vec<&str> = lines.iter().map(String::as_str).collect();
        let (text, diagnostic) = bounded(Ok(path.clone()), &chunks);
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
                })
            )
        );
        assert_eq!(std::fs::read_to_string(&path).expect("artifact"), all);
    }

    #[test]
    fn a_session_without_storage_still_bounds_and_says_why_nothing_was_kept() {
        let big = "x".repeat(DEFAULT_MAX_BYTES as usize * 2);
        let (text, diagnostic) =
            bounded(Err("the session has no storage directory".into()), &[&big]);
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
}
