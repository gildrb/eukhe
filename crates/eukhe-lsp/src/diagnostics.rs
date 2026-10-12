//! The per-session diagnostics ledger (omp `DiagnosticsLedger`): late
//! diagnostics repeat only what is new since the last report of the file.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use eukhe_types::lsp::{LspDiagnostic, LspSeverity};

/// A diagnostic without its location: an edit above it moves the span but
/// leaves the diagnostic the same.
type Identity = (LspSeverity, String, Option<String>, Option<String>, String);

fn identity(diagnostic: &LspDiagnostic) -> Identity {
    (
        diagnostic.severity,
        diagnostic.message.clone(),
        diagnostic.source.clone(),
        diagnostic.code.clone(),
        diagnostic.server.clone(),
    )
}

/// What a session last reported per file.
#[derive(Debug, Default)]
pub struct DiagnosticsLedger {
    seen: HashMap<PathBuf, HashSet<Identity>>,
}

impl DiagnosticsLedger {
    /// Record `diagnostics` as the current set of `path` and return the
    /// ones the previous set lacked.
    pub fn reduce(&mut self, path: &Path, diagnostics: Vec<LspDiagnostic>) -> Vec<LspDiagnostic> {
        let current: HashSet<Identity> = diagnostics.iter().map(identity).collect();
        let fresh = match self.seen.get(path) {
            Some(previous) => diagnostics
                .into_iter()
                .filter(|diagnostic| !previous.contains(&identity(diagnostic)))
                .collect(),
            None => diagnostics,
        };
        if current.is_empty() {
            self.seen.remove(path);
        } else {
            self.seen.insert(path.to_owned(), current);
        }
        fresh
    }
}

#[cfg(test)]
mod tests {
    use eukhe_types::lsp::{LspPoint, LspSpan};

    use super::*;

    fn diagnostic(line: u32, message: &str) -> LspDiagnostic {
        let point = LspPoint { line, column: 1 };
        LspDiagnostic {
            path: PathBuf::from("/a.rs"),
            span: LspSpan {
                start: point,
                end: point,
            },
            severity: LspSeverity::Error,
            message: message.to_owned(),
            source: None,
            code: None,
            server: "fixture".to_owned(),
        }
    }

    #[test]
    fn moved_diagnostics_are_not_repeated() {
        let mut ledger = DiagnosticsLedger::default();
        let path = Path::new("/a.rs");
        assert_eq!(
            ledger.reduce(path, vec![diagnostic(1, "x")]),
            vec![diagnostic(1, "x")]
        );
        assert_eq!(
            ledger.reduce(path, vec![diagnostic(2, "x"), diagnostic(3, "y")]),
            vec![diagnostic(3, "y")]
        );
        assert_eq!(ledger.reduce(path, Vec::new()), Vec::new());
        assert_eq!(
            ledger.reduce(path, vec![diagnostic(2, "x")]),
            vec![diagnostic(2, "x")]
        );
    }
}
