//! Every provider-request path of the workspace passes a budget gate
//! (spec/README.md B4; the user's rule: no exceptions). The test reads the
//! source of every workspace crate but `eukhe-ai` (where the providers and
//! the model collection themselves live) and finds each place that sends a
//! provider request or builds or fills a model collection; every hit must
//! be in [`GATED`], which names the gate that covers it. A new request
//! path, or one more of an existing kind in a file, fails here until it is
//! gated and listed. Test files and inline test modules are not read.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// What starts a provider request, or builds or fills the collection one
/// goes through.
const ENTRIES: [&str; 14] = [
    ".stream(",
    ".stream_simple(",
    ".complete(",
    ".complete_simple(",
    ".fetch_deferred(",
    ".cancel_deferred(",
    ".classify(",
    ".generate_images(",
    "create_models(",
    "create_pi_models(",
    ".set_provider(",
    "Models::new(",
    "SettingsSummarizer::new(",
    "SettingsSummarizer::in_process(",
];

/// The session's model collection: gated at open
/// (`durable::open::open_session`, `wrap_models_with_budget` with the
/// session's gate, before admission; providers registered later too).
const SESSION: &str =
    "HostDeps.models / the Harness's models: the session's collection, gated at open";
/// A wrapper that re-wraps the rows a collection holds (same ids): the
/// budget-gated row stays beneath it.
const REWRAP: &str = "re-wraps rows the collection holds: the budget row stays innermost";
/// The account of requests that belong to no task.
const DAEMON: &str = "BudgetGate::daemon (the daemon account)";

/// Every place that may reach a provider, how often it occurs in its file,
/// and the gate that covers it.
const GATED: &[(&str, &str, usize, &str)] = &[
    ("crates/eukhe-cli/src/chat_command.rs", "SettingsSummarizer::in_process(", 1, "the shared chat's compactor: SettingsSummarizer's default gate, BudgetGate::daemon"),
    ("crates/eukhe-cli/src/headless_session.rs", "SettingsSummarizer::in_process(", 1, "SettingsSummarizer::for_session(the session whose chat it compacts)"),
    ("crates/eukhe-cli/src/provider_command.rs", "create_models(", 1, DAEMON),
    ("crates/eukhe-cli/src/tiny_command.rs", "create_models(", 1, DAEMON),
    ("crates/eukhe-core/src/durable/admission_gate.rs", ".set_provider(", 1, REWRAP),
    ("crates/eukhe-core/src/durable/budget/rows.rs", ".set_provider(", 1, "the budget gate itself (wrap_models_with_budget)"),
    ("crates/eukhe-core/src/durable/compaction/autorefine.rs", ".complete_simple(", 1, SESSION),
    ("crates/eukhe-core/src/durable/compaction/summary.rs", ".stream_simple(", 1, SESSION),
    ("crates/eukhe-core/src/durable/fork.rs", "create_models(", 1, "an empty collection: the fork's Harness has no provider to send to"),
    ("crates/eukhe-core/src/durable/import.rs", "create_models(", 1, "an empty collection: the import's Harness has no provider to send to"),
    ("crates/eukhe-core/src/durable/models.rs", ".set_provider(", 2, "builds a collection its caller gates (open.rs, memory/summarizer.rs, eukhe-cli provider/tiny commands)"),
    ("crates/eukhe-core/src/durable/models.rs", "create_models(", 1, "builds a collection its caller gates (open.rs, memory/summarizer.rs, eukhe-cli provider/tiny commands)"),
    ("crates/eukhe-core/src/durable/models.rs", "create_pi_models(", 1, "builds a collection its caller gates (open.rs, memory/summarizer.rs, eukhe-cli provider/tiny commands)"),
    ("crates/eukhe-core/src/durable/models/provider.rs", ".set_provider(", 1, REWRAP),
    ("crates/eukhe-core/src/durable/open.rs", ".set_provider(", 2, "the semantic-edge re-wrap, and the session-local copy of a caller's collection, gated next by the session's gate"),
    ("crates/eukhe-core/src/durable/open.rs", "create_models(", 1, SESSION),
    ("crates/eukhe-core/src/durable/open.rs", "create_pi_models(", 1, SESSION),
    ("crates/eukhe-core/src/durable/rlm/query.rs", ".complete_simple(", 1, SESSION),
    ("crates/eukhe-core/src/durable/rlm/refine.rs", ".complete_simple(", 1, SESSION),
    ("crates/eukhe-core/src/memory/compactor.rs", ".complete(", 1, "a Summarizer: SettingsSummarizer or the scripted one, each gated"),
    ("crates/eukhe-core/src/memory/summarizer.rs", ".stream_simple(", 1, "the summarizer's own collection, gated per call with its gate"),
    ("crates/eukhe-core/src/memory/summarizer.rs", "SettingsSummarizer::new(", 1, "SettingsSummarizer::in_process: the daemon gate until for_session"),
    ("crates/eukhe-core/src/memory/summarizer.rs", "create_models(", 1, "the summarizer's own collection, gated per call with its gate"),
    ("crates/eukhe-core/src/tiny/judge.rs", ".set_provider(", 1, "adds the local classifier while a collection is built, before its caller gates it"),
    ("crates/eukhe-core/src/tiny/mod.rs", ".complete_simple(", 1, "TextBackends.models: the session's collection (worker titles) or the daemon-gated one (eukhe-cli tiny command)"),
    ("crates/eukhe-daemon/src/branch_navigation/summary.rs", ".complete_simple(", 1, SESSION),
    ("crates/eukhe-daemon/src/side_question.rs", ".stream_simple(", 1, SESSION),
    ("crates/eukhe-daemon/src/supervisor.rs", "SettingsSummarizer::new(", 1, "the shared chat's compactor: SettingsSummarizer's default gate, BudgetGate::daemon"),
    ("crates/eukhe-daemon/src/worker/create.rs", "SettingsSummarizer::in_process(", 1, "SettingsSummarizer::for_session(the session whose chat it compacts)"),
    ("crates/eukhe-daemon/src/worker/create.rs", "SettingsSummarizer::new(", 1, "SettingsSummarizer::for_session(the session whose chat it compacts)"),
    ("crates/eukhe-daemon/src/worker/durable_host/mod.rs", ".complete_simple(", 1, "the scripted compactor's own collection, gated with its session's gate"),
    ("crates/eukhe-daemon/src/worker/durable_host/mod.rs", ".set_provider(", 1, "the scripted compactor's own collection, gated with its session's gate"),
    ("crates/eukhe-daemon/src/worker/durable_host/mod.rs", "create_models(", 1, "the scripted compactor's own collection, gated with its session's gate"),
    ("crates/eukhe-durable/src/codemode/call.rs", ".complete(", 1, "no provider request: a code-mode call's completion"),
    ("crates/eukhe-durable/src/codemode/models.rs", ".classify(", 3, "the session's collection, its classify rows gated (two are the docs' text)"),
    ("crates/eukhe-durable/src/codemode/models.rs", ".generate_images(", 1, "the session's collection, its image rows gated"),
    ("crates/eukhe-durable/src/harness/compaction.rs", ".complete_simple(", 1, SESSION),
    ("crates/eukhe-durable/src/harness/generation.rs", ".cancel_deferred(", 1, "the session's collection: the cancel settles the deferred reservation"),
    ("crates/eukhe-durable/src/harness/generation.rs", ".fetch_deferred(", 1, "the session's collection: the fetch settles the deferred reservation"),
    ("crates/eukhe-durable/src/harness/generation/stream.rs", ".stream_simple(", 1, SESSION),
];

/// The `.rs` files under `dir`, recursively.
fn rust_sources(dir: &Path, found: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries {
        let path = entry.unwrap().path();
        if path.is_dir() {
            rust_sources(&path, found);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            found.push(path);
        }
    }
}

#[test]
fn every_provider_request_path_passes_a_budget_gate() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut sources = Vec::new();
    for crate_dir in std::fs::read_dir(root.join("crates")).unwrap() {
        let crate_dir = crate_dir.unwrap().path();
        if crate_dir.file_name().is_some_and(|name| name == "eukhe-ai") {
            continue;
        }
        rust_sources(&crate_dir.join("src"), &mut sources);
    }
    let mut found: BTreeMap<(String, String), usize> = BTreeMap::new();
    for source in sources {
        let relative = source
            .strip_prefix(&root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let name = relative.rsplit('/').next().unwrap_or_default();
        let test_file = relative.split('/').any(|part| part == "tests")
            || name == "tests.rs"
            || name.ends_with("_tests.rs")
            || name.starts_with("test_")
            || name.ends_with("test_support.rs");
        if test_file {
            continue;
        }
        let text = std::fs::read_to_string(&source).unwrap();
        let lines: Vec<&str> = text.lines().collect();
        for (at, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            // An inline test module ends what the crate ships.
            let test_module = trimmed == "#[cfg(test)]"
                && lines.get(at + 1).is_some_and(|next| {
                    let next = next.trim();
                    next.starts_with("mod ") && next.ends_with('{')
                });
            if test_module {
                break;
            }
            if trimmed.starts_with("//") {
                continue;
            }
            for entry in ENTRIES {
                let calls = line
                    .match_indices(entry)
                    .filter(|(index, _)| !line[index + entry.len()..].starts_with(')'))
                    .count();
                if calls > 0 {
                    *found
                        .entry((relative.clone(), entry.to_owned()))
                        .or_default() += calls;
                }
            }
        }
    }
    let gated: BTreeMap<(String, String), usize> = GATED
        .iter()
        .map(|(file, entry, count, _)| (((*file).to_owned(), (*entry).to_owned()), *count))
        .collect();
    assert_eq!(
        (found, GATED.iter().all(|(.., gate)| !gate.is_empty())),
        (gated, true),
        "a provider-request path is not in GATED: gate it, then list it with its gate"
    );
}
