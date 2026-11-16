//! The doc guard of Rust files: hashline edits that move a doc comment or
//! attribute off its item, or drop the doc of an item they write again,
//! are refused with nothing written. The fixtures are extracts of
//! eukhe-tiny files three agents of one tree edited this way (election.rs,
//! download.rs, worker.rs).

mod common;

use common::{DiskWriter, Workspace};

const ELECTION: &str = include_str!("fixtures/doc_guard/election.rs.txt");
const DOWNLOAD: &str = include_str!("fixtures/doc_guard/download.rs.txt");
const WORKER: &str = include_str!("fixtures/doc_guard/worker.rs.txt");

const LEFT: &str = "enum Left {\n    Nothing,\n    Pinged(Met),\n    Heard(io::Result<Response>),\n    NoSpawn(TinyError),\n}\n";

const HELPERS: &str = "\
fn file_url(base_url: &str, file: &ModelFile) -> String {
    let prefix = match file.repo_kind {
        RepoKind::Model => \"\",
        RepoKind::Dataset => \"datasets/\",
    };
    format!(\"{base_url}/{prefix}{}/resolve/{}/{}\", file.repo, file.revision, file.path)
}

fn staging_dirs(staging: &Path, files: &[ModelFile]) -> Vec<PathBuf> {
    vec![staging.to_path_buf()]
}
";

/// What worker.rs lines 9-52 became: `Activity` and `Shared` written
/// again; `docs` keeps their docs, else none.
fn worker_body(docs: bool) -> String {
    let doc = |text: &str| if docs { text.to_owned() } else { String::new() };
    format!(
        "{}enum Activity {{
    Idle {{ since: Instant }},
    Busy {{ requests: std::num::NonZeroU32 }},
}}

{}struct Shared {{
    tag: String,
    socket: PathBuf,
    engine: Mutex<Box<dyn Engine>>,
    events: tokio::sync::mpsc::UnboundedSender<Event>,
{}    closing: watch::Sender<Serving>,
}}

impl Shared {{
{}    async fn infer(
        self: &Arc<Shared>,
        infer: impl FnOnce(&mut dyn Engine) -> Result<Reply, WorkerFailure> + Send + 'static,
    ) -> Response {{
        Response::Ok {{ reply: infer_now(self, infer).await }}
    }}
}}
",
        doc("/// When the worker last finished a request, and how many are in flight.\n"),
        doc("/// What every connection of one worker shares.\n"),
        doc("    /// Set by a [`Request::Shutdown`]: the worker takes no new connection.\n"),
        doc("    /// Runs `infer` on the engine on the blocking pool, one at a time.\n"),
    )
}

/// A hashline body: `text`'s lines as `+` rows.
fn rows(text: &str) -> String {
    text.lines().flat_map(|line| ["+", line, "\n"]).collect()
}

/// `text` with `insert` put before its 1-based line `line`.
fn inserted(text: &str, line: usize, insert: &str) -> String {
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    let (head, tail) = lines.split_at(line - 1);
    format!("{}{insert}{}", head.concat(), tail.concat())
}

/// `text` with its 1-based lines `first..=last` replaced by `body`.
fn replaced(text: &str, first: usize, last: usize, body: &str) -> String {
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    format!(
        "{}{body}{}",
        lines[..first - 1].concat(),
        lines[last..].concat()
    )
}

/// Apply `ops` to `path` (holding `text`): the error text, or the file
/// after the edit.
fn edit(path: &str, text: &str, ops: &str) -> Result<String, String> {
    let ws = Workspace::new();
    ws.write(path, text);
    let tag = ws.snapshot(path, text, None);
    let applied = ws.apply(&format!("[{path}#{tag}]\n{ops}"), &DiskWriter::default());
    let after = ws.read(path).unwrap_or_default();
    match applied {
        Ok(_) => Ok(after),
        Err(error) => {
            assert_eq!(after, text, "a refused edit writes nothing");
            Err(error.to_string())
        }
    }
}

fn refusal(path: &str, lines: &[&str]) -> String {
    format!(
        "Edit to {path} not applied: a doc comment or attribute belongs to the item right below \
         it.\n{}\nNothing was written.",
        lines.join("\n")
    )
}

#[test]
fn an_insert_inside_a_doc_is_refused_and_above_it_lands() {
    let body = format!("{}+\n", rows(LEFT));
    assert_eq!(
        (
            edit("src/election.rs", ELECTION, &format!("PUT <10:\n{body}")),
            edit("src/election.rs", ELECTION, &format!("PUT <9:\n{body}")),
        ),
        (
            Err(refusal(
                "src/election.rs",
                &[
                    "- the doc of `fn ensure` (lines 9-19): after this edit line 9 sits above \
                   `enum Left` instead. Insert before line 9, above the doc of `fn ensure`, or \
                   below the end of `fn ensure`."
                ]
            )),
            Ok(inserted(ELECTION, 9, &format!("{LEFT}\n"))),
        )
    );
}

#[test]
fn an_insert_between_a_doc_and_its_item_is_refused_and_above_it_lands() {
    let body = format!("{}+\n", rows(HELPERS));
    assert_eq!(
        (
            edit("src/download.rs", DOWNLOAD, &format!("PUT <6:\n{body}")),
            edit("src/download.rs", DOWNLOAD, &format!("PUT <4:\n{body}")),
        ),
        (
            Err(refusal(
                "src/download.rs",
                &[
                    "- the doc of `fn fetch_all` (lines 4-5): after this edit line 4 sits above \
                   `fn file_url` instead. Insert before line 4, above the doc of `fn fetch_all`, \
                   or below the end of `fn fetch_all`."
                ]
            )),
            Ok(inserted(DOWNLOAD, 4, &format!("{HELPERS}\n"))),
        )
    );
}

#[test]
fn a_replacement_that_drops_the_docs_of_items_it_keeps_is_refused() {
    let dropped = worker_body(false);
    let kept = worker_body(true);
    assert_eq!(
        (
            edit("src/worker.rs", WORKER, &format!("PUT 9.=52:\n{}", rows(&dropped))),
            edit("src/worker.rs", WORKER, &format!("PUT 9.=52:\n{}", rows(&kept))),
        ),
        (
            Err(refusal(
                "src/worker.rs",
                &[
                    "- the doc of `struct Activity` (line 9): this edit removes it and writes \
                     `struct Activity` again without a doc. Keep the doc above `struct Activity` \
                     in the body, or start the range below line 9.",
                    "- the doc of `struct Shared` (line 15): this edit removes it and writes \
                     `struct Shared` again without a doc. Keep the doc above `struct Shared` in \
                     the body, or start the range below line 15.",
                    "- the doc of `fn infer` (line 31): this edit removes it and writes `fn infer` \
                     again without a doc. Keep the doc above `fn infer` in the body, or start the \
                     range below line 31.",
                ]
            )),
            Ok(replaced(WORKER, 9, 52, &kept)),
        )
    );
}

#[test]
fn removing_an_item_but_not_its_doc_is_refused_and_with_it_lands() {
    assert_eq!(
        (
            edit("src/worker.rs", WORKER, "CUT 10.=14\n"),
            edit("src/worker.rs", WORKER, "CUT 9.=14\n"),
        ),
        (
            Err(refusal(
                "src/worker.rs",
                &[
                    "- the doc of `struct Activity` (line 9): this edit removes `struct Activity` \
                   but keeps line 9, which now sits above `struct Shared`. Remove line 9 with \
                   `struct Activity`, or write its replacement right below the doc."
                ]
            )),
            Ok(replaced(WORKER, 9, 14, "")),
        )
    );
}

#[test]
fn edits_that_continue_a_doc_or_rename_its_item_land() {
    let attribute = edit(
        "src/election.rs",
        ELECTION,
        "PUT <19:\n+/// Cancel safe.\n+#[must_use]\n",
    );
    let renamed = edit(
        "src/election.rs",
        ELECTION,
        "PUT 20.=20:\n+pub(crate) async fn elect(\n",
    );
    assert_eq!(
        (attribute, renamed),
        (
            Ok(inserted(ELECTION, 19, "/// Cancel safe.\n#[must_use]\n")),
            Ok(replaced(ELECTION, 20, 20, "pub(crate) async fn elect(\n")),
        )
    );
}

#[test]
fn only_rust_files_are_guarded() {
    let body = format!("{}+\n", rows(LEFT));
    assert_eq!(
        edit("notes/election.txt", ELECTION, &format!("PUT <10:\n{body}")),
        Ok(inserted(ELECTION, 10, &format!("{LEFT}\n"))),
    );
}
