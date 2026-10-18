//! The owner and its clients over the real lock socket: a turn's view is
//! never a placeholder, and the root-turn lease goes around in order and
//! survives cancelled waits, clients that hang up, and owner changes. Then
//! the owner's own duties: free and model-built lines, the compactor's
//! input and retries, zoom and date, reloads and takeovers.

use std::fmt::Write as _;
use std::future::Future;
use std::sync::Arc;
use std::time::Duration;

use eukhe_types::daemon::{MemoryLine, MemoryUpdate};
use eukhe_types::pi_ai::{Context, ImageContent, Message, UserContent, UserContentBlock};
use eukhe_types::platform::transport::connect_transport;
use tokio::sync::{mpsc, oneshot};

use super::actor::commit;
use super::client::Client;
use super::turn::TURN_FILE;
use super::{
    ImportItem, KeyedAppend, Memory, MemoryStatus, Outcome, RenderedView, Reply, Request, Zoomed,
};
use crate::memory::compactor::tests::{reply, thinking_only, Scripted, Silent};
use crate::memory::prompts::{compress_task, merge_task};
use crate::memory::saved::{CompactionPrompt, VIEW_FILE};
use crate::memory::{
    cut, AppendKey, Kind, ResponseStarted, Summarizer, SummarizerFuture, FAILURES, NODE,
    PLACEHOLDER, RETRY, SETTLE_TIMEOUT,
};

/// A compactor call the test answers with the line.
type Call = oneshot::Sender<String>;

/// A compactor whose every call waits for the test's answer.
struct Gated {
    calls: mpsc::UnboundedSender<Call>,
}

impl Summarizer for Gated {
    /// A whole-reply model: its response starts with the test's answer.
    fn complete(&self, _context: Context, mut started: ResponseStarted) -> SummarizerFuture {
        let (answer, line) = oneshot::channel();
        let asked = self.calls.send(answer);
        Box::pin(async move {
            asked.map_err(|_| anyhow::anyhow!("the test stopped answering"))?;
            let text = line.await?;
            started.signal();
            Ok(reply(&text))
        })
    }
}

/// A compactor call the test starts (its response's first event) and
/// answers with the line.
type StagedCall = (ResponseStarted, Call);

/// A compactor whose every call hands the test its start and its answer.
struct Staged {
    calls: mpsc::UnboundedSender<StagedCall>,
}

impl Summarizer for Staged {
    fn complete(&self, _context: Context, started: ResponseStarted) -> SummarizerFuture {
        let (answer, line) = oneshot::channel();
        let asked = self.calls.send((started, answer));
        Box::pin(async move {
            asked.map_err(|_| anyhow::anyhow!("the test stopped answering"))?;
            let text = line.await?;
            Ok(reply(&text))
        })
    }
}

/// Two compactions on one new cache prefix: the second waits for the
/// first, and goes once the first's response starts, before its line is
/// done (§3.3).
#[tokio::test]
async fn a_waiting_compaction_goes_once_the_writers_response_starts() {
    let dir = tempfile::tempdir().unwrap();
    let (calls, mut asked) = mpsc::unbounded_channel();
    let memory = Memory::open(dir.path(), Arc::new(Staged { calls }))
        .await
        .unwrap();
    let item = |text: String| ImportItem {
        kind: Kind::Echo,
        text,
        date: "2026-10-12".to_string(),
    };
    memory
        .import(vec![item("x".repeat(NODE)), item("y".repeat(NODE))])
        .await
        .unwrap();
    let (mut started, first) = within(asked.recv()).await.unwrap();
    let alone = asked.try_recv().is_err();
    started.signal();
    let (_, second) = within(asked.recv()).await.unwrap();
    let first_open = !first.is_closed();
    first.send("line x".to_string()).unwrap();
    second.send("line y".to_string()).unwrap();
    assert_eq!((alone, first_open), (true, true));
}

/// One chat seen by three handles in this process: the owner, then two
/// clients on its socket (as other processes would be).
struct Chat {
    owner: Memory,
    first: Memory,
    second: Memory,
    calls: mpsc::UnboundedReceiver<Call>,
    dir: tempfile::TempDir,
}

async fn open() -> Chat {
    let dir = tempfile::tempdir().unwrap();
    let (calls_sender, calls) = mpsc::unbounded_channel();
    let summarizer: Arc<dyn Summarizer> = Arc::new(Gated {
        calls: calls_sender,
    });
    let owner = Memory::open(dir.path(), Arc::clone(&summarizer))
        .await
        .unwrap();
    let first = Memory::open(dir.path(), Arc::clone(&summarizer))
        .await
        .unwrap();
    let second = Memory::open(dir.path(), summarizer).await.unwrap();
    assert_eq!(
        [owner.owns().await, first.owns().await, second.owns().await],
        [true, false, false]
    );
    Chat {
        owner,
        first,
        second,
        calls,
        dir,
    }
}

/// Fail instead of hanging when a step never comes.
async fn within<F: Future>(future: F) -> F::Output {
    tokio::time::timeout(Duration::from_secs(30), future)
        .await
        .expect("the step comes")
}

/// A message too long to be its own line: the compactor must summarize it.
fn long(id: u64) -> String {
    format!("message {id}: {}", "x".repeat(NODE))
}

/// Where turns log their names, in the order they hold the lease.
type Log = mpsc::UnboundedSender<String>;

/// The names logged so far.
fn logged(log: &mut mpsc::UnboundedReceiver<String>) -> Vec<String> {
    std::iter::from_fn(|| log.try_recv().ok()).collect()
}

/// A root turn that has reached the owner's queue, left to run on its own
/// task: it logs its name once it holds the lease, then releases it.
async fn queued_turn(
    memory: &Memory,
    name: &str,
    log: &Log,
) -> tokio::task::JoinHandle<anyhow::Result<()>> {
    let mut turn = Box::pin({
        let memory = memory.clone();
        let name = name.to_string();
        let log = log.clone();
        async move {
            let lease = memory.acquire_turn().await?;
            log.send(name)
                .map_err(|_| anyhow::anyhow!("the test stopped listening"))?;
            lease.release().await
        }
    });
    assert!(
        futures::poll!(turn.as_mut()).is_pending(),
        "the lease is held"
    );
    // One handle's requests reach the owner in order: once this answers,
    // the turn is in the queue.
    memory.status().await.unwrap();
    tokio::spawn(turn)
}

/// One runtime thread, so every step below happens in a fixed order: the
/// compactor's answer runs the node's build to its end (the line reaches
/// the owner) before the appending client's frame leaves, so each append
/// reaches the owner right after the line that settles the view: exactly
/// where a render separate from the settling step shows the appended
/// message unsummarized.
#[tokio::test(flavor = "current_thread")]
async fn a_settled_view_never_shows_a_placeholder_while_another_client_appends() {
    let mut chat = open().await;
    chat.second.append(Kind::User, &long(0)).await.unwrap();
    let mut lines = String::new();
    for id in 0..4 {
        let call = within(chat.calls.recv())
            .await
            .expect("the compactor summarizes the newest message");
        let mut view = Box::pin({
            let reader = chat.first.clone();
            async move { reader.settled_render(SETTLE_TIMEOUT).await }
        });
        assert!(
            futures::poll!(view.as_mut()).is_pending(),
            "message {id} is not summarized yet"
        );
        // Once this answers, the wait is registered at the owner.
        chat.first.status().await.unwrap();
        call.send(format!("line {id}")).unwrap();
        chat.second.append(Kind::User, &long(id + 1)).await.unwrap();
        writeln!(lines, "{id}+1|line {id}").unwrap();
        assert_eq!(
            within(view).await.unwrap(),
            RenderedView {
                messages: id + 1,
                text: format!("<chat>\n{lines}</chat>"),
            }
        );
    }
}

#[tokio::test]
async fn root_turns_go_in_arrival_order_across_processes() {
    let chat = open().await;
    let (log, mut names) = mpsc::unbounded_channel();
    let held = chat.owner.acquire_turn().await.unwrap();
    let first = queued_turn(&chat.first, "first", &log).await;
    let second = queued_turn(&chat.second, "second", &log).await;
    let owner = queued_turn(&chat.owner, "owner", &log).await;
    held.release().await.unwrap();
    for turn in [first, second, owner] {
        within(turn).await.unwrap().unwrap();
    }
    assert_eq!(logged(&mut names), ["first", "second", "owner"]);
}

#[tokio::test]
async fn a_client_that_hangs_up_frees_its_lease() {
    let chat = open().await;
    let (log, mut names) = mpsc::unbounded_channel();
    // A client process that holds the lease and dies: only its connection
    // closes.
    let crashed = Client::connect(
        connect_transport(&chat.dir.path().join("lock"))
            .await
            .unwrap(),
    );
    let granted = within(crashed.request(&Request::AcquireTurn { lease: 1 })).await;
    assert!(
        matches!(granted, Ok(Outcome::Ok(Reply::Granted))),
        "{granted:?}"
    );
    let next = queued_turn(&chat.first, "next", &log).await;
    drop(crashed);
    within(next).await.unwrap().unwrap();
    assert_eq!(logged(&mut names), ["next"]);
}

#[tokio::test]
async fn a_cancelled_wait_leaves_no_lease_behind() {
    let chat = open().await;
    let (log, mut names) = mpsc::unbounded_channel();
    let held = chat.owner.acquire_turn().await.unwrap();
    // Queued in this order: a client's wait and the owner's own, each
    // dropped only once the lease has reached it, a client's wait dropped
    // before, and the turn that must still come.
    let mut client_wait = Box::pin(chat.first.acquire_turn());
    assert!(futures::poll!(client_wait.as_mut()).is_pending());
    chat.first.status().await.unwrap();
    let mut early_wait = Box::pin(chat.second.acquire_turn());
    assert!(futures::poll!(early_wait.as_mut()).is_pending());
    chat.second.status().await.unwrap();
    let mut owner_wait = Box::pin(chat.owner.acquire_turn());
    assert!(futures::poll!(owner_wait.as_mut()).is_pending());
    let last = queued_turn(&chat.second, "last", &log).await;
    drop(early_wait);
    // Once this answers, the early wait has left the queue.
    chat.second.status().await.unwrap();
    // The lease reaches the client's wait, which nobody polls any more.
    held.release().await.unwrap();
    drop(client_wait);
    // Once this answers, the client's lease has ended and the lease has
    // reached the owner's own wait, which nobody polls either.
    chat.first.status().await.unwrap();
    drop(owner_wait);
    within(last).await.unwrap().unwrap();
    assert_eq!(logged(&mut names), ["last"]);
}

#[tokio::test]
async fn a_new_owner_never_starts_a_turn_over_a_surviving_one() {
    let chat = open().await;
    let held = chat.first.acquire_turn().await.unwrap();
    // The owner goes away, and the lease it knew with it.
    drop(chat.owner);
    // The other client takes the chat over: its owner never knew `held`.
    chat.second.status().await.unwrap();
    assert!(chat.second.owns().await);
    let mut next = Box::pin(chat.second.acquire_turn());
    assert!(futures::poll!(next.as_mut()).is_pending());
    // Once this answers, the new owner has granted `next` its lease.
    chat.second.status().await.unwrap();
    assert!(
        futures::poll!(next.as_mut()).is_pending(),
        "the surviving turn still runs"
    );
    let probe = std::fs::File::options()
        .write(true)
        .open(chat.dir.path().join(TURN_FILE))
        .unwrap();
    assert!(matches!(
        probe.try_lock(),
        Err(std::fs::TryLockError::WouldBlock)
    ));
    held.release().await.unwrap();
    within(next).await.unwrap().release().await.unwrap();
}

/// Runtime files and the view cache stay out of the chat's history (an
/// ignore file from before one existed gets its line, and a view a chat
/// committed before is untracked).
#[test]
fn a_commit_keeps_runtime_files_and_the_view_cache_out() {
    let dir = tempfile::tempdir().unwrap();
    let git = |args: &[&str]| {
        let output = std::process::Command::new("git")
            .arg("-C")
            .arg(dir.path())
            .args(args)
            .output()
            .unwrap();
        assert!(output.status.success(), "git {args:?}: {output:?}");
        String::from_utf8(output.stdout).unwrap()
    };
    // A throwaway repository, with its own identity.
    git(&["init", "-q"]);
    git(&["config", "user.name", "eukhe test"]);
    git(&["config", "user.email", "test@eukhe.invalid"]);
    std::fs::write(dir.path().join(".gitignore"), "lock\nlock.lock/\n").unwrap();
    std::fs::create_dir(dir.path().join("main")).unwrap();
    std::fs::write(dir.path().join("main/2026-10-05.jsonl"), "{}\n").unwrap();
    std::fs::write(dir.path().join(TURN_FILE), "").unwrap();
    std::fs::write(dir.path().join(VIEW_FILE), "[[0,0]]").unwrap();
    git(&["add", VIEW_FILE]);
    git(&["commit", "-q", "-m", "an old chat"]);
    std::fs::write(dir.path().join(".view.json.tmp"), "[").unwrap();
    std::fs::write(dir.path().join("prompt.json"), "{}").unwrap();
    commit(dir.path(), &dir.path().join(".git")).unwrap();
    assert_eq!(
        (
            std::fs::read_to_string(dir.path().join(".gitignore")).unwrap(),
            git(&["ls-files"]),
        ),
        (
            "lock\nlock.lock/\nturn\n.*.tmp\nprompt.json\nview.json\n".to_string(),
            ".gitignore\nmain/2026-10-05.jsonl\n".to_string(),
        )
    );
}

fn no_model() -> Arc<Scripted> {
    Scripted::with(Vec::new())
}

/// A compactor request: its system prompt, its tools' names, and its text
/// blocks with whether each carries a cache mark.
type RequestShape = (Option<String>, Vec<String>, Vec<(String, bool)>);

fn request_shape(context: &Context) -> RequestShape {
    let texts = context
        .messages
        .iter()
        .flat_map(|message| match message {
            Message::User(user) => match &user.content {
                UserContent::Text(text) => vec![(text.clone(), false)],
                UserContent::Blocks(blocks) => blocks
                    .iter()
                    .map(|block| match block {
                        UserContentBlock::Text(text) => {
                            (text.text.clone(), text.cache_breakpoint.is_some())
                        }
                        UserContentBlock::Image(_) => {
                            panic!("a compactor request holds text only")
                        }
                    })
                    .collect(),
            },
            Message::System(_) | Message::Assistant(_) | Message::ToolResult(_) => {
                panic!("a first compactor request is one user message")
            }
        })
        .collect();
    let tools = context
        .tools
        .iter()
        .flatten()
        .map(|tool| tool.name.clone())
        .collect();
    (context.system_prompt.clone(), tools, texts)
}

/// Short messages are their own lines (no model call), and so is the
/// merge of two short lines; `zoom` opens lines and messages.
#[tokio::test]
async fn short_messages_are_their_own_lines() {
    let dir = tempfile::tempdir().unwrap();
    let summarizer = no_model();
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    assert!(memory.owns().await);
    assert_eq!(memory.append(Kind::User, "hello").await.unwrap(), 0);
    assert_eq!(memory.append(Kind::Eukhe, "hi\nthere").await.unwrap(), 1);
    assert_eq!(
        memory.settled_render(SETTLE_TIMEOUT).await.unwrap(),
        RenderedView {
            messages: 2,
            text: "<chat>\n0+1|user: hello\n1+1|eukhe: hi there\n</chat>".to_string(),
        }
    );
    assert_eq!(
        [
            memory.zoom(1, 1).await.unwrap().text,
            memory.zoom(0, 2).await.unwrap().text,
            memory.zoom(0, 4).await.unwrap().text,
        ],
        [
            "1+0|eukhe: hi\nthere",
            "0+1|user: hello\n1+1|eukhe: hi there",
            "No line 0+4.",
        ]
    );
    assert_eq!(
        memory.status().await.unwrap(),
        MemoryStatus {
            messages: 2,
            nodes: 3,
            view_lines: 2,
            view_bytes: ("user: hello".len() + "eukhe: hi\nthere".len()) as u64,
            unsummarized: 0,
            running: 0,
            last_error: None,
        }
    );
    assert_eq!(summarizer.requests(), Vec::new());
}

/// Every compactor call sends the turns' system prompt and tools, then
/// its own view up to its node (only built lines, `id+n|text`), then the
/// task, marked as the request's end; messages compress in parallel. The
/// view then shows the model's lines, the message stays one zoom away.
#[tokio::test]
async fn compactions_reuse_the_turns_prompt_and_see_built_lines_only() {
    let dir = tempfile::tempdir().unwrap();
    let first = format!("echo: first, {}", "a".repeat(287));
    let second = format!("echo: second, {}", "b".repeat(286));
    let summarizer = Scripted::with(vec![
        Ok(reply(&first)),
        Ok(reply(&second)),
        Ok(reply("echo: both listings")),
    ]);
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    let prompt = CompactionPrompt {
        system: "You are Eukhe. The user's instructions follow.".to_string(),
        tools: vec![serde_json::from_value(serde_json::json!({
            "name": "zoom",
            "description": "Open a line.",
            "parameters": {"type": "object", "properties": {}}
        }))
        .unwrap()],
    };
    memory.set_compaction_prompt(prompt.clone()).await.unwrap();
    let long = |c: &str| c.repeat(NODE);
    let item = |text: String| ImportItem {
        kind: Kind::Echo,
        text,
        date: "2026-10-12".to_string(),
    };
    // One step logs both, so neither node waits for the other.
    memory
        .import(vec![item(long("x")), item(long("y\n"))])
        .await
        .unwrap();
    let mut requests: Vec<RequestShape> = summarizer
        .requested(3)
        .await
        .iter()
        .map(request_shape)
        .collect();
    requests[..2].sort();
    let shape =
        |texts: Vec<(String, bool)>| (Some(prompt.system.clone()), vec!["zoom".to_string()], texts);
    let rendered = memory.settled_render(SETTLE_TIMEOUT).await.unwrap().text;
    // Both messages compressed at once: the second did not wait for the
    // first, and saw no line of it.
    let (line_0, line_1) = (
        memory.zoom(0, 2).await.unwrap().text,
        rendered.lines().nth(2).unwrap().to_string(),
    );
    let built: Vec<&str> = line_0
        .lines()
        .map(|line| line.split_once('|').unwrap().1)
        .collect();
    assert_eq!(
        (requests, line_1),
        (
            vec![
                shape(vec![
                    ("<chat>\n</chat>".to_string(), false),
                    (compress_task(0, &format!("echo: {}", long("x"))), true),
                ]),
                shape(vec![
                    ("<chat>\n</chat>".to_string(), false),
                    (compress_task(1, &format!("echo: {}", long("y\n"))), true),
                ]),
                shape(vec![
                    (
                        format!("<chat>\n0+1|{}\n1+1|{}\n</chat>", built[0], built[1]),
                        false
                    ),
                    (merge_task("0+1", "1+1", (0, 1), (built[0], built[1])), true),
                ]),
            ],
            format!("1+1|{}", built[1])
        )
    );
    assert_eq!(
        memory.zoom(1, 1).await.unwrap().text,
        format!("1+0|echo: {}", long("y\n"))
    );
}

/// `date(id)`: the stored date as local date and time.
#[tokio::test]
async fn dates_read_as_local_date_and_time() {
    let dir = tempfile::tempdir().unwrap();
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    let item = |date: &str| ImportItem {
        kind: Kind::User,
        text: "m".to_string(),
        date: date.to_string(),
    };
    memory
        .import(vec![
            item("2026-10-05T09:32:11.123+02:00"),
            item("2026-10-05T07:32:11Z"),
            item("2026-08-03"),
        ])
        .await
        .unwrap();
    let mut dates = Vec::new();
    for id in 0..4 {
        dates.push(memory.date(id).await.unwrap());
    }
    assert_eq!(
        dates,
        [
            "2026-10-05 09:32:11 +02:00",
            "2026-10-05 07:32:11 +00:00",
            "2026-08-03",
            "No message 3.",
        ]
    );
}

/// The view is the fold of the logs and `view.json` only its cache: an
/// old chat's saved view is imported once as logged merges, and deleting
/// `view.json` afterwards reproduces the identical view.
#[tokio::test]
async fn deleting_the_saved_view_reproduces_the_identical_view() {
    let dir = tempfile::tempdir().unwrap();
    {
        let memory = Memory::open(dir.path(), no_model()).await.unwrap();
        for i in 0..5 {
            memory.append(Kind::User, &format!("m{i}")).await.unwrap();
        }
        memory.settled_render(SETTLE_TIMEOUT).await.unwrap();
    }
    // A chat from before the merges were logged: its view merged the
    // first four messages (every node is built: short lines are free).
    std::fs::write(dir.path().join(VIEW_FILE), "[[2,0],[0,4]]").unwrap();
    let imported = {
        let memory = Memory::open(dir.path(), no_model()).await.unwrap();
        assert_eq!(memory.append(Kind::User, "m5").await.unwrap(), 5);
        memory.render().await.unwrap().text
    };
    let cached = std::fs::read_to_string(dir.path().join(VIEW_FILE)).unwrap();
    std::fs::remove_file(dir.path().join(VIEW_FILE)).unwrap();
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    assert_eq!(
        (
            imported.clone(),
            memory.render().await.unwrap().text,
            std::fs::read_to_string(dir.path().join(VIEW_FILE)).unwrap(),
        ),
        (
            "<chat>\n0+4|user: m0 user: m1 user: m2 user: m3\n4+1|user: m4\n5+1|user: m5\n</chat>"
                .to_string(),
            imported,
            cached,
        )
    );
}

/// A subscriber sees each step's built nodes, from the owner and across
/// the socket alike.
#[tokio::test]
async fn subscribers_see_the_lines_each_step_builds() {
    let dir = tempfile::tempdir().unwrap();
    let owner = Memory::open(dir.path(), no_model()).await.unwrap();
    let client = Memory::open(dir.path(), no_model()).await.unwrap();
    let mut local = owner.subscribe().await.unwrap();
    let mut remote = client.subscribe().await.unwrap();
    owner.append(Kind::User, "hello").await.unwrap();
    client.append(Kind::Eukhe, "hi").await.unwrap();
    let line = |id, count, text: &str| MemoryLine {
        id,
        count,
        text: text.to_string(),
    };
    let expected = vec![
        MemoryUpdate::Summarized {
            lines: vec![line(0, 1, "user: hello")],
            view_bytes: 11,
        },
        MemoryUpdate::Summarized {
            lines: vec![
                line(1, 1, "eukhe: hi"),
                line(0, 2, "user: hello\neukhe: hi"),
            ],
            view_bytes: 20,
        },
    ];
    let mut seen = Vec::new();
    for _ in 0..2 {
        seen.push(within(local.next()).await.unwrap());
    }
    for _ in 0..2 {
        seen.push(within(remote.next()).await.unwrap());
    }
    assert_eq!(seen, [expected.clone(), expected].concat());
}

/// A second handle is the owner's client; when the owner goes, it takes
/// the chat over and the ids go on.
#[tokio::test]
async fn a_second_handle_is_a_client_and_takes_over() {
    let dir = tempfile::tempdir().unwrap();
    let owner = Memory::open(dir.path(), no_model()).await.unwrap();
    let client = Memory::open(dir.path(), no_model()).await.unwrap();
    assert_eq!((owner.owns().await, client.owns().await), (true, false));
    assert_eq!(
        client.append(Kind::User, "from the client").await.unwrap(),
        0
    );
    assert_eq!(
        owner.settled_render(SETTLE_TIMEOUT).await.unwrap().text,
        "<chat>\n0+1|user: from the client\n</chat>"
    );
    drop(owner);
    assert_eq!(
        client.append(Kind::User, "after the owner").await.unwrap(),
        1
    );
    assert!(client.owns().await);
    assert_eq!(
        client.settled_render(SETTLE_TIMEOUT).await.unwrap().text,
        "<chat>\n0+1|user: from the client\n1+1|user: after the owner\n</chat>"
    );
}

/// A socket that refuses connections is stale (its owner died): the next
/// process takes it over. The fixture binds without listening, so a connect
/// is refused even while a concurrent test's `fork` holds a descriptor
/// copy (a bound-then-dropped listener would keep accepting through such a
/// copy until the child's `exec`).
#[cfg(unix)]
#[tokio::test]
async fn a_stale_socket_is_taken_over() {
    let dir = tempfile::tempdir().unwrap();
    let lock = dir.path().join("lock");
    let dead = socket2::Socket::new(socket2::Domain::UNIX, socket2::Type::STREAM, None).unwrap();
    dead.bind(&socket2::SockAddr::unix(&lock).unwrap()).unwrap();
    drop(dead);
    assert!(lock.exists());
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    assert!(memory.owns().await);
}

#[tokio::test]
async fn a_resent_append_is_written_once() {
    let dir = tempfile::tempdir().unwrap();
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    let append = |dedupe| Request::Append {
        kind: Kind::User,
        text: "once".to_string(),
        date: "2026-10-05T09:00:00.000+02:00".to_string(),
        dedupe,
        key: None,
        images: Vec::new(),
    };
    let mut replies = Vec::new();
    for dedupe in [false, true, false] {
        replies.push(memory.request(append(dedupe)).await.unwrap());
    }
    assert_eq!(
        replies,
        [
            Reply::Appended { id: 0 },
            Reply::Appended { id: 0 },
            Reply::Appended { id: 1 },
        ]
    );
}

/// A keyed append is written once per key, across an owner restart too:
/// the key rides on the logged line, and a key at or below its scope's
/// newest is answered without a write. Other scopes count on their own.
#[tokio::test]
async fn a_keyed_append_is_written_once_across_owner_restarts() {
    let dir = tempfile::tempdir().unwrap();
    let key = |scope: &str, seq| AppendKey {
        scope: scope.to_string(),
        seq,
    };
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    let mut outcomes = vec![
        memory
            .append_keyed(Kind::User, "a", Vec::new(), key("s", 0))
            .await
            .unwrap(),
        memory
            .append_keyed(Kind::Eukhe, "b", Vec::new(), key("s", 1))
            .await
            .unwrap(),
        memory
            .append(Kind::User, "unkeyed")
            .await
            .map(KeyedAppend::Written)
            .unwrap(),
        memory
            .append_keyed(Kind::User, "a", Vec::new(), key("s", 0))
            .await
            .unwrap(),
    ];
    drop(memory);
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    outcomes.extend([
        memory
            .append_keyed(Kind::User, "a", Vec::new(), key("s", 0))
            .await
            .unwrap(),
        memory
            .append_keyed(Kind::Eukhe, "b", Vec::new(), key("s", 1))
            .await
            .unwrap(),
        memory
            .append_keyed(Kind::Echo, "c", Vec::new(), key("s", 2))
            .await
            .unwrap(),
        memory
            .append_keyed(Kind::User, "a", Vec::new(), key("t", 0))
            .await
            .unwrap(),
    ]);
    assert_eq!(
        (outcomes, memory.status().await.unwrap().messages),
        (
            vec![
                KeyedAppend::Written(0),
                KeyedAppend::Written(1),
                KeyedAppend::Written(2),
                KeyedAppend::AlreadyLogged(1),
                KeyedAppend::AlreadyLogged(1),
                KeyedAppend::AlreadyLogged(1),
                KeyedAppend::Written(3),
                KeyedAppend::Written(4),
            ],
            5
        )
    );
}

/// `zoom(id, 1)` gives message id whole, with its images (§5), across an
/// owner restart too; a message without images (every message of an old
/// log) gives none, and lines never carry images.
#[tokio::test]
async fn a_message_zoomed_whole_comes_with_its_images() {
    let dir = tempfile::tempdir().unwrap();
    let image = |data: &str| ImageContent {
        data: data.to_string(),
        mime_type: "image/png".to_string(),
    };
    let key = |seq| AppendKey {
        scope: "s".to_string(),
        seq,
    };
    {
        let memory = Memory::open(dir.path(), no_model()).await.unwrap();
        memory.append(Kind::User, "before images").await.unwrap();
        memory
            .append_keyed(
                Kind::User,
                "look\n[image: image/png]\n[image: image/png]",
                vec![image("AAAA"), image("BBBB")],
                key(0),
            )
            .await
            .unwrap();
    }
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    assert_eq!(
        [
            memory.zoom(0, 1).await.unwrap(),
            memory.zoom(1, 1).await.unwrap(),
            memory.zoom(0, 2).await.unwrap(),
        ],
        [
            Zoomed {
                text: "0+0|user: before images".to_string(),
                images: Vec::new(),
            },
            Zoomed {
                text: "1+0|user: look\n[image: image/png]\n[image: image/png]".to_string(),
                images: vec![image("AAAA"), image("BBBB")],
            },
            Zoomed {
                text:
                    "0+1|user: before images\n1+1|user: look [image: image/png] [image: image/png]"
                        .to_string(),
                images: Vec::new(),
            },
        ]
    );
}

/// Images saved for a message whose line never got written (a crash in
/// between) never reach the message that takes its id.
#[tokio::test]
async fn images_of_an_unlogged_message_never_reach_the_next_one() {
    let dir = tempfile::tempdir().unwrap();
    crate::memory::saved::save_images(
        dir.path(),
        0,
        &[ImageContent {
            data: "AAAA".to_string(),
            mime_type: "image/png".to_string(),
        }],
    )
    .unwrap();
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    memory.append(Kind::User, "no image").await.unwrap();
    assert_eq!(
        memory.zoom(0, 1).await.unwrap(),
        Zoomed {
            text: "0+0|user: no image".to_string(),
            images: Vec::new(),
        }
    );
}

/// A failed node is reported, then left alone while the chat is idle: no
/// call goes out however long nothing happens. A turn's wait tries it
/// again at once, then every [`RETRY`] while the turn waits, with no
/// backoff, until it is built.
#[tokio::test(start_paused = true)]
async fn a_failed_node_is_tried_again_only_for_a_waiting_turn() {
    let dir = tempfile::tempdir().unwrap();
    let summarizer = Scripted::with(vec![
        Err(anyhow::anyhow!("overloaded")),
        Err(anyhow::anyhow!("overloaded")),
        Ok(reply("echo: recovered")),
    ]);
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    memory.append(Kind::Echo, &"y".repeat(NODE)).await.unwrap();
    summarizer.requested(1).await;
    // Once the owner answers, it has handled the failure: a retry it
    // scheduled counts from now.
    let failed = memory.status().await.unwrap();
    tokio::time::sleep(RETRY * 3).await;
    // Once the owner answers again, a retry due in the idle time has
    // started its call; the yield runs it.
    memory.status().await.unwrap();
    tokio::task::yield_now().await;
    assert_eq!(
        (summarizer.requests().len(), failed),
        (
            1,
            MemoryStatus {
                messages: 1,
                nodes: 0,
                view_lines: 1,
                view_bytes: PLACEHOLDER.len() as u64,
                unsummarized: 1,
                running: 1,
                last_error: Some("overloaded".to_string()),
            }
        )
    );
    assert_eq!(
        memory.settled_render(SETTLE_TIMEOUT).await.unwrap().text,
        "<chat>\n0+1|echo: recovered\n</chat>"
    );
    let times = summarizer.times();
    assert_eq!(
        times
            .windows(2)
            .map(|pair| pair[1] - pair[0])
            .collect::<Vec<_>>(),
        [RETRY * 3, RETRY]
    );
    assert_eq!(memory.status().await.unwrap().last_error, None);
}

/// The owner's compactor calls end with it: a call still waiting for the
/// model is dropped when the last handle goes.
#[tokio::test]
async fn a_stopped_owner_drops_its_running_compactor_calls() {
    let dir = tempfile::tempdir().unwrap();
    let (calls, mut asked) = mpsc::unbounded_channel();
    let owner = Memory::open(dir.path(), Arc::new(Gated { calls }))
        .await
        .unwrap();
    owner.append(Kind::User, &long(0)).await.unwrap();
    let mut call = within(asked.recv())
        .await
        .expect("the compactor asks the model");
    drop(owner);
    within(call.closed()).await;
}

/// A node whose calls keep failing is built from its input, cut to
/// [`NODE`] bytes, at its third failure: the waiting turn gets a line
/// that fits, not an error, and the node is not tried again.
#[tokio::test(start_paused = true)]
async fn a_node_that_keeps_failing_is_built_from_its_input() {
    let dir = tempfile::tempdir().unwrap();
    let summarizer = Scripted::with(vec![
        Err(anyhow::anyhow!("overloaded")),
        Err(anyhow::anyhow!("overloaded")),
        Err(anyhow::anyhow!("overloaded")),
    ]);
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    let message = format!("echo: {}", "y".repeat(NODE));
    memory.append(Kind::Echo, &message[6..]).await.unwrap();
    let view = format!("<chat>\n0+1|{}\n</chat>", cut(&message));
    assert_eq!(
        (
            memory.settled_render(SETTLE_TIMEOUT).await.unwrap().text,
            memory.render().await.unwrap().text,
            summarizer.requests().len(),
            memory.status().await.unwrap().last_error,
        ),
        (view.clone(), view, 3, None)
    );
}

/// A model whose every call fails; its [`FAILURES`]-th call first moves
/// the message log away, so no message can be read from then on.
struct LosesTheLog {
    calls: std::sync::atomic::AtomicU32,
    log: std::path::PathBuf,
}

impl Summarizer for LosesTheLog {
    fn complete(&self, _context: Context, _started: ResponseStarted) -> SummarizerFuture {
        let call = self.calls.fetch_add(1, std::sync::atomic::Ordering::SeqCst) + 1;
        if call == FAILURES {
            std::fs::rename(&self.log, self.log.with_extension("gone")).unwrap();
        }
        Box::pin(async { Err(anyhow::anyhow!("overloaded")) })
    }
}

/// Regression (H1.5): the failure cap builds a node from the input its
/// failed call had, with no read, so a log that cannot be read by then
/// does not keep the node unbuilt. The old cap read the message again:
/// the node stayed unbuilt and the waiting turn got an error.
#[tokio::test(start_paused = true)]
async fn the_failure_cap_reads_nothing() {
    let dir = tempfile::tempdir().unwrap();
    let summarizer = Arc::new(LosesTheLog {
        calls: std::sync::atomic::AtomicU32::new(0),
        log: dir.path().join("main"),
    });
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    let message = format!("echo: {}", "y".repeat(NODE));
    memory.append(Kind::Echo, &message[6..]).await.unwrap();
    assert_eq!(
        (
            memory.settled_render(SETTLE_TIMEOUT).await.unwrap().text,
            summarizer.calls.load(std::sync::atomic::Ordering::SeqCst),
        ),
        (format!("<chat>\n0+1|{}\n</chat>", cut(&message)), FAILURES)
    );
}

/// A turn whose message the model never summarizes gets the view at its
/// deadline, the line shown as the message cut to [`NODE`] bytes: never
/// an error, never a placeholder (H2.3). The deadline runs on the owner
/// thread's clock, so this test runs in real time.
#[tokio::test]
async fn a_turn_gets_the_view_by_its_deadline_when_the_model_never_answers() {
    let dir = tempfile::tempdir().unwrap();
    let memory = Memory::open(dir.path(), Arc::new(Silent)).await.unwrap();
    let message = format!("echo: {}", "y".repeat(NODE));
    memory.append(Kind::Echo, &message[6..]).await.unwrap();
    let deadline = Duration::from_millis(200);
    let asked = std::time::Instant::now();
    let view = within(memory.settled_render(deadline)).await.unwrap().text;
    assert_eq!(
        (
            view,
            asked.elapsed() >= deadline,
            memory.render().await.unwrap().text
        ),
        (
            format!("<chat>\n0+1|{}\n</chat>", cut(&message)),
            true,
            format!("<chat>\n0+1|{PLACEHOLDER}\n</chat>")
        )
    );
}

/// A model that answers with thinking only (an empty line) still gives a
/// line that fits: the message cut to [`NODE`] bytes, after one call.
#[tokio::test(start_paused = true)]
async fn an_empty_reply_still_gives_a_line_that_fits() {
    let dir = tempfile::tempdir().unwrap();
    let summarizer = Scripted::with(vec![Ok(thinking_only())]);
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    let message = format!("echo: {}", "y".repeat(NODE));
    memory.append(Kind::Echo, &message[6..]).await.unwrap();
    assert_eq!(
        (
            memory.settled_render(SETTLE_TIMEOUT).await.unwrap().text,
            summarizer.requests().len()
        ),
        (format!("<chat>\n0+1|{}\n</chat>", cut(&message)), 1)
    );
}

/// A provider that serves one request at a time, as a local model does: a
/// merge takes the slot and never answers; a message's summary answers
/// [`leaf`]. Each call reports whether it is a merge.
struct OneSlot {
    slot: Arc<tokio::sync::Semaphore>,
    calls: mpsc::UnboundedSender<bool>,
}

/// A summary line: two of them are too long to be their own merge.
fn leaf() -> String {
    "l".repeat(NODE / 2 + 1)
}

/// Whether a user text is a merge task.
fn is_merge(text: &str) -> bool {
    text.starts_with("Compaction: merge")
}

impl Summarizer for OneSlot {
    fn complete(&self, context: Context, mut started: ResponseStarted) -> SummarizerFuture {
        let merge = context.messages.iter().any(|message| match message {
            Message::User(user) => match &user.content {
                UserContent::Blocks(blocks) => blocks.iter().any(|block| match block {
                    UserContentBlock::Text(text) => is_merge(&text.text),
                    UserContentBlock::Image(_) => false,
                }),
                UserContent::Text(text) => is_merge(text),
            },
            Message::System(_) | Message::Assistant(_) | Message::ToolResult(_) => false,
        });
        let _ = self.calls.send(merge);
        let slot = Arc::clone(&self.slot);
        Box::pin(async move {
            let _slot = slot.acquire_owned().await?;
            started.signal();
            if merge {
                std::future::pending::<()>().await;
            }
            Ok(reply(&leaf()))
        })
    }
}

/// The incident (H2.1): on a one-slot provider a merge call holds the
/// slot, and the line a turn needs waits behind it. A waiting turn stops
/// the merge, so the needed line goes at once; the stopped merge is no
/// failure and starts again once the view is settled.
#[tokio::test]
async fn a_waiting_turn_stops_a_merge_that_holds_the_slot() {
    let dir = tempfile::tempdir().unwrap();
    let (calls, mut asked) = mpsc::unbounded_channel();
    let memory = Memory::open(
        dir.path(),
        Arc::new(OneSlot {
            slot: Arc::new(tokio::sync::Semaphore::new(1)),
            calls,
        }),
    )
    .await
    .unwrap();
    memory.append(Kind::User, &long(0)).await.unwrap();
    memory.append(Kind::User, &long(1)).await.unwrap();
    let mut kinds = Vec::new();
    for _ in 0..3 {
        kinds.push(within(asked.recv()).await.unwrap());
    }
    // The merge of the two lines runs and holds the slot; the third
    // message's summary queues behind it.
    memory.append(Kind::User, &long(2)).await.unwrap();
    let view = within(memory.settled_render(Duration::from_secs(3600)))
        .await
        .unwrap()
        .text;
    for _ in 0..2 {
        kinds.push(within(asked.recv()).await.unwrap());
    }
    assert_eq!(
        (view, kinds, memory.status().await.unwrap().last_error),
        (
            format!("<chat>\n0+1|{0}\n1+1|{0}\n2+1|{0}\n</chat>", leaf()),
            vec![false, false, true, false, true],
            None
        )
    );
}

/// Regression: a client's settled render with a huge
/// `memory.settleTimeoutMs` panicked adding its reply deadline to now.
#[tokio::test]
async fn a_huge_settle_timeout_does_not_overflow_the_reply_deadline() {
    let deadline = Request::SettledRender {
        within_ms: u64::MAX,
    }
    .reply_deadline();
    assert_eq!(super::answered(deadline, async { 7 }).await.unwrap(), 7);
}
