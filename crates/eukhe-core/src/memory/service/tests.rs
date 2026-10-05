//! The owner and its clients over the real lock socket: a turn's view is
//! never a placeholder, and the root-turn lease goes around in order and
//! survives cancelled waits, clients that hang up, and owner changes. Then
//! the owner's own duties: free and model-built lines, the compactor's
//! input and retries, zoom and date, reloads and takeovers.

use std::fmt::Write as _;
use std::future::Future;
use std::sync::Arc;
use std::time::Duration;

use eukhe_types::ai::{
    AssistantContentBlock, AssistantMessage, Context, Message, StopReason, TextContent, Usage,
    UserContent, UserContentBlock,
};
use eukhe_types::platform::transport::connect_transport;
use tokio::sync::{mpsc, oneshot};

use super::turn::TURN_FILE;
use super::{
    commit, Client, ImportItem, Memory, MemoryStatus, Outcome, RenderedView, Reply, Request,
};
use crate::memory::compactor::tests::{reply, Scripted};
use crate::memory::prompts::{compress_step, merge_step, COMPACT};
use crate::memory::{Kind, Summarizer, SummarizerFuture, NODE, PLACEHOLDER, RETRY};

/// A compactor call the test answers with the line.
type Call = oneshot::Sender<String>;

/// A compactor whose every call waits for the test's answer.
struct Gated {
    calls: mpsc::UnboundedSender<Call>,
}

impl Summarizer for Gated {
    fn complete(&self, _context: Context) -> SummarizerFuture {
        let (answer, line) = oneshot::channel();
        let asked = self.calls.send(answer);
        Box::pin(async move {
            asked.map_err(|_| anyhow::anyhow!("the test stopped answering"))?;
            let text = line.await?;
            Ok(AssistantMessage {
                content: vec![AssistantContentBlock::Text(TextContent {
                    text,
                    text_signature: None,
                    rest: serde_json::Map::default(),
                    cache_breakpoint: None,
                })],
                api: "anthropic-messages".to_string(),
                provider: "test".to_string(),
                model: "compactor".to_string(),
                response_model: None,
                response_id: None,
                diagnostics: None,
                usage: Usage::default(),
                stop_reason: StopReason::Stop,
                stop_reason_raw: None,
                error_message: None,
                timestamp: 0,
                rest: serde_json::Map::default(),
            })
        })
    }
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
            async move { reader.settled_render().await }
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

#[test]
fn a_commit_keeps_the_turn_file_out_of_a_chat_committed_before_it() {
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
    commit(dir.path(), &dir.path().join(".git")).unwrap();
    assert_eq!(
        (
            std::fs::read_to_string(dir.path().join(".gitignore")).unwrap(),
            git(&["ls-files"]),
        ),
        (
            "lock\nlock.lock/\nturn\n".to_string(),
            ".gitignore\nmain/2026-10-05.jsonl\n".to_string(),
        )
    );
}

fn no_model() -> Arc<Scripted> {
    Scripted::with(Vec::new())
}

/// A compactor request as its system prompt and its text blocks.
fn request_texts(context: &Context) -> (Option<String>, Vec<String>) {
    let texts = context
        .messages
        .iter()
        .flat_map(|message| match message {
            Message::User(user) => match &user.content {
                UserContent::Text(text) => vec![text.clone()],
                UserContent::Blocks(blocks) => blocks
                    .iter()
                    .map(|block| match block {
                        UserContentBlock::Text(text) => text.text.clone(),
                        UserContentBlock::Image(_) | UserContentBlock::Raw(_) => {
                            panic!("a compactor request holds text only")
                        }
                    })
                    .collect(),
            },
            Message::Assistant(_) | Message::ToolResult(_) => {
                panic!("a first compactor request is one user message")
            }
        })
        .collect();
    (context.system_prompt.clone(), texts)
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
    assert_eq!(memory.append(Kind::Talk, "hi\nthere").await.unwrap(), 1);
    assert_eq!(
        memory.settled_render().await.unwrap(),
        RenderedView {
            messages: 2,
            text: "<chat>\n0+1|user: hello\n1+1|talk: hi there\n</chat>".to_string(),
        }
    );
    assert_eq!(
        [
            memory.zoom(1, 1).await.unwrap(),
            memory.zoom(0, 2).await.unwrap(),
            memory.zoom(0, 4).await.unwrap(),
        ],
        [
            "1+0|talk: hi\nthere",
            "0+1|user: hello\n1+1|talk: hi there",
            "No line 0+4.",
        ]
    );
    assert_eq!(
        memory.status().await.unwrap(),
        MemoryStatus {
            messages: 2,
            nodes: 3,
            view_lines: 2,
            view_bytes: ("user: hello".len() + "talk: hi\nthere".len()) as u64,
            unsummarized: 0,
            running: 0,
            last_error: None,
        }
    );
    assert_eq!(summarizer.requests(), Vec::new());
}

/// Every compactor call sees the bare view lines up to its node, never an
/// id: a message goes whole under the step, a merge writes both lines out
/// again; the view then shows the model's lines, the message stays one zoom
/// away.
#[tokio::test]
async fn the_compactor_sees_bare_lines_and_whole_inputs() {
    let dir = tempfile::tempdir().unwrap();
    let first = format!("echo: first, {}", "a".repeat(287));
    let second = format!("echo: second, {}", "b".repeat(286));
    let summarizer = Scripted::with(vec![
        Ok(reply(&first)),
        Ok(reply(&second)),
        Ok(reply("echo: both listings")),
    ]);
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    let long = |c: &str| c.repeat(NODE);
    memory.append(Kind::Echo, &long("x")).await.unwrap();
    memory.append(Kind::Echo, &long("y\n")).await.unwrap();
    let requests: Vec<_> = summarizer
        .requested(3)
        .await
        .iter()
        .map(request_texts)
        .collect();
    let compact = Some(COMPACT.to_string());
    assert_eq!(
        requests,
        [
            (
                compact.clone(),
                vec![
                    "<chat>\n</chat>".to_string(),
                    compress_step(&format!("echo: {}", long("x"))),
                ]
            ),
            (
                compact.clone(),
                vec![
                    format!("<chat>\n{first}\n</chat>"),
                    compress_step(&format!("echo: {}", long("y\n"))),
                ]
            ),
            (
                compact,
                vec![
                    format!("<chat>\n{first}\n{second}\n</chat>"),
                    merge_step(&first, &second),
                ]
            ),
        ]
    );
    assert_eq!(
        (
            memory.settled_render().await.unwrap().text,
            memory.zoom(1, 1).await.unwrap()
        ),
        (
            format!("<chat>\n0+1|{first}\n1+1|{second}\n</chat>"),
            format!("1+0|echo: {}", long("y\n"))
        )
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
        .import(
            None,
            vec![
                item("2026-10-05T09:32:11.123+02:00"),
                item("2026-10-05T07:32:11Z"),
                item("2026-08-03"),
            ],
        )
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

/// The view is not saved: a reopened chat folds the same view again.
#[tokio::test]
async fn a_reopened_chat_folds_the_same_view() {
    let dir = tempfile::tempdir().unwrap();
    let before = {
        let memory = Memory::open(dir.path(), no_model()).await.unwrap();
        for i in 0..5 {
            memory.append(Kind::User, &format!("m{i}")).await.unwrap();
        }
        memory.settled_render().await.unwrap()
    };
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    assert!(memory.owns().await);
    assert_eq!(memory.render().await.unwrap(), before);
    assert_eq!(memory.append(Kind::User, "m5").await.unwrap(), 5);
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
        owner.settled_render().await.unwrap().text,
        "<chat>\n0+1|user: from the client\n</chat>"
    );
    drop(owner);
    assert_eq!(
        client.append(Kind::User, "after the owner").await.unwrap(),
        1
    );
    assert!(client.owns().await);
    assert_eq!(
        client.settled_render().await.unwrap().text,
        "<chat>\n0+1|user: from the client\n1+1|user: after the owner\n</chat>"
    );
}

/// A socket that refuses connections is stale (its owner died): the next
/// process takes it over.
#[cfg(unix)]
#[tokio::test]
async fn a_stale_socket_is_taken_over() {
    let dir = tempfile::tempdir().unwrap();
    let lock = dir.path().join("lock");
    drop(std::os::unix::net::UnixListener::bind(&lock).unwrap());
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

/// A failed node is reported and tried again every [`RETRY`], with no
/// backoff, until it is built.
#[tokio::test(start_paused = true)]
async fn a_failed_node_is_retried_at_a_fixed_delay() {
    let dir = tempfile::tempdir().unwrap();
    let summarizer = Scripted::with(vec![
        Err(anyhow::anyhow!("overloaded")),
        Err(anyhow::anyhow!("overloaded")),
        Ok(reply("echo: recovered")),
    ]);
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    memory.append(Kind::Echo, &"y".repeat(NODE)).await.unwrap();
    summarizer.requested(2).await;
    assert_eq!(
        memory.status().await.unwrap(),
        MemoryStatus {
            messages: 1,
            nodes: 0,
            view_lines: 1,
            view_bytes: PLACEHOLDER.len() as u64,
            unsummarized: 1,
            running: 1,
            last_error: Some("overloaded".to_string()),
        }
    );
    summarizer.requested(3).await;
    assert_eq!(
        memory.settled_render().await.unwrap().text,
        "<chat>\n0+1|echo: recovered\n</chat>"
    );
    let times = summarizer.times();
    assert_eq!(
        times
            .windows(2)
            .map(|pair| pair[1] - pair[0])
            .collect::<Vec<_>>(),
        [RETRY, RETRY]
    );
    assert_eq!(memory.status().await.unwrap().last_error, None);
}

/// A turn waiting for the view fails with the compactor's error once the
/// node it waits on keeps failing; the compactor goes on, and a new wait
/// tries the node again at once.
#[tokio::test(start_paused = true)]
async fn a_settled_render_fails_after_repeated_compactor_failures() {
    let dir = tempfile::tempdir().unwrap();
    let summarizer = Scripted::with(vec![
        Err(anyhow::anyhow!("overloaded")),
        Err(anyhow::anyhow!("overloaded")),
        Err(anyhow::anyhow!("overloaded")),
        Ok(reply("echo: recovered")),
    ]);
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    memory.append(Kind::Echo, &"y".repeat(NODE)).await.unwrap();
    let error = memory.settled_render().await.unwrap_err();
    assert!(format!("{error:#}").contains("overloaded"), "{error:#}");
    assert_eq!(
        memory.render().await.unwrap().text,
        format!("<chat>\n0+1|{PLACEHOLDER}\n</chat>")
    );
    assert_eq!(
        memory.settled_render().await.unwrap().text,
        "<chat>\n0+1|echo: recovered\n</chat>"
    );
}
