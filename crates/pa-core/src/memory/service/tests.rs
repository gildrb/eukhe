use std::sync::Arc;

use super::*;
use crate::memory::compactor::tests::{reply, Scripted};
use crate::memory::{import_optmem, PLACEHOLDER};

fn no_model() -> Arc<Scripted> {
    Scripted::with(Vec::new())
}

#[tokio::test]
async fn short_messages_are_their_own_lines() {
    let dir = tempfile::tempdir().unwrap();
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    assert!(memory.owns().await);
    assert_eq!(memory.append(Kind::User, "hello").await.unwrap(), 0);
    assert_eq!(memory.append(Kind::Talk, "hi\nthere").await.unwrap(), 1);
    memory.settle().await.unwrap();
    let view = memory.render().await.unwrap();
    assert_eq!(view.messages, 2);
    assert_eq!(
        view.text,
        "<chat>\n0+1|user: hello\n1+1|talk: hi there\n</chat>"
    );
    assert_eq!(view.pieces(), vec![view.text.clone()]);
    assert_eq!(memory.zoom(1, 1).await.unwrap(), "1+0|talk: hi\nthere");
    // The free merge of 0 and 1 exists already.
    assert_eq!(
        memory.zoom(0, 2).await.unwrap(),
        "0+1|user: hello\n1+1|talk: hi there"
    );
    assert_eq!(memory.zoom(0, 4).await.unwrap(), "No line 0+4.");
    let date = memory.date(0).await.unwrap();
    assert_eq!(date.len(), "2026-10-05 09:32:11 +02:00".len(), "{date}");
    assert_eq!(memory.date(9).await.unwrap(), "No message 9.");
    let status = memory.status().await.unwrap();
    assert_eq!(
        status,
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
}

#[tokio::test]
async fn long_messages_wait_for_the_compactor() {
    let dir = tempfile::tempdir().unwrap();
    let summarizer = Scripted::with(vec![Ok(reply("echo: a long listing, summarized"))]);
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    let long = "x".repeat(2_000);
    memory.append(Kind::Echo, &long).await.unwrap();
    memory.settle().await.unwrap();
    assert_eq!(
        memory.render().await.unwrap().text,
        "<chat>\n0+1|echo: a long listing, summarized\n</chat>"
    );
    // The whole message stays one zoom away.
    assert_eq!(
        memory.zoom(0, 1).await.unwrap(),
        format!("0+0|echo: {long}")
    );
    let requests = summarizer.requests.lock().unwrap();
    assert_eq!(requests.len(), 1);
    let pa_types::ai::Message::User(user) = &requests[0].messages[0] else {
        panic!("user message");
    };
    let text = user.content.text();
    assert!(text.contains("<chat>\n</chat>"), "{text}");
    assert!(text.ends_with(&format!(
        "Compress this message into one line, in at most 512 bytes:\necho: {long}"
    )));
}

#[tokio::test]
async fn a_reopened_chat_folds_the_same_view() {
    let dir = tempfile::tempdir().unwrap();
    let before = {
        let memory = Memory::open(dir.path(), no_model()).await.unwrap();
        for i in 0..5 {
            memory.append(Kind::User, &format!("m{i}")).await.unwrap();
        }
        memory.settle().await.unwrap();
        memory.render().await.unwrap()
    };
    let memory = Memory::open(dir.path(), no_model()).await.unwrap();
    assert!(memory.owns().await);
    assert_eq!(memory.render().await.unwrap(), before);
    assert_eq!(memory.append(Kind::User, "m5").await.unwrap(), 5);
}

#[tokio::test]
async fn a_second_handle_is_a_client_and_takes_over() {
    let dir = tempfile::tempdir().unwrap();
    let owner = Memory::open(dir.path(), no_model()).await.unwrap();
    let client = Memory::open(dir.path(), no_model()).await.unwrap();
    assert!(owner.owns().await);
    assert!(!client.owns().await);
    assert_eq!(
        client.append(Kind::User, "from the client").await.unwrap(),
        0
    );
    owner.settle().await.unwrap();
    assert_eq!(
        owner.render().await.unwrap().text,
        "<chat>\n0+1|user: from the client\n</chat>"
    );
    drop(owner);
    // The owner's socket now refuses connections: the client takes over.
    let mut attempts = 0;
    let id = loop {
        attempts += 1;
        match client.append(Kind::User, "after the owner").await {
            Ok(id) => break id,
            Err(error) if attempts < 50 => {
                let _ = error;
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
            Err(error) => panic!("takeover failed: {error:#}"),
        }
    };
    assert_eq!(id, 1);
    assert!(client.owns().await);
}

#[cfg(unix)]
#[tokio::test]
async fn a_stale_socket_is_taken_over() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::create_dir_all(dir.path()).unwrap();
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
    assert_eq!(
        memory.request(append(false)).await.unwrap(),
        Reply::Appended { id: 0 }
    );
    assert_eq!(
        memory.request(append(true)).await.unwrap(),
        Reply::Appended { id: 0 }
    );
    assert_eq!(
        memory.request(append(false)).await.unwrap(),
        Reply::Appended { id: 1 }
    );
}

#[tokio::test(start_paused = true)]
async fn settle_fails_after_repeated_compactor_failures() {
    let dir = tempfile::tempdir().unwrap();
    let summarizer = Scripted::with(vec![
        Err(anyhow::anyhow!("overloaded")),
        Err(anyhow::anyhow!("overloaded")),
        Err(anyhow::anyhow!("overloaded")),
        Ok(reply("echo: recovered")),
    ]);
    let memory = Memory::open(dir.path(), summarizer.clone()).await.unwrap();
    memory.append(Kind::Echo, &"y".repeat(600)).await.unwrap();
    let error = memory.settle().await.unwrap_err();
    assert!(format!("{error:#}").contains("overloaded"), "{error:#}");
    assert_eq!(
        memory.render().await.unwrap().text,
        format!("<chat>\n0+1|{PLACEHOLDER}\n</chat>")
    );
    // The compactor keeps retrying; a new wait triggers the next try now.
    memory.settle().await.unwrap();
    assert_eq!(
        memory.render().await.unwrap().text,
        "<chat>\n0+1|echo: recovered\n</chat>"
    );
}

#[tokio::test]
async fn optmem_notes_keep_their_ids() {
    let dir = tempfile::tempdir().unwrap();
    let optmem = tempfile::tempdir().unwrap();
    std::fs::write(
        optmem.path().join("LOG.txt"),
        "#0 2026-08-03 first note      \n#1 2026-08-04 second note\n",
    )
    .unwrap();
    let memory = Memory::open(dir.path().join("chat"), no_model())
        .await
        .unwrap();
    let report = import_optmem(&memory, optmem.path()).await.unwrap();
    assert_eq!((report.first, report.count), (Some(0), 2));
    memory.settle().await.unwrap();
    assert_eq!(memory.zoom(1, 1).await.unwrap(), "1+0|note: second note");
    assert_eq!(memory.date(0).await.unwrap(), "2026-08-03");
    // A second import would shift the ids: refused.
    assert!(import_optmem(&memory, optmem.path()).await.is_err());
}
