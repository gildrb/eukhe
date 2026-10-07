//! `write` and `edit` cases of `test/tools.test.ts`.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use eukhe_chord::context::{with_abort_signal, AbortController, BACKGROUND_CONTEXT};
use eukhe_chord::json::from_json;
use futures::FutureExt;
use serde_json::json;
use tokio::sync::Notify;

use super::support::{
    execute, native, read_file, run, temp_dir, text_output, write_file, FakeApi, HookedEnv,
};
use crate::env::{ExecutionEnv, FileSystem};
use crate::tools::{create_edit_tool, create_write_tool};

/// How long a blocked call is given to (wrongly) proceed, like the TS
/// `delay(20)`.
const PROCEED_WINDOW: Duration = Duration::from_millis(20);

/// TS `BlockingWriteExecutionEnv`: the write of `"first\n"` waits for
/// `finish_first`; a write of `"second\n"` is recorded.
struct BlockingWrites {
    first_started: Arc<Notify>,
    finish_first: Arc<Notify>,
    second_started: Arc<AtomicBool>,
}

fn blocking_write_env(env: crate::env::NativeExecutionEnv) -> (HookedEnv, BlockingWrites) {
    let state = BlockingWrites {
        first_started: Arc::new(Notify::new()),
        finish_first: Arc::new(Notify::new()),
        second_started: Arc::new(AtomicBool::new(false)),
    };
    let (started, finish, second) = (
        Arc::clone(&state.first_started),
        Arc::clone(&state.finish_first),
        Arc::clone(&state.second_started),
    );
    let mut hooked = HookedEnv::new(env);
    hooked.write_file = Some(Arc::new(move |inner, path, content, cx| {
        let (started, finish, second) = (
            Arc::clone(&started),
            Arc::clone(&finish),
            Arc::clone(&second),
        );
        async move {
            if content == b"first\n" {
                started.notify_one();
                finish.notified().await;
            } else if content == b"second\n" {
                second.store(true, Ordering::SeqCst);
            }
            inner.write_file(path, content, cx).await
        }
        .boxed()
    }));
    (hooked, state)
}

/// TS `SlowReadExecutionEnv`: every text read first waits 20ms.
fn slow_read_env(env: crate::env::NativeExecutionEnv) -> HookedEnv {
    let mut hooked = HookedEnv::new(env);
    hooked.read_text_file = Some(Arc::new(|inner, path, cx| {
        async move {
            tokio::time::sleep(PROCEED_WINDOW).await;
            inner.read_text_file(path, cx).await
        }
        .boxed()
    }));
    hooked
}

#[tokio::test]
async fn writes_files_and_creates_parent_directories() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    let (result, _) = run(
        &create_write_tool(),
        json!({ "path": "nested/dir/file.txt", "content": "hello" }),
        Arc::clone(&env) as Arc<dyn ExecutionEnv>,
    )
    .await;
    assert_eq!(
        text_output(&result.unwrap()),
        "Successfully wrote to nested/dir/file.txt"
    );
    assert_eq!(
        read_file(env.as_ref(), "nested/dir/file.txt").await,
        "hello"
    );
}

#[tokio::test]
async fn keeps_the_mutation_queue_locked_until_an_aborted_write_settles() {
    let dir = temp_dir();
    let (env, state) = blocking_write_env(native(&dir));
    let env: Arc<dyn ExecutionEnv> = Arc::new(env);
    let tool = create_write_tool();
    let controller = AbortController::new();
    let first = {
        let (tool, env) = (Arc::clone(&tool), Arc::clone(&env));
        let cx = with_abort_signal(&controller.signal(), &BACKGROUND_CONTEXT);
        tokio::spawn(async move {
            let api = FakeApi::new(Some(env));
            execute(
                &tool,
                json!({ "path": "file.txt", "content": "first\n" }),
                &api,
                &cx,
            )
            .await
        })
    };
    state.first_started.notified().await;
    controller.abort(None);
    let second = {
        let (tool, env) = (Arc::clone(&tool), Arc::clone(&env));
        tokio::spawn(async move {
            run(
                &tool,
                json!({ "path": "file.txt", "content": "second\n" }),
                env,
            )
            .await
            .0
        })
    };
    tokio::time::sleep(PROCEED_WINDOW).await;
    assert!(!state.second_started.load(Ordering::SeqCst));
    state.finish_first.notify_one();
    assert!(first.await.unwrap().is_err());
    second.await.unwrap().unwrap();
    assert_eq!(read_file(env.as_ref(), "file.txt").await, "second\n");
}

#[tokio::test]
async fn applies_disjoint_edits_and_returns_both_diff_formats() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    let original = "alpha\nbeta\ngamma\ndelta\n";
    write_file(env.as_ref(), "edit.txt", original).await;
    let (result, _) = run(
        &create_edit_tool(),
        json!({
            "path": "edit.txt",
            "edits": [
                { "oldText": "alpha\n", "newText": "ALPHA\n" },
                { "oldText": "gamma\n", "newText": "GAMMA\n" }
            ]
        }),
        Arc::clone(&env) as Arc<dyn ExecutionEnv>,
    )
    .await;
    let result = result.unwrap();
    let details: serde_json::Value = from_json(result.details.as_ref().unwrap()).unwrap();
    assert_eq!(
        text_output(&result),
        "Successfully replaced 2 block(s) in edit.txt."
    );
    let diff = details["diff"].as_str().unwrap();
    assert!(diff.contains("ALPHA"));
    assert!(diff.contains("GAMMA"));
    // `applyPatch(original, patch)`: the hunks of this patch replace exactly the edited lines.
    let patch = details["patch"].as_str().unwrap();
    assert!(patch.contains("-alpha\n+ALPHA\n"));
    assert!(patch.contains("-gamma\n+GAMMA\n"));
    assert_eq!(
        read_file(env.as_ref(), "edit.txt").await,
        "ALPHA\nbeta\nGAMMA\ndelta\n"
    );
}

#[test]
fn repairs_edits_sent_as_a_json_string_a_single_object_or_top_level_old_text_new_text_without_mutating_them(
) {
    let tool = create_edit_tool();
    let prepare = tool.prepare_arguments.as_ref().unwrap();
    let edit = json!({ "oldText": "a", "newText": "b" });
    let as_string = json!({ "path": "f", "edits": serde_json::to_string(&json!([edit])).unwrap() });
    assert_eq!(
        prepare(as_string.clone()).unwrap(),
        json!({ "path": "f", "edits": [edit] })
    );
    assert_eq!(
        as_string["edits"],
        json!(serde_json::to_string(&json!([edit])).unwrap())
    );
    assert_eq!(
        prepare(json!({ "path": "f", "edits": serde_json::to_string(&edit).unwrap() })).unwrap(),
        json!({ "path": "f", "edits": [edit] })
    );
    assert_eq!(
        prepare(json!({ "path": "f", "edits": edit })).unwrap(),
        json!({ "path": "f", "edits": [edit] })
    );
    assert_eq!(
        prepare(json!({ "path": "f", "edits": [edit], "oldText": "c", "newText": "d" })).unwrap(),
        json!({ "path": "f", "edits": [edit, { "oldText": "c", "newText": "d" }] })
    );
    assert_eq!(
        prepare(json!({ "path": "f", "edits": "not json" })).unwrap(),
        json!({ "path": "f", "edits": "not json" })
    );
}

#[tokio::test]
async fn matches_all_edits_against_the_original_and_rejects_overlaps() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    write_file(env.as_ref(), "edit.txt", "one\ntwo\nthree\n").await;
    let (result, _) = run(
        &create_edit_tool(),
        json!({
            "path": "edit.txt",
            "edits": [
                { "oldText": "one\ntwo\n", "newText": "ONE\nTWO\n" },
                { "oldText": "two\nthree\n", "newText": "TWO\nTHREE\n" }
            ]
        }),
        Arc::clone(&env) as Arc<dyn ExecutionEnv>,
    )
    .await;
    assert!(result.unwrap_err().to_string().contains("overlap"));
    assert_eq!(
        read_file(env.as_ref(), "edit.txt").await,
        "one\ntwo\nthree\n"
    );
}

#[tokio::test]
async fn rejects_missing_and_duplicate_target_text() {
    let dir = temp_dir();
    let env: Arc<dyn ExecutionEnv> = Arc::new(native(&dir));
    write_file(env.as_ref(), "edit.txt", "foo foo foo").await;
    let tool = create_edit_tool();
    let (missing, _) = run(
        &tool,
        json!({ "path": "edit.txt", "edits": [{ "oldText": "bar", "newText": "baz" }] }),
        Arc::clone(&env),
    )
    .await;
    assert!(missing
        .unwrap_err()
        .to_string()
        .contains("Could not find the exact text"));
    let (duplicate, _) = run(
        &tool,
        json!({ "path": "edit.txt", "edits": [{ "oldText": "foo", "newText": "bar" }] }),
        env,
    )
    .await;
    assert!(duplicate
        .unwrap_err()
        .to_string()
        .contains("Found 3 occurrences"));
}

#[tokio::test]
async fn keeps_the_mutation_queue_locked_until_an_aborted_edit_write_settles() {
    let dir = temp_dir();
    let started = Arc::new(Notify::new());
    let finish = Arc::new(Notify::new());
    let first_settled = Arc::new(AtomicBool::new(false));
    let second_started = Arc::new(AtomicBool::new(false));
    let mut hooked = HookedEnv::new(native(&dir));
    {
        let (started, finish, first_settled, second_started) = (
            Arc::clone(&started),
            Arc::clone(&finish),
            Arc::clone(&first_settled),
            Arc::clone(&second_started),
        );
        hooked.write_file = Some(Arc::new(move |inner, path, content, cx| {
            let (started, finish, first_settled, second_started) = (
                Arc::clone(&started),
                Arc::clone(&finish),
                Arc::clone(&first_settled),
                Arc::clone(&second_started),
            );
            async move {
                if content == b"ALPHA\nbeta\n" {
                    started.notify_one();
                    finish.notified().await;
                    let result = inner.write_file(path, content, &BACKGROUND_CONTEXT).await;
                    first_settled.store(true, Ordering::SeqCst);
                    return result;
                }
                if content == b"ALPHA\nBETA\n" || content == b"alpha\nBETA\n" {
                    second_started.store(true, Ordering::SeqCst);
                }
                inner.write_file(path, content, cx).await
            }
            .boxed()
        }));
    }
    write_file(&hooked, "file.txt", "alpha\nbeta\n").await;
    let env: Arc<dyn ExecutionEnv> = Arc::new(hooked);
    let tool = create_edit_tool();
    let controller = AbortController::new();
    let first = {
        let (tool, env) = (Arc::clone(&tool), Arc::clone(&env));
        let cx = with_abort_signal(&controller.signal(), &BACKGROUND_CONTEXT);
        tokio::spawn(async move {
            let api = FakeApi::new(Some(env));
            let args = json!({ "path": "file.txt", "edits": [{ "oldText": "alpha", "newText": "ALPHA" }] });
            execute(&tool, args, &api, &cx).await
        })
    };
    started.notified().await;
    controller.abort(None);
    let second = {
        let (tool, env) = (Arc::clone(&tool), Arc::clone(&env));
        tokio::spawn(async move {
            let args =
                json!({ "path": "file.txt", "edits": [{ "oldText": "beta", "newText": "BETA" }] });
            run(&tool, args, env).await.0
        })
    };
    tokio::time::sleep(PROCEED_WINDOW).await;
    assert!(!second_started.load(Ordering::SeqCst));
    finish.notify_one();
    assert!(first
        .await
        .unwrap()
        .unwrap_err()
        .to_string()
        .contains("Operation aborted"));
    second.await.unwrap().unwrap();
    assert!(first_settled.load(Ordering::SeqCst));
    assert_eq!(read_file(env.as_ref(), "file.txt").await, "ALPHA\nBETA\n");
}

#[tokio::test]
async fn serializes_concurrent_edits_through_canonical_and_symlink_paths() {
    let dir = temp_dir();
    let env: Arc<dyn ExecutionEnv> = Arc::new(slow_read_env(native(&dir)));
    write_file(env.as_ref(), "target.txt", "alpha\nbeta\ngamma\n").await;
    std::os::unix::fs::symlink("target.txt", dir.path().join("link.txt")).unwrap();
    let tool = create_edit_tool();
    let (first, second) = tokio::join!(
        run(
            &tool,
            json!({ "path": "target.txt", "edits": [{ "oldText": "alpha", "newText": "ALPHA" }] }),
            Arc::clone(&env)
        ),
        run(
            &tool,
            json!({ "path": "link.txt", "edits": [{ "oldText": "beta", "newText": "BETA" }] }),
            Arc::clone(&env)
        ),
    );
    first.0.unwrap();
    second.0.unwrap();
    assert_eq!(
        read_file(env.as_ref(), "target.txt").await,
        "ALPHA\nBETA\ngamma\n"
    );
}

#[tokio::test]
async fn serializes_edits_of_one_file_across_environment_objects_of_one_file_system() {
    let dir = temp_dir();
    let first: Arc<dyn ExecutionEnv> = Arc::new(slow_read_env(native(&dir)));
    let second: Arc<dyn ExecutionEnv> = Arc::new(slow_read_env(native(&dir)));
    write_file(first.as_ref(), "file.txt", "alpha\nbeta\n").await;
    let tool = create_edit_tool();
    let (a, b) = tokio::join!(
        run(
            &tool,
            json!({ "path": "file.txt", "edits": [{ "oldText": "alpha", "newText": "ALPHA" }] }),
            Arc::clone(&first)
        ),
        run(
            &tool,
            json!({ "path": "file.txt", "edits": [{ "oldText": "beta", "newText": "BETA" }] }),
            second
        ),
    );
    a.0.unwrap();
    b.0.unwrap();
    assert_eq!(read_file(first.as_ref(), "file.txt").await, "ALPHA\nBETA\n");
}

#[tokio::test]
async fn serializes_a_new_file_created_through_a_symlinked_directory_with_its_canonical_path() {
    let dir = temp_dir();
    std::fs::create_dir(dir.path().join("real")).unwrap();
    std::os::unix::fs::symlink(dir.path().join("real"), dir.path().join("link")).unwrap();
    let (env, state) = blocking_write_env(native(&dir));
    let env: Arc<dyn ExecutionEnv> = Arc::new(env);
    let tool = create_write_tool();
    let first = {
        let (tool, env) = (Arc::clone(&tool), Arc::clone(&env));
        tokio::spawn(async move {
            run(
                &tool,
                json!({ "path": "link/new.txt", "content": "first\n" }),
                env,
            )
            .await
            .0
        })
    };
    state.first_started.notified().await;
    let second = {
        let (tool, env) = (Arc::clone(&tool), Arc::clone(&env));
        tokio::spawn(async move {
            run(
                &tool,
                json!({ "path": "real/new.txt", "content": "second\n" }),
                env,
            )
            .await
            .0
        })
    };
    tokio::time::sleep(PROCEED_WINDOW).await;
    assert!(!state.second_started.load(Ordering::SeqCst));
    state.finish_first.notify_one();
    first.await.unwrap().unwrap();
    second.await.unwrap().unwrap();
    assert_eq!(read_file(env.as_ref(), "real/new.txt").await, "second\n");
}

#[tokio::test]
async fn does_not_serialize_the_same_path_on_different_file_systems() {
    let dir = temp_dir();
    let (local, local_state) = blocking_write_env(native(&dir));
    let (mut other, other_state) = blocking_write_env(native(&dir));
    other.id = Some("other".to_owned());
    let local: Arc<dyn ExecutionEnv> = Arc::new(local);
    let other: Arc<dyn ExecutionEnv> = Arc::new(other);
    let tool = create_write_tool();
    let blocked = {
        let (tool, local) = (Arc::clone(&tool), Arc::clone(&local));
        tokio::spawn(async move {
            run(
                &tool,
                json!({ "path": "file.txt", "content": "first\n" }),
                local,
            )
            .await
            .0
        })
    };
    local_state.first_started.notified().await;
    run(
        &tool,
        json!({ "path": "file.txt", "content": "second\n" }),
        other,
    )
    .await
    .0
    .unwrap();
    assert!(other_state.second_started.load(Ordering::SeqCst));
    local_state.finish_first.notify_one();
    blocked.await.unwrap().unwrap();
}

#[tokio::test]
async fn edits_regular_files_through_symlinks() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    write_file(env.as_ref(), "target.txt", "before\n").await;
    std::os::unix::fs::symlink("target.txt", dir.path().join("link.txt")).unwrap();
    let (result, _) = run(
        &create_edit_tool(),
        json!({ "path": "link.txt", "edits": [{ "oldText": "before", "newText": "after" }] }),
        Arc::clone(&env) as Arc<dyn ExecutionEnv>,
    )
    .await;
    result.unwrap();
    assert_eq!(read_file(env.as_ref(), "target.txt").await, "after\n");
}

#[tokio::test]
async fn preserves_bom_and_crlf_line_endings() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    write_file(env.as_ref(), "edit.txt", "\u{FEFF}one\r\ntwo\r\n").await;
    let (result, _) = run(
        &create_edit_tool(),
        json!({ "path": "edit.txt", "edits": [{ "oldText": "two", "newText": "TWO" }] }),
        Arc::clone(&env) as Arc<dyn ExecutionEnv>,
    )
    .await;
    result.unwrap();
    assert_eq!(
        read_file(env.as_ref(), "edit.txt").await,
        "\u{FEFF}one\r\nTWO\r\n"
    );
}
