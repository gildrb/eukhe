//! Per-file serialization of `edit` and `write`. Port of
//! `tools/file-mutation-queue.ts`.

use std::collections::BTreeMap;
use std::future::Future;
use std::sync::{Mutex, PoisonError};

use eukhe_chord::context::Context;
use futures::channel::oneshot;
use futures::future::{BoxFuture, FutureExt, Shared};

use crate::env::{ExecutionEnv, FileError, FileErrorCode};

/// Resolves when a call and every call queued before it on its key have
/// finished.
type Tail = Shared<BoxFuture<'static, ()>>;

/// Tail of the mutation chain of each file, keyed by file system id and
/// canonical path.
static QUEUES: Mutex<BTreeMap<String, Tail>> = Mutex::new(BTreeMap::new());

async fn mutation_key(
    env: &dyn ExecutionEnv,
    path: &str,
    cx: &Context,
) -> Result<String, FileError> {
    let absolute_path = env.absolute_path(path, cx).await?;
    Ok(format!(
        "{}\0{}",
        env.id(),
        canonical(env, &absolute_path, cx).await?
    ))
}

/// The canonical path; for a file that does not exist yet, its canonical
/// parent joined with its name, so a `write` that creates a file and a later
/// mutation of it share one key even under a symlinked directory.
fn canonical<'a>(
    env: &'a dyn ExecutionEnv,
    absolute_path: &'a str,
    cx: &'a Context,
) -> BoxFuture<'a, Result<String, FileError>> {
    Box::pin(async move {
        match env.canonical_path(absolute_path, cx).await {
            Ok(path) => return Ok(path),
            Err(error) => match error.code {
                FileErrorCode::NotSupported => return Ok(absolute_path.to_owned()),
                FileErrorCode::NotFound => {}
                FileErrorCode::Aborted
                | FileErrorCode::PermissionDenied
                | FileErrorCode::NotDirectory
                | FileErrorCode::IsDirectory
                | FileErrorCode::Invalid
                | FileErrorCode::Unknown => return Err(error),
            },
        }
        // The file system splits the path, so a name may contain characters
        // that are separators elsewhere.
        let parent = env.join_path(&[absolute_path, ".."], cx).await?;
        let Some(rest) = absolute_path.strip_prefix(parent.as_str()) else {
            return Ok(absolute_path.to_owned());
        };
        if rest.is_empty() {
            return Ok(absolute_path.to_owned());
        }
        let name = if parent.ends_with(['/', '\\']) {
            rest.to_owned()
        } else {
            skip_one_code_unit(rest)
        };
        let canonical_parent = canonical(env, &parent, cx).await?;
        env.join_path(&[&canonical_parent, &name], cx).await
    })
}

/// `text.slice(1)`: without its first UTF-16 code unit. Splitting a surrogate
/// pair leaves a lone low surrogate in JS, which a path written as UTF-8
/// carries as U+FFFD, as here.
fn skip_one_code_unit(text: &str) -> String {
    let mut chars = text.chars();
    match chars.next() {
        Some(first) if first.len_utf16() == 2 => format!("\u{FFFD}{}", chars.as_str()),
        _ => chars.as_str().to_owned(),
    }
}

/// The slot one call holds in its key's queue. Dropping it releases the slot,
/// also when the caller's future is dropped mid-call, and removes the key
/// once no later call queued behind it.
struct Slot {
    key: String,
    tail: Tail,
    /// Dropping the sender is the release.
    release: Option<oneshot::Sender<()>>,
}

impl Drop for Slot {
    fn drop(&mut self) {
        drop(self.release.take());
        let mut queues = QUEUES.lock().unwrap_or_else(PoisonError::into_inner);
        if queues
            .get(&self.key)
            .is_some_and(|tail| tail.ptr_eq(&self.tail))
        {
            queues.remove(&self.key);
        }
    }
}

/// Serialize `edit` and `write` mutations of one file within this process:
/// same file system id and canonical path, whichever environment object the
/// call got. Other files, and other file systems, never wait. Concurrent
/// calls on one file run in the order their keys resolve. Not a lock against
/// `bash` or other processes.
///
/// Resolving the key fails with the [`FileError`] of the environment; then
/// `f` does not run.
pub(crate) async fn with_file_mutation_queue<T, E, F, Fut>(
    env: &dyn ExecutionEnv,
    path: &str,
    f: F,
    cx: &Context,
) -> Result<T, E>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: From<FileError>,
{
    let key = mutation_key(env, path, cx).await?;
    // Take the slot without awaiting, so no other call can take it in between.
    let (previous, slot) = {
        let mut queues = QUEUES.lock().unwrap_or_else(PoisonError::into_inner);
        let previous = queues.get(&key).cloned();
        let (release, done) = oneshot::channel::<()>();
        let tail = {
            let previous = previous.clone();
            async move {
                if let Some(previous) = previous {
                    previous.await;
                }
                // `Err(Canceled)`: the slot's sender was dropped, i.e. released.
                let _released = done.await;
            }
            .boxed()
            .shared()
        };
        queues.insert(key.clone(), tail.clone());
        (
            previous,
            Slot {
                key,
                tail,
                release: Some(release),
            },
        )
    };
    if let Some(previous) = previous {
        previous.await;
    }
    let result = f().await;
    drop(slot);
    result
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use std::time::Duration;

    use eukhe_chord::context::BACKGROUND_CONTEXT;

    use super::*;
    use crate::env::{NativeExecutionEnv, NativeExecutionEnvOptions};

    fn create_env() -> (tempfile::TempDir, Arc<NativeExecutionEnv>) {
        let dir = tempfile::tempdir().unwrap();
        let env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
            cwd: dir.path().to_str().unwrap().to_owned(),
            ..Default::default()
        });
        (dir, Arc::new(env))
    }

    fn current_tail(key: &str) -> Option<Tail> {
        QUEUES
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(key)
            .cloned()
    }

    /// Wait until a call other than the one holding `held` took a slot on
    /// `key`: that call then awaits `held` with no await in between.
    async fn wait_until_queued_behind(key: &str, held: &Tail) {
        while current_tail(key).is_some_and(|tail| tail.ptr_eq(held)) {
            tokio::time::sleep(Duration::from_millis(1)).await;
        }
    }

    #[tokio::test]
    async fn keys_a_missing_file_whose_name_contains_a_backslash_like_the_created_file() {
        let (_dir, env) = create_env();
        let cx = &BACKGROUND_CONTEXT;
        let (created_tx, created_rx) = oneshot::channel::<()>();
        let (release_tx, release_rx) = oneshot::channel::<()>();
        let first = tokio::spawn({
            let env = Arc::clone(&env);
            async move {
                let env: &dyn ExecutionEnv = &*env;
                with_file_mutation_queue(
                    env,
                    "a\\b.txt",
                    move || async move {
                        env.write_file("a\\b.txt", b"first\n", &BACKGROUND_CONTEXT)
                            .await?;
                        created_tx.send(()).unwrap();
                        release_rx.await.unwrap();
                        Ok::<(), FileError>(())
                    },
                    &BACKGROUND_CONTEXT,
                )
                .await
            }
        });
        created_rx.await.unwrap();
        let key = mutation_key(&*env, "a\\b.txt", cx).await.unwrap();
        let held = current_tail(&key).unwrap();

        let entered = Arc::new(AtomicBool::new(false));
        let second = tokio::spawn({
            let env = Arc::clone(&env);
            let entered = Arc::clone(&entered);
            async move {
                with_file_mutation_queue(
                    &*env,
                    "a\\b.txt",
                    move || async move {
                        entered.store(true, Ordering::SeqCst);
                        Ok::<(), FileError>(())
                    },
                    &BACKGROUND_CONTEXT,
                )
                .await
            }
        });
        wait_until_queued_behind(&key, &held).await;
        assert!(!entered.load(Ordering::SeqCst));
        release_tx.send(()).unwrap();
        first.await.unwrap().unwrap();
        second.await.unwrap().unwrap();
        assert!(entered.load(Ordering::SeqCst));
        assert!(current_tail(&key).is_none());
    }

    /// Rust futures stop when dropped: a dropped call releases its slot, and
    /// later calls still wait for the calls before it.
    #[tokio::test]
    async fn a_dropped_call_releases_its_slot() {
        let (_dir, env) = create_env();
        let cx = &BACKGROUND_CONTEXT;
        let key = mutation_key(&*env, "dropped.txt", cx).await.unwrap();

        let (entered_tx, entered_rx) = oneshot::channel::<()>();
        let dropped = tokio::spawn({
            let env = Arc::clone(&env);
            async move {
                with_file_mutation_queue(
                    &*env,
                    "dropped.txt",
                    move || async move {
                        entered_tx.send(()).unwrap();
                        futures::future::pending::<Result<(), FileError>>().await
                    },
                    &BACKGROUND_CONTEXT,
                )
                .await
            }
        });
        entered_rx.await.unwrap();
        dropped.abort();
        assert!(dropped.await.unwrap_err().is_cancelled());
        assert!(current_tail(&key).is_none());

        let ran =
            with_file_mutation_queue(&*env, "dropped.txt", || async { Ok::<_, FileError>(7) }, cx)
                .await
                .unwrap();
        assert_eq!(ran, 7);
    }

    #[tokio::test]
    async fn runs_calls_on_one_file_in_order() {
        let (_dir, env) = create_env();
        let cx = &BACKGROUND_CONTEXT;
        let key = mutation_key(&*env, "ordered.txt", cx).await.unwrap();
        let order = Arc::new(Mutex::new(Vec::new()));
        let (release_tx, release_rx) = oneshot::channel::<()>();
        let (entered_tx, entered_rx) = oneshot::channel::<()>();
        let first = tokio::spawn({
            let (env, order) = (Arc::clone(&env), Arc::clone(&order));
            async move {
                with_file_mutation_queue(
                    &*env,
                    "ordered.txt",
                    move || async move {
                        entered_tx.send(()).unwrap();
                        release_rx.await.unwrap();
                        order.lock().unwrap_or_else(PoisonError::into_inner).push(0);
                        Ok::<(), FileError>(())
                    },
                    &BACKGROUND_CONTEXT,
                )
                .await
            }
        });
        entered_rx.await.unwrap();
        let mut later = Vec::new();
        for index in 1..=3 {
            let held = current_tail(&key).unwrap();
            later.push(tokio::spawn({
                let (env, order) = (Arc::clone(&env), Arc::clone(&order));
                async move {
                    with_file_mutation_queue(
                        &*env,
                        "ordered.txt",
                        move || async move {
                            order
                                .lock()
                                .unwrap_or_else(PoisonError::into_inner)
                                .push(index);
                            Ok::<(), FileError>(())
                        },
                        &BACKGROUND_CONTEXT,
                    )
                    .await
                }
            }));
            wait_until_queued_behind(&key, &held).await;
        }
        release_tx.send(()).unwrap();
        first.await.unwrap().unwrap();
        for handle in later {
            handle.await.unwrap().unwrap();
        }
        assert_eq!(
            *order.lock().unwrap_or_else(PoisonError::into_inner),
            vec![0, 1, 2, 3]
        );
        assert!(current_tail(&key).is_none());
    }
}
