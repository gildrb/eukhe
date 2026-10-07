//! TS `describe("Harness open")`.

use std::sync::Arc;

use super::{create_in, until, Log, Step};
use crate::errors::StorageError;
use crate::harness::tests::support::{context, create_models, create_registry};
use crate::harness::tests::task_support::{open_tasks, CountingReader, OpenTasksOptions};
use crate::harness::types::{HarnessOptions, RegistryReader};
use crate::harness::Harness;
use crate::session::tests::support::ControlledStorage;
use crate::tasks::{define_task, TaskDefinition};
use crate::types::{Storage, TaskId};

#[tokio::test]
async fn releases_its_registry_subscription_and_closes_the_session_when_open_fails() {
    let storage = ControlledStorage::new();
    let log = Log::default();
    let stuck = {
        let log = log.clone();
        define_task(
            TaskDefinition::<(), Step, (), ()>::new(
                "test.stuck",
                1,
                |()| Ok(Step::Run),
                |_task, _runtime, _cx| async { Ok(()) },
            )
            .phase("run", move |_task, _runtime, _cx| {
                let log = log.clone();
                async move {
                    log.push("run");
                    std::future::pending::<()>().await;
                    Ok(())
                }
            }),
        )
        .erase()
    };
    // Leave a running task behind so open has a reconciliation commit to fail.
    let first = open_tasks(
        Arc::clone(&storage) as Arc<dyn Storage>,
        std::slice::from_ref(&stuck),
        OpenTasksOptions::default(),
    )
    .await;
    create_in(&first.harness, &stuck).await;
    first.harness.resume().unwrap();
    until(|| log.len() == 1).await;

    let reader = Arc::new(CountingReader::new(create_registry()));
    storage.fail_next_commit(StorageError::Failed(Arc::new(std::io::Error::other(
        "disk full",
    ))));
    let Err(error) = Harness::open(
        Arc::clone(&storage) as Arc<dyn Storage>,
        HarnessOptions::new(
            create_models(),
            Arc::clone(&reader) as Arc<dyn RegistryReader>,
        ),
        context(),
    )
    .await
    else {
        panic!("open rejects");
    };
    assert!(error.to_string().contains("disk full"), "{error}");
    assert_eq!(reader.subscriptions(), 0);
    assert!(storage
        .task(TaskId::from_number(1), context())
        .await
        .is_err());
}
