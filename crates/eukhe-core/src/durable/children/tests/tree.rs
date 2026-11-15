//! The agent tree over the children: a split spawns both children in their
//! own copies with their places, a split child's own first request states
//! the split rule and its place, a refused split names its first failing
//! check, a help leaf works read-only in the parent's directory, a failed
//! split child runs again once, and an abort of the turn cancels the
//! subtree.

use eukhe_ai::utils::text::get_system_message_text;
use eukhe_ai::utils::transcript::get_current_system_message;
use eukhe_types::daemon::agent_tree::{TreePlace, TreeRole};

use super::*;
use crate::child_workspace::WorkspaceMode;
use crate::durable::deps::{ParentLink, SessionRole};
use crate::durable::{open_session, SessionConfig, SessionStorage};

/// The places and workspaces the host was asked to spawn, by tree path:
/// a split's two children spawn concurrently, in either order.
fn spawned(host: &FakeHost) -> Vec<(Option<TreePlace>, WorkspaceMode)> {
    let mut spawns: Vec<_> = lock(&host.state)
        .spawns
        .iter()
        .map(|spawn| (spawn.tree.clone(), spawn.workspace))
        .collect();
    spawns.sort_by(|(left, _), (right, _)| {
        let path = |place: &Option<TreePlace>| place.as_ref().map(|place| place.path.clone());
        path(left).cmp(&path(right))
    });
    spawns
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_split_spawns_both_children_in_their_own_copies() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    split_children(&opened, &setup, &["src/a"], &["src/b", "docs"]).await;
    let place = |role, scope: &[&str], path: &str| TreePlace {
        role,
        scope: scope.iter().map(|path| (*path).to_owned()).collect(),
        path: path.to_owned(),
        allowance: 7,
        deadline: None,
    };
    assert_eq!(
        spawned(&host),
        vec![
            (
                Some(place(TreeRole::Left, &["src/a"], "L")),
                WorkspaceMode::Isolated
            ),
            (
                Some(place(TreeRole::Right, &["src/b", "docs"], "R")),
                WorkspaceMode::Isolated
            ),
        ]
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

/// The system prompt of the first request of a child session opened at
/// `place`, as the daemon opens a spawned child (its place from the
/// spawn's metadata, a child host to split through).
async fn first_system_prompt(place: TreePlace, host: Arc<FakeHost>) -> String {
    let _env_lock = crate::kernel::bootstrap::KERNEL_ENV_LOCK.lock().await;
    let dir = tempfile::tempdir().expect("tempdir");
    let (agent_dir, cwd) = (dir.path().join("agent"), dir.path().join("project"));
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&cwd).expect("cwd");
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let sent: Arc<Mutex<Option<String>>> = Arc::default();
    let capture = Arc::clone(&sent);
    faux.set_responses(vec![FauxResponseStep::factory(move |context, _, _, _| {
        let system = get_current_system_message(context.messages()).expect("a system prompt");
        *lock(&capture) = Some(get_system_message_text(&system));
        Ok(faux_assistant_message(
            "done",
            FauxAssistantMessageOptions::default(),
        ))
    })]);
    let model = faux.get_model();
    let mut config = SessionConfig::new(
        &agent_dir,
        &cwd,
        "0192a000-0000-7000-8000-0000000000c1",
        SessionStorage::Memory,
    );
    config.models = Some(models);
    config.model = Some(
        ModelRef {
            provider: model.provider,
            model_id: model.id,
        }
        .into(),
    );
    config.role = SessionRole {
        rlm_depth: 1,
        rlm_max_depth: 3,
        parent: Some(ParentLink {
            session_id: PARENT_SESSION_ID.to_owned(),
            task_id: None,
            agent_name: None,
            spawned_by_request_id: None,
        }),
        worker: false,
        tree: Some(place),
    };
    config.children = Some(host as Arc<dyn RlmSubagentHost>);
    let session = open_session(config, cx()).await.expect("open");
    session
        .root()
        .submit(InputSubmissionDraft::new("do the left half"), cx())
        .await
        .expect("submitted");
    session.root().wait_for_idle(cx()).await.expect("idle");
    session.close(cx()).await.expect("close");
    let system = lock(&sent).take();
    system.expect("the request was captured")
}

/// The parent's task text says nothing of splitting: the child's own
/// system prompt carries the split rule, its scope and its room to split.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_split_childs_first_request_states_the_split_rule_and_its_scope() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    split_children(&opened, &setup, &["src/a", "docs"], &["src/b"]).await;
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
    let left = spawned(&host)
        .into_iter()
        .find_map(|(place, _)| place.filter(|place| place.role == TreeRole::Left));
    let system = first_system_prompt(left.expect("the left child's place"), host).await;
    assert!(
        system.contains("Split when two halves write disjoint files"),
        "{system}"
    );
    assert!(
        system.contains(
            "Agent tree: you are node L (`src/a`, `docs`; write only there). \
             You may split: 2 levels, 6 agents below."
        ),
        "{system}"
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_refused_split_names_its_first_failing_check_and_spawns_nothing() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let split = |left: &str, right: &str| {
        json!({
            "left": { "scope": [left], "task": "l" },
            "right": { "scope": [right], "task": "r" },
        })
    };
    let overlapping = request_turn(&opened, &setup, "rlm.split", split("src", "src/a")).await;
    let empty = request_turn(
        &opened,
        &setup,
        "rlm.split",
        json!({ "left": { "scope": [], "task": "l" }, "right": { "scope": ["b"], "task": "r" } }),
    )
    .await;
    let spawns_after_refusals = host.spawn_keys().len();
    split_children(&opened, &setup, &["a"], &["b"]).await;
    let again = request_turn(&opened, &setup, "rlm.split", split("c", "d")).await;
    assert_eq!(
        (overlapping, empty, spawns_after_refusals, again),
        (
            "error: own, left and right must split the node's scope exactly, each half non-empty"
                .to_owned(),
            "error: rlm.split left scope must be a non-empty list of paths".to_owned(),
            0,
            "error: the node has already split".to_owned(),
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_help_leaf_works_read_only_in_the_parents_directory() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    spawn_child(&opened, &setup).await;
    assert_eq!(
        spawned(&host),
        vec![(
            Some(TreePlace {
                role: TreeRole::Help,
                scope: Vec::new(),
                path: String::new(),
                allowance: 1,
                deadline: None,
            }),
            WorkspaceMode::Shared
        )]
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_failed_split_child_runs_again_once_then_reports_its_failure() {
    let setup = setup();
    let host = FakeHost::new();
    lock(&host.state).patch = Some(vec![None, Some(1), None]);
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let [left, _right] = split_children(&opened, &setup, &["a"], &["b"]).await;
    eventually(|| async { host.prompt_keys().len() == 2 }).await;
    let failed = || RlmChildRunState::Failed {
        failure: eukhe_types::input_origin::ChildFailure::Aborted,
        error: "boom".to_owned(),
    };
    host.settle(&left.session_id, failed(), None);
    let redo = format!("rlm:{}:redo", left.task_id);
    eventually(|| async { host.prompt_keys().contains(&redo) }).await;
    let running = row_of(&opened.harness, left.task_id).await.unwrap().status;
    host.settle(&left.session_id, RlmChildRunState::Running, None);
    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(&left.session_id, failed(), None);
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(left.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    let row = row_of(&opened.harness, left.task_id).await.unwrap();
    assert_eq!(
        (
            running,
            row.status,
            row.patch,
            host.prompt_keys()
                .iter()
                .filter(|key| **key == redo)
                .count(),
        ),
        (
            ChildStatus::Running,
            ChildStatus::Error,
            Some(vec![None, Some(1), None]),
            1
        )
    );
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_abort_of_the_turn_cancels_every_child_of_the_subtree() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let [left, right] = split_children(&opened, &setup, &["a"], &["b"]).await;
    eventually(|| async { host.prompt_keys().len() == 2 }).await;
    crate::durable::children::cancel_tree(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap();
    for row in [&left, &right] {
        opened
            .harness
            .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
            .await
            .unwrap();
    }
    let cancelled: Vec<String> = lock(&host.state)
        .cancels
        .iter()
        .map(|cancel| cancel.session_id.clone())
        .collect();
    let statuses = [
        row_of(&opened.harness, left.task_id).await.unwrap().status,
        row_of(&opened.harness, right.task_id).await.unwrap().status,
    ];
    assert_eq!(
        (cancelled, statuses),
        (
            vec![left.session_id.clone(), right.session_id.clone()],
            [ChildStatus::Cancelled, ChildStatus::Cancelled]
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}
