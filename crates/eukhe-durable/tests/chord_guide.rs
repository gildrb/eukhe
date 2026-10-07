//! Port of `test/chord-guide.test.ts`: the code of
//! `docs/pico-v5-chord-usage.md`, compiled and run against a real Harness.
//! The guide's blocks are copied as written apart from Rust spelling and the
//! output sinks, which record instead of printing (each block takes its sink
//! as a parameter; TS shadows a module-level `console`).

use std::future::Future;
use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::delta::Op;
use eukhe_chord::json::{utf16_suffix, JsonObject, JsonValue};
use eukhe_chord::{
    create_facet_host, create_remote_service_binding, define_facet, define_service, BoxError,
    ChordError, Facet, FacetHost, FacetOptions, MethodFuture, Outcome, RemoteServiceBindingOptions,
    RemoteServiceTransport, Service, ServiceCall, ServiceMode, ServiceObject, ServiceObserver,
    ServiceSubscription, ServiceUpdateListener, StateListener,
};
use eukhe_durable::documents::{
    ConversationDocFamily, DocDefinition, DocFamilyDefinition, SessionDoc, TaskDoc,
};
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{Extension, HarnessOptions};
use eukhe_durable::harness::{Harness, RootOptions};
use eukhe_durable::session::{Session, SessionError, SessionResult, WatchListenerError};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tasks::{define_task, AnyTask, NextTaskState, TaskDefinition, TaskRuntime};
use eukhe_durable::types::{
    CheckpointInfo, ConversationId, DocumentObserver, DocumentObserverExt, LatestFork, TaskId,
    TaskOptions, TaskOutcome, TaskOwnership,
};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use futures::future::{BoxFuture, FutureExt};
use serde::{Deserialize, Serialize};
use serde_json::json;

/// What a block "prints": one array of logged values per call.
type Log = Arc<Mutex<Vec<JsonValue>>>;

fn log(sink: &Log, values: serde_json::Value) {
    sink.lock()
        .unwrap_or_else(PoisonError::into_inner)
        .push(JsonValue::from(values));
}

fn logged(sink: &Log) -> Vec<JsonValue> {
    sink.lock().unwrap_or_else(PoisonError::into_inner).clone()
}

fn plain(value: &JsonValue) -> serde_json::Value {
    serde_json::to_value(value).expect("JSON values serialize")
}

fn retirement_or<T: Serialize>(
    value: &JsonValue,
    field: impl Fn(&JsonValue) -> T,
) -> serde_json::Value {
    if value.is_null() {
        json!("retired")
    } else {
        json!(field(value))
    }
}

// ─── 1. A Session-wide canvas ────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct Point {
    x: f64,
    y: f64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct Stroke {
    color: String,
    points: Vec<Point>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct CanvasState {
    strokes: Vec<Stroke>,
}

static CANVAS_DOC: LazyLock<SessionDoc<CanvasState>> = LazyLock::new(|| {
    SessionDoc::define(DocDefinition {
        kind: "app.canvas",
        version: 1,
        initial: || CanvasState {
            strokes: Vec::new(),
        },
        migrate: None,
        // Store a complete base after at most 99 replayed deltas.
        checkpoint_when: Some(|_value: &JsonObject, _ops: &[Op], info: CheckpointInfo| {
            info.deltas_since_base >= 99
        }),
    })
    .expect("a valid definition")
});

/// The canvas service contract: a `state` member
/// (`ReplicatedState<CanvasState | null>`) and an `addStroke(stroke)` method.
enum CanvasService {}

static CANVAS: LazyLock<Service<CanvasService>> =
    LazyLock::new(|| define_service("app.canvas").expect("a valid service ID"));

async fn create_canvas_facet(session: Session, context: &Context) -> SessionResult<Arc<dyn Facet>> {
    // Creation is explicit; observation never writes.
    session
        .commit(
            |tx| async move {
                tx.doc(&*CANVAS_DOC, ()).await?;
                Ok(())
            },
            context,
        )
        .await?;
    let Some(state) = session.document_state(&*CANVAS_DOC, (), context).await? else {
        return Err(SessionError::error("canvas was retired during setup"));
    };
    Ok(define_facet(
        "app.canvas/session",
        move |env| -> Result<(), ChordError> {
            let owned = state.clone();
            env.own(move || owned.dispose())?;
            let session = session.clone();
            env.provide(
                &CANVAS,
                ServiceObject::new().state("state", &state).method(
                    "addStroke",
                    move |args: Vec<JsonValue>, context: Context| {
                        let session = session.clone();
                        let stroke = args.into_iter().next().unwrap_or_default();
                        async move {
                            session
                                .commit(
                                    |tx| async move {
                                        let draft = tx.doc(&*CANVAS_DOC, ()).await?;
                                        // Chord copies the assigned stroke by value.
                                        draft.child("strokes")?.push([stroke])?;
                                        Ok(())
                                    },
                                    &context,
                                )
                                .await?;
                            Ok::<_, SessionError>(None)
                        }
                    },
                ),
            )
        },
    ))
}

fn canvas_consumer(sink: Log) -> Arc<dyn Facet> {
    define_facet(
        "app.canvas/consumer",
        move |env| -> Result<(), ChordError> {
            // Declare now; access only after activation.
            let canvas = env.use_service(&CANVAS)?;
            let owner = env.clone();
            let sink = sink.clone();
            env.on_activate(move || -> Result<(), ChordError> {
                // subscribe delivers the current hydrated value, then updates.
                owner.own_disposer(canvas.member("state")?.subscribe(StateListener::new(
                    move |value: JsonValue, _context, delivery| {
                        let strokes = retirement_or(&value, |value| {
                            value["strokes"].as_array().map_or(0, <[JsonValue]>::len)
                        });
                        log(
                            &sink,
                            json!([delivery.kind.as_str(), delivery.sequence, strokes]),
                        );
                    },
                ))?)
            })
        },
    )
}

async fn run_canvas_example(session: Session, sink: Log) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    let provider = create_canvas_facet(session, context).await?;
    let host = create_facet_host(FacetOptions {
        facets: vec![provider, canvas_consumer(sink)],
        ..FacetOptions::default()
    })
    .await?;
    let stroke = JsonValue::from(json!({
        "color": "black",
        "points": [{ "x": 10, "y": 20 }, { "x": 30, "y": 40 }],
    }));
    let added = match host.services().use_service(&*CANVAS) {
        Ok(canvas) => canvas
            .invoke("addStroke", vec![stroke], context)
            .await
            .map(drop),
        Err(error) => Err(error),
    };
    // Unsubscribes; does not delete the canvas or close Session.
    host.dispose().await?;
    Ok(added?)
}

/// Stops a client's subscription and disposes its binding.
type Detach = Box<dyn FnOnce() -> BoxFuture<'static, Result<(), ChordError>> + Send>;

async fn connect_canvas(
    transport: Arc<dyn RemoteServiceTransport>,
    sink: Log,
    context: &Context,
) -> Result<Detach, ChordError> {
    let services = create_remote_service_binding(RemoteServiceBindingOptions::new(
        vec![CANVAS.id().to_owned()],
        transport,
    ))?;
    let canvas = services.use_service(&*CANVAS)?;
    let stop = canvas.member("state")?.subscribe(StateListener::new(
        move |value: JsonValue, _context, delivery| {
            let strokes = retirement_or(&value, |value| plain(&value["strokes"]));
            log(
                &sink,
                json!([delivery.kind.as_str(), delivery.sequence, strokes]),
            );
        },
    ))?;
    // Initial snapshot installed; not all future updates.
    if let Err(error) = services.ready(context).await {
        stop.dispose();
        services.dispose(&BACKGROUND_CONTEXT).await?;
        return Err(error);
    }
    Ok(Box::new(move || {
        async move {
            stop.dispose();
            services.dispose(&BACKGROUND_CONTEXT).await
        }
        .boxed()
    }))
}

/// The facet host as `shutdown` uses it (TS `FacetHost`). Implementations
/// dispose the host and its services.
trait HostLifetime: Sync {
    fn dispose(&self) -> BoxFuture<'_, Result<(), ChordError>>;
}

impl HostLifetime for FacetHost {
    fn dispose(&self) -> BoxFuture<'_, Result<(), ChordError>> {
        FacetHost::dispose(self).boxed()
    }
}

/// The Harness as `shutdown` uses it (TS `Harness`). Implementations close
/// the Harness.
trait HarnessLifetime: Sync {
    fn close(&self, context: &Context) -> BoxFuture<'static, SessionResult<()>>;
}

impl HarnessLifetime for Harness {
    fn close(&self, context: &Context) -> BoxFuture<'static, SessionResult<()>> {
        Harness::close(self, context)
    }
}

async fn shutdown(
    host: &dyn HostLifetime,
    detach_clients: Detach,
    harness: &dyn HarnessLifetime,
    context: &Context,
) -> Result<(), BoxError> {
    detach_clients().await?;
    host.dispose().await?;
    harness.close(context).await?;
    Ok(())
}

// ─── 2. Conversation-scoped diff reviews ─────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct ReviewInput {
    path: String,
    patch: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct ReviewComment {
    id: String,
    line: f64,
    text: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct ReviewState {
    path: String,
    patch: String,
    comments: Vec<ReviewComment>,
}

static REVIEW_DOC: LazyLock<ConversationDocFamily<ReviewState, ReviewInput>> =
    LazyLock::new(|| {
        ConversationDocFamily::define(
            DocFamilyDefinition {
                kind: "app.diff-review",
                version: 1,
                initial: |seed: ReviewInput| ReviewState {
                    path: seed.path,
                    patch: seed.patch,
                    comments: Vec::new(),
                },
                migrate: None,
                checkpoint_when: Some(|_value: &JsonObject, _ops: &[Op], info: CheckpointInfo| {
                    info.deltas_since_base >= 49
                }),
            },
            LatestFork::Current,
        )
        .expect("a valid definition")
    });

/// The diff review service contract: a `state` member
/// (`ReplicatedState<ReviewState | null>`), `identity()` returning
/// `{ conversationId, key }`, and `addComment(comment)`.
enum DiffReviewService {}

static DIFF_REVIEWS: LazyLock<Service<DiffReviewService>> =
    LazyLock::new(|| define_service("app.diff-reviews").expect("a valid service ID"));

#[derive(Clone)]
struct Review {
    key: String,
    seed: ReviewInput,
}

fn review_facet(
    session: Session,
    conversation_id: ConversationId,
    reviews: Vec<Review>,
    context: &Context,
) -> Arc<dyn Facet> {
    let context = context.clone();
    define_facet(
        "app.diff-reviews/session",
        move |env| -> Result<(), ChordError> {
            let instances = env.provide_many(&DIFF_REVIEWS)?;
            let (owner, session, reviews, context) = (
                env.clone(),
                session.clone(),
                reviews.clone(),
                context.clone(),
            );
            env.on_activate(move || {
                Outcome::pending(async move {
                    for review in reviews {
                        let (key, seed) = (review.key.clone(), review.seed.clone());
                        session
                            .commit(
                                move |tx| async move {
                                    tx.doc_member(&*REVIEW_DOC, (conversation_id, &key), &seed)
                                        .await?;
                                    Ok(())
                                },
                                &context,
                            )
                            .await?;
                        let Some(state) = session
                            .document_state(&*REVIEW_DOC, (conversation_id, &review.key), &context)
                            .await?
                        else {
                            return Err(BoxError::from("review was retired during setup"));
                        };
                        let retained = state.clone();
                        owner.own(move || retained.dispose())?;
                        let identity = JsonValue::from(json!({
                            "conversationId": conversation_id.get(),
                            "key": review.key,
                        }));
                        let session = session.clone();
                        // Chord instance keys route services; they are not numeric document incarnation IDs.
                        let instance_key = json!([conversation_id.get(), review.key]).to_string();
                        instances.spawn(
                            &instance_key,
                            ServiceObject::new()
                                .state("state", &state)
                                .method("identity", move |_args, _context| {
                                    let identity = identity.clone();
                                    async move { Ok::<_, BoxError>(Some(identity)) }
                                })
                                .method(
                                    "addComment",
                                    move |args: Vec<JsonValue>, context: Context| {
                                        let session = session.clone();
                                        let review = review.clone();
                                        let comment = args.into_iter().next().unwrap_or_default();
                                        async move {
                                            session
                                                .commit(
                                                    move |tx| async move {
                                                        let draft = tx
                                                            .doc_member(
                                                                &*REVIEW_DOC,
                                                                (conversation_id, &review.key),
                                                                &review.seed,
                                                            )
                                                            .await?;
                                                        // Chord copies the assigned comment by value.
                                                        draft.child("comments")?.push([comment])?;
                                                        Ok(())
                                                    },
                                                    &context,
                                                )
                                                .await?;
                                            Ok::<_, SessionError>(None)
                                        }
                                    },
                                ),
                        )?; // The facet owns spawned service lifetimes automatically.
                    }
                    Ok::<(), BoxError>(())
                })
            })
        },
    )
}

// ─── 3. Task-scoped output and a tool/task watch ─────────────────────────────

#[derive(Clone, Default)]
struct Frames {
    sent: Arc<Mutex<Vec<JsonValue>>>,
    rendered: Arc<Mutex<Vec<String>>>,
}

impl Frames {
    fn send_committed_frame(&self, value: Option<&JobOutput>, ops: &[Op]) {
        let ops: Vec<serde_json::Value> = ops.iter().map(|op| plain(&op.to_json())).collect();
        self.sent
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(JsonValue::from(json!({ "value": value, "ops": ops })));
    }

    fn render(&self, text: String) {
        self.rendered
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(text);
    }

    fn rendered(&self) -> Vec<String> {
        self.rendered
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct JobInput {
    command: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct JobOutput {
    stdout: String,
    chunks: f64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase")]
enum JobCheckpoint {
    #[serde(rename = "running")]
    Running,
}

static JOB_OUTPUT_DOC: LazyLock<TaskDoc<JobOutput>> = LazyLock::new(|| {
    TaskDoc::define(DocDefinition {
        kind: "app.job-output",
        version: 1,
        initial: || JobOutput {
            stdout: String::new(),
            chunks: 0.0,
        },
        migrate: None,
        checkpoint_when: Some(|_value: &JsonObject, _ops: &[Op], info: CheckpointInfo| {
            info.deltas_since_base >= 99
        }),
    })
    .expect("a valid definition")
});

async fn append_job_output(
    runtime: &TaskRuntime<JobInput, JobCheckpoint, (), ()>,
    chunk: String,
    context: &Context,
) -> SessionResult<()> {
    let task_id = runtime.task_id().erase();
    // Read process output outside this callback. The runtime gates the live task.
    runtime
        .commit(
            move |tx, _current| async move {
                let draft = tx.doc(&*JOB_OUTPUT_DOC, task_id).await?;
                let value = draft.value()?;
                let stdout = format!("{}{chunk}", value["stdout"].as_str().unwrap_or_default());
                draft.set("stdout", utf16_suffix(&stdout, 50_000))?;
                let chunks = value["chunks"].as_f64().unwrap_or_default() + 1.0;
                draft.set("chunks", JsonValue::from(json!(chunks)))?;
                Ok(None)
            },
            context,
        )
        .await
}

async fn observe_job(
    api: &dyn DocumentObserver,
    producer_task_id: TaskId,
    finished: impl Future<Output = ()>,
    sink: Log,
    frames: Frames,
    context: &Context,
) -> SessionResult<()> {
    let Some(watch) = api
        .watch_doc(&*JOB_OUTPUT_DOC, producer_task_id, context)
        .await?
    else {
        return Ok(());
    };
    let first = decode_job(watch.value().as_deref())?;
    log(
        &sink,
        json!([first.map_or_else(|| "retired".to_owned(), |value| value.stdout)]),
    );
    // Serialized callbacks never overlap.
    let started = watch.start(Arc::new(move |value, ops, _context| {
        let frames = frames.clone();
        async move {
            let value = decode_job(value.as_deref())
                .map_err(|error| Arc::new(error) as WatchListenerError)?;
            frames.send_committed_frame(value.as_ref(), &ops);
            frames.render(value.map_or_else(|| "retired".to_owned(), |value| value.stdout));
            Ok(())
        }
        .boxed()
    }));
    if started.is_ok() {
        // Caller-supplied observation lifetime; outside any commit.
        finished.await;
    }
    // Idempotent; prevents another callback from starting.
    watch.stop().await;
    started
}

fn decode_job(value: Option<&JsonObject>) -> SessionResult<Option<JobOutput>> {
    value
        .map(|value| eukhe_chord::json::from_json(&JsonValue::Object(Arc::new(value.clone()))))
        .transpose()
        .map_err(SessionError::from)
}

// ─── Runs ────────────────────────────────────────────────────────────────────

/// In-process transport to a host's service provider; a real client puts a
/// socket between the two.
struct InProcess {
    host: FacetHost,
}

impl RemoteServiceTransport for InProcess {
    fn invoke(&self, call: ServiceCall, context: &Context) -> MethodFuture {
        self.host.services().invoke(call, context)
    }

    fn subscribe(
        &self,
        service_id: &str,
        mode: ServiceMode,
        listener: ServiceUpdateListener,
        _context: &Context,
    ) -> BoxFuture<'static, Result<Box<dyn ServiceSubscription>, ChordError>> {
        let subscription = self
            .host
            .services()
            .subscribe(service_id, mode, listener)
            .map(|subscription| Box::new(subscription) as Box<dyn ServiceSubscription>);
        futures::future::ready(subscription).boxed()
    }
}

fn in_process(host: &FacetHost) -> Arc<dyn RemoteServiceTransport> {
    Arc::new(InProcess { host: host.clone() })
}

/// TS `session-support.ts` `context`.
fn context() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// Drain runnable work deterministically (TS `flush()`: macrotask turns).
async fn flush() {
    for _ in 0..64 {
        tokio::task::yield_now().await;
    }
}

/// Flush pending work until `check` holds (TS `eventually`).
async fn eventually<F, Fut>(mut check: F)
where
    F: FnMut() -> Fut,
    Fut: Future<Output = bool>,
{
    for _ in 0..200 {
        if check().await {
            return;
        }
        flush().await;
    }
    panic!("Condition was not reached");
}

/// Open a Harness whose registry holds `tasks` (TS `openTasks`).
async fn open_tasks(tasks: Vec<AnyTask>) -> Result<Harness, BoxError> {
    let registry = create_registry();
    if !tasks.is_empty() {
        registry.install(define_extension(Extension {
            name: "tasks".to_owned(),
            tasks,
            ..Extension::default()
        }))?;
    }
    let options = HarnessOptions::new(
        create_models(CreateModelsOptions::default()),
        Arc::new(registry),
    );
    Ok(Harness::open(Arc::new(MemoryStorage::new()), options, context()).await?)
}

/// Shutdown order the tracked host and Harness record.
type Order = Arc<Mutex<Vec<&'static str>>>;

fn record(order: &Order, step: &'static str) {
    order
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .push(step);
}

/// The TS `trackedHost` literal: disposal recorded around the real host's.
struct TrackedHost {
    host: FacetHost,
    order: Order,
}

impl HostLifetime for TrackedHost {
    fn dispose(&self) -> BoxFuture<'_, Result<(), ChordError>> {
        async move {
            record(&self.order, "dispose start");
            self.host.dispose().await?;
            record(&self.order, "dispose end");
            Ok(())
        }
        .boxed()
    }
}

/// The TS `trackedHarness` proxy: `close` recorded around the real one.
struct TrackedHarness {
    harness: Harness,
    order: Order,
}

impl HarnessLifetime for TrackedHarness {
    fn close(&self, context: &Context) -> BoxFuture<'static, SessionResult<()>> {
        let (closing, order) = (self.harness.close(context), Arc::clone(&self.order));
        record(&order, "close start");
        async move {
            closing.await?;
            record(&order, "close end");
            Ok(())
        }
        .boxed()
    }
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn runs_the_canvas_facet_host_a_remote_client_withdrawal_and_detach_before_harness_close(
) -> Result<(), BoxError> {
    let sink = Log::default();
    let harness = open_tasks(Vec::new()).await?;
    run_canvas_example((*harness).clone(), sink.clone()).await?;
    assert_eq!(
        logged(&sink),
        vec![
            JsonValue::from(json!(["hydrate", 0, 0])),
            JsonValue::from(json!(["update", 1, 1])),
        ]
    );
    let snapshot = harness.snapshot(&*CANVAS_DOC, (), context()).await?;
    assert_eq!(
        snapshot.and_then(|value| value
            .get("strokes")
            .and_then(|strokes| strokes.as_array().map(<[JsonValue]>::len))),
        Some(1)
    );

    // A worker installs the canvas facet again; a late remote client hydrates the stroke, then follows updates.
    let sink = Log::default();
    let host = create_facet_host(FacetOptions {
        facets: vec![create_canvas_facet((*harness).clone(), context()).await?],
        ..FacetOptions::default()
    })
    .await?;
    let detach = connect_canvas(in_process(&host), sink.clone(), context()).await?;
    host.services()
        .use_service(&*CANVAS)?
        .invoke(
            "addStroke",
            vec![JsonValue::from(json!({ "color": "red", "points": [] }))],
            context(),
        )
        .await?;
    eventually(|| {
        let done = logged(&sink).len() == 2;
        async move { done }
    })
    .await;
    let kinds: Vec<JsonValue> = logged(&sink)
        .iter()
        .map(|entry| {
            let strokes = entry[2].as_array().map_or(0, <[JsonValue]>::len);
            JsonValue::from(json!([plain(&entry[0]), strokes]))
        })
        .collect();
    assert_eq!(
        kinds,
        vec![
            JsonValue::from(json!(["hydrate", 1])),
            JsonValue::from(json!(["update", 2])),
        ]
    );
    // Record the shutdown order: clients detach and services withdraw while the Harness is still open.
    let order = Order::default();
    let tracked_harness = TrackedHarness {
        harness: harness.clone(),
        order: Arc::clone(&order),
    };
    let tracked_host = TrackedHost {
        host: host.clone(),
        order: Arc::clone(&order),
    };
    let detach_order = Arc::clone(&order);
    shutdown(
        &tracked_host,
        Box::new(move || {
            async move {
                record(&detach_order, "detach start");
                detach().await?;
                record(&detach_order, "detach end");
                Ok(())
            }
            .boxed()
        }),
        &tracked_harness,
        context(),
    )
    .await?;
    assert_eq!(
        *order.lock().unwrap_or_else(PoisonError::into_inner),
        vec![
            "detach start",
            "detach end",
            "dispose start",
            "dispose end",
            "close start",
            "close end",
        ]
    );
    let used = host
        .services()
        .use_service(&*CANVAS)
        .err()
        .map(|error| error.to_string());
    assert!(
        used.as_deref()
            .is_some_and(|error| error.contains("disposed")),
        "{used:?}"
    );
    let committed = harness
        .commit(|_tx| async { Ok(()) }, context())
        .await
        .err()
        .map(|error| error.to_string());
    assert!(
        committed
            .as_deref()
            .is_some_and(|error| error.contains("closed")),
        "{committed:?}"
    );
    Ok(())
}

#[tokio::test]
async fn runs_the_diff_reviews_with_a_keyed_consumer() -> Result<(), BoxError> {
    let harness = open_tasks(Vec::new()).await?;
    let root = harness.root(RootOptions::default(), context()).await?;
    let reviews = vec![Review {
        key: "review-7".to_owned(),
        seed: ReviewInput {
            path: "a.ts".to_owned(),
            patch: "-old\n+new".to_owned(),
        },
    }];
    let seen = Log::default();
    let observed = seen.clone();
    let consumer = define_facet(
        "app.diff-reviews/consumer",
        move |env| -> Result<(), ChordError> {
            let seen = observed.clone();
            env.observe(
                &DIFF_REVIEWS,
                ServiceObserver::new(move |review, call_context| {
                    let seen = seen.clone();
                    Outcome::pending(async move {
                        let identity = review.call("identity", vec![], &call_context)?.await?;
                        let key = identity.map(|identity| plain(&identity["key"]));
                        review.member("state")?.subscribe(StateListener::new(
                            move |value: JsonValue, _context, _delivery| {
                                let comments =
                                    value["comments"].as_array().map_or(-1, |comments| {
                                        i64::try_from(comments.len()).unwrap_or(i64::MAX)
                                    });
                                log(&seen, json!({ "key": key, "comments": comments }));
                            },
                        ))?;
                        review
                            .call(
                                "addComment",
                                vec![JsonValue::from(
                                    json!({ "id": "c1", "line": 1, "text": "why?" }),
                                )],
                                &call_context,
                            )?
                            .await?;
                        Ok::<(), ChordError>(())
                    })
                }),
            )
        },
    );
    let host = create_facet_host(FacetOptions {
        facets: vec![
            review_facet((*harness).clone(), root.id(), reviews, context()),
            consumer,
        ],
        ..FacetOptions::default()
    })
    .await?;
    eventually(|| {
        let done = logged(&seen)
            .iter()
            .any(|frame| frame["comments"].as_i64() == Some(1));
        async move { done }
    })
    .await;
    assert_eq!(
        logged(&seen),
        vec![
            JsonValue::from(json!({ "key": "review-7", "comments": 0 })),
            JsonValue::from(json!({ "key": "review-7", "comments": 1 })),
        ]
    );
    let snapshot = harness
        .snapshot(&*REVIEW_DOC, (root.id(), "review-7"), context())
        .await?
        .map(|value| plain(&JsonValue::Object(value)));
    assert_eq!(
        snapshot,
        Some(json!({
            "path": "a.ts",
            "patch": "-old\n+new",
            "comments": [{ "id": "c1", "line": 1, "text": "why?" }],
        }))
    );
    host.dispose().await?;
    harness.close(context()).await?;
    Ok(())
}

#[tokio::test]
async fn runs_the_job_output_watch_until_the_producer_retires_its_document() -> Result<(), BoxError>
{
    let sink = Log::default();
    let frames = Frames::default();
    let (gate, gate_open) = tokio::sync::watch::channel(false);
    let job = define_task(
        TaskDefinition::<JobInput, JobCheckpoint, (), ()>::new(
            "app.job",
            1,
            |_: &JobInput| Ok(JobCheckpoint::Running),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("running", move |task, runtime, ctx: Context| {
            let mut gate_open = gate_open.clone();
            async move {
                append_job_output(&runtime, format!("$ {}\n", task.input.command), &ctx).await?;
                gate_open
                    .wait_for(|open| *open)
                    .await
                    .map_err(SessionError::other)?;
                append_job_output(&runtime, "ok\n".to_owned(), &ctx).await?;
                runtime
                    .commit(
                        |_tx, _current| async {
                            Ok(Some(NextTaskState::Terminal {
                                outcome: TaskOutcome::Completed { result: () },
                            }))
                        },
                        &ctx,
                    )
                    .await
            }
        }),
    );
    let harness = open_tasks(vec![job.erase()]).await?;
    let root = harness.root(RootOptions::default(), context()).await?;
    let definition = job.as_definition_ref();
    let id = root
        .commit(
            move |tx| async move {
                tx.create_task(
                    definition,
                    JsonValue::from(json!({ "command": "make" })),
                    TaskOptions {
                        ownership: TaskOwnership::Conversation,
                        conversation_id: None,
                        background: None,
                    },
                )
                .await
            },
            context(),
        )
        .await?;
    harness.resume()?;
    eventually(|| {
        let snapshot = harness.snapshot(&*JOB_OUTPUT_DOC, id, context());
        async move {
            snapshot
                .await
                .ok()
                .flatten()
                .and_then(|value| value.get("chunks").and_then(JsonValue::as_f64))
                == Some(1.0)
        }
    })
    .await;
    let waiting = harness.wait_for_task(id, context());
    let finished = tokio::spawn(async move {
        // TS `.then(() => {})`: only settlement matters.
        let _settled = waiting.await;
    });
    let observing = tokio::spawn({
        let (harness, sink, frames) = (harness.clone(), sink.clone(), frames.clone());
        async move { observe_job(&harness, id, finished.map(drop), sink, frames, context()).await }
    });
    eventually(|| {
        let done = logged(&sink).len() == 1;
        async move { done }
    })
    .await;
    gate.send_replace(true);
    observing.await??;
    assert_eq!(logged(&sink), vec![JsonValue::from(json!(["$ make\n"]))]);
    // Stopped once the task finished; the retirement frame may or may not have been delivered before.
    assert_eq!(
        frames.rendered().into_iter().take(1).collect::<Vec<_>>(),
        vec!["$ make\nok\n".to_owned()]
    );
    assert!(harness
        .watch_doc(&*JOB_OUTPUT_DOC, id, context())
        .await?
        .is_none());
    harness.close(context()).await?;
    Ok(())
}
