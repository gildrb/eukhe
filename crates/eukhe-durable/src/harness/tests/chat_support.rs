//! Port of `test/chat-support.ts`: a faux-model chat setup that survives a
//! close/reopen, and helpers over its conversations.

use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use eukhe_chord::context::Context;
use eukhe_pi_ai::models::Models;
use eukhe_pi_ai::providers::faux::{
    faux_provider, FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{AssistantContentBlock, Message, UserContent, UserContentBlock};
use futures::FutureExt;
use tokio::sync::watch;

use super::support::{context, create_models, create_registry};
use crate::env::ExecutionEnv;
use crate::harness::registry::Registry;
use crate::harness::types::{
    AgentChange, Clock, EnvFactory, FieldChange, HarnessOptions, LiveSettings, ModelRef,
    ToolRegistration,
};
use crate::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use crate::session::{SessionError, SessionResult};
use crate::types::{EntryRecord, Storage};

/// Models and registry that survive a close/reopen, like a host process's
/// own objects.
pub(crate) struct ChatSetup {
    pub(crate) faux: FauxProviderHandle,
    pub(crate) models: Models,
    pub(crate) registry: Registry,
    pub(crate) reports: Arc<Mutex<Vec<SessionError>>>,
    /// Live Harness settings; tests edit them between decisions.
    pub(crate) settings: Arc<LiveSettings>,
    now: Arc<Mutex<Clock>>,
}

#[expect(
    clippy::cast_precision_loss,
    reason = "`Date.now()` is a whole number of milliseconds, far below 2^53"
)]
fn date_now() -> f64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0.0, |elapsed| elapsed.as_millis() as f64)
}

impl ChatSetup {
    /// Replace the Harness clock (TS `setup.now = ...`).
    pub(crate) fn set_now(&self, now: impl Fn() -> f64 + Send + Sync + 'static) {
        *self.now.lock().unwrap_or_else(PoisonError::into_inner) = Arc::new(now);
    }

    /// The current Harness clock reading.
    pub(crate) fn now(&self) -> f64 {
        let now = Arc::clone(&self.now.lock().unwrap_or_else(PoisonError::into_inner));
        now()
    }

    /// The same setup over other models (TS `{ ...setup, models }`): faux,
    /// registry, reports, settings, and clock stay shared.
    pub(crate) fn with_models(&self, models: Models) -> ChatSetup {
        ChatSetup {
            faux: self.faux.clone(),
            models,
            registry: self.registry.clone(),
            reports: Arc::clone(&self.reports),
            settings: Arc::clone(&self.settings),
            now: Arc::clone(&self.now),
        }
    }

    /// Reports received so far.
    pub(crate) fn reports(&self) -> Vec<SessionError> {
        self.reports
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

pub(crate) fn chat_setup(options: RegisterFauxProviderOptions) -> ChatSetup {
    let faux = faux_provider(options);
    let models = create_models();
    models.set_provider(faux.provider.clone());
    ChatSetup {
        faux,
        models,
        registry: create_registry(),
        reports: Arc::new(Mutex::new(Vec::new())),
        settings: Arc::new(LiveSettings::default()),
        now: Arc::new(Mutex::new(Arc::new(date_now))),
    }
}

/// One environment for every conversation, or an `env` function.
pub(crate) enum ChatEnv {
    One(Arc<dyn ExecutionEnv>),
    Factory(EnvFactory),
}

/// A Harness and its root conversation.
pub(crate) struct OpenChat {
    pub(crate) harness: Harness,
    pub(crate) root: Conversation,
}

/// Open a Harness over `storage` and return its root, configured with the
/// faux model on first creation.
pub(crate) async fn open_chat(
    storage: Arc<dyn Storage>,
    setup: &ChatSetup,
    env: Option<ChatEnv>,
) -> SessionResult<OpenChat> {
    let mut options = HarnessOptions::new(setup.models.clone(), Arc::new(setup.registry.clone()));
    options.settings = Some(Arc::clone(&setup.settings) as _);
    options.env = env.map(|env| match env {
        ChatEnv::Factory(factory) => factory,
        ChatEnv::One(env) => Arc::new(move |_, _: &Context| {
            futures::future::ready(Ok(Some(Arc::clone(&env)))).boxed()
        }) as EnvFactory,
    });
    let clock = Arc::clone(&setup.now);
    options.now = Some(Arc::new(move || {
        let now = Arc::clone(&clock.lock().unwrap_or_else(PoisonError::into_inner));
        now()
    }));
    let reports = Arc::clone(&setup.reports);
    options.on_report = Some(Arc::new(move |error| {
        reports
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(error);
    }));
    let harness = Harness::open(storage, options, context()).await?;
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(ModelRef {
                        provider: "faux".to_owned(),
                        model_id: "faux-1".to_owned(),
                    }),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            context(),
        )
        .await?;
    Ok(OpenChat { harness, root })
}

/// Raw entries of a conversation, oldest first.
pub(crate) async fn all_entries(
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<Vec<EntryRecord>> {
    let page = conversation
        .entries(ConversationEntryQuery::default(), 1000, None, cx)
        .await?;
    Ok(page.items.into_iter().rev().collect())
}

/// Text of the first text content of a message.
pub(crate) fn text_of(message: Option<&Message>) -> Option<String> {
    match message? {
        Message::System(_) => None,
        Message::User(message) => match &message.content {
            UserContent::Text(text) => Some(text.clone()),
            UserContent::Blocks(blocks) => blocks.iter().find_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.clone()),
                UserContentBlock::Image(_) => None,
            }),
        },
        Message::Assistant(message) => message.content.iter().find_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.clone()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        }),
        Message::ToolResult(message) => message.content.iter().find_map(|block| match block {
            UserContentBlock::Text(text) => Some(text.text.clone()),
            UserContentBlock::Image(_) => None,
        }),
    }
}

/// Poll `check` in real time until it holds; for waits that span throttle
/// windows and timers. Default timeout in TS: 5000 ms.
pub(crate) async fn wait_for<F, Fut>(mut check: F, timeout_ms: u64)
where
    F: FnMut() -> Fut,
    Fut: Future<Output = bool>,
{
    let deadline = Instant::now() + Duration::from_millis(timeout_ms);
    while !check().await {
        assert!(Instant::now() <= deadline, "Condition was not reached");
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
}

/// Faux response that never answers; the run stays busy until its
/// generation is cancelled.
pub(crate) struct Unanswered {
    pub(crate) step: FauxResponseStep,
    reached: watch::Sender<bool>,
}

impl Unanswered {
    /// Resolves once the request was sent, after the generation's
    /// preparation and request commits.
    pub(crate) fn reached(&self) -> impl Future<Output = ()> + Send + 'static {
        let mut receiver = self.reached.subscribe();
        async move {
            // The sender lives in the step, which the faux provider keeps.
            let _ = receiver.wait_for(|reached| *reached).await;
        }
    }
}

pub(crate) fn unanswered() -> Unanswered {
    let reached = watch::channel(false).0;
    let reach = reached.clone();
    let step = FauxResponseStep::Factory(Arc::new(move |_, options, _, _| {
        reach.send_replace(true);
        let signal = options.and_then(|options| options.stream.request.signal.clone());
        async move {
            match signal {
                Some(signal) => Err(signal.cancelled().await),
                None => futures::future::pending().await,
            }
        }
        .boxed()
    }));
    Unanswered { step, reached }
}

/// The installed tools with these names, as `configure()` takes them.
pub(crate) fn tools_named(setup: &ChatSetup, names: &[&str]) -> Vec<Arc<ToolRegistration>> {
    use crate::harness::types::RegistryReader;
    let installed = setup.registry.snapshot().tools();
    names
        .iter()
        .map(|name| {
            let entry = installed
                .iter()
                .find(|entry| entry.tool.name == *name)
                .unwrap_or_else(|| panic!("Tool {name} is not installed"));
            Arc::clone(&entry.tool)
        })
        .collect()
}
