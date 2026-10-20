//! docs/harness.md H4.4: a failed poll of a deferred job. The job can
//! still run, so a retryable failure polls the same job again and never
//! sends a new request (law `deferred_pays_once`).

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, FauxAssistantMessageOptions, FauxContentBlock,
    FauxDeferredOptions, FauxProviderState, RegisterFauxProviderOptions,
};
use eukhe_ai::types::DeferredRequest;
use eukhe_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_types::pi_ai::{
    AssistantMessageDiagnostic, AssistantMessageEvent, ErrorReason, StopReason,
};

use crate::harness::tests::chat_support::{chat_setup, open_chat, OpenChat};
use crate::harness::tests::support::context;
use crate::harness::types::{ConversationStreamOptions, InputSubmissionDraft, PartialRetryPolicy};
use crate::storage::MemoryStorage;
use crate::types::SubmissionStatus;

/// The observed failure: one failed fetch of a deferred job threw its
/// handle away and sent the request again, so the provider ran (and
/// billed) the work two times. Now the run polls the same job again: the
/// provider sees one request, and the poll after the failure gets the
/// answer.
#[tokio::test]
async fn a_retryable_failed_poll_polls_the_same_job_again() {
    let setup = chat_setup(RegisterFauxProviderOptions {
        deferred: Some(FauxDeferredOptions {
            pending_fetches: Some(0.0),
            poll_after_ms: Some(1.0),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    setup.faux.set_responses(vec![faux_assistant_message(
        vec![faux_text("deferred answer")],
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    // The first fetch fails as a server error would; the next ones are
    // the provider's.
    let mut provider = setup.faux.provider.clone();
    let fetch = provider.fetch_deferred.clone().expect("faux fetches");
    let failed = AtomicBool::new(false);
    provider.fetch_deferred = Some(Arc::new(move |model, handle, options| {
        if failed.swap(true, Ordering::SeqCst) {
            return fetch(model, handle, options);
        }
        let mut message = faux_assistant_message(
            Vec::<FauxContentBlock>::new(),
            FauxAssistantMessageOptions {
                stop_reason: Some(StopReason::Error),
                error_message: Some("503 Service Unavailable".to_owned()),
                ..FauxAssistantMessageOptions::default()
            },
        );
        let mut details = serde_json::Map::new();
        details.insert("status".to_owned(), 503.into());
        message.diagnostics = Some(vec![AssistantMessageDiagnostic {
            kind: "provider_stream_failure".to_owned(),
            timestamp: 0,
            error: None,
            details: Some(details),
        }]);
        let stream = AssistantMessageEventStream::new();
        stream.push(AssistantMessageEvent::Error {
            reason: ErrorReason::Error,
            error: message.clone(),
        });
        stream.end(Some(message));
        stream
    }));
    setup.models.set_provider(provider);
    setup.settings.update(|settings| {
        settings.stream = Some(ConversationStreamOptions {
            deferred: Some(DeferredRequest::Flag(true)),
            ..ConversationStreamOptions::default()
        });
        settings.retry = Some(PartialRetryPolicy {
            enabled: Some(true),
            max_retries: Some(1),
            base_delay_ms: Some(1.0),
            ..PartialRetryPolicy::default()
        });
    });
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    harness.resume().unwrap();
    let settled = root
        .submit(InputSubmissionDraft::new("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    harness.close(context()).await.unwrap();
    assert_eq!(
        (settled.state.status(), setup.faux.state()),
        (
            SubmissionStatus::Done,
            FauxProviderState {
                call_count: 1,
                deferred_fetch_count: 1,
                cancelled_deferred: Vec::new(),
            }
        )
    );
}
