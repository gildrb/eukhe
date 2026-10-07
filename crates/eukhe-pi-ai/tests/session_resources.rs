//! `session-resources.ts` has no TS test; this pins the port's registry
//! semantics (one test: the registry is process-global).

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::session_resources::{
    cleanup_session_resources, register_session_resource_cleanup, SessionResourceCleanup,
};
use eukhe_pi_ai::utils::diagnostics::ErrorObject;

#[test]
fn runs_every_cleanup_aggregates_failures_and_unregisters() {
    let seen: Arc<Mutex<Vec<Option<String>>>> = Arc::default();
    let record = Arc::clone(&seen);
    let recording: SessionResourceCleanup = Arc::new(move |session_id| {
        record
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(session_id.map(str::to_owned));
        Ok(())
    });
    let failures = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&failures);
    let failing: SessionResourceCleanup = Arc::new(move |_| {
        counter.fetch_add(1, Ordering::SeqCst);
        Err(ErrorObject::new("cleanup failed").thrown())
    });

    let unregister_recording = register_session_resource_cleanup(Arc::clone(&recording));
    // The same cleanup registers once (TS `Set`).
    let _duplicate = register_session_resource_cleanup(Arc::clone(&recording));
    let unregister_failing = register_session_resource_cleanup(failing);

    let error = cleanup_session_resources(Some("s1")).expect_err("one cleanup fails");
    assert_eq!(error.to_string(), "Failed to cleanup session resources");
    assert_eq!(error.errors.len(), 1);
    assert_eq!(error.errors[0].to_string(), "cleanup failed");
    assert_eq!(
        *seen.lock().unwrap_or_else(PoisonError::into_inner),
        [Some("s1".to_owned())]
    );

    unregister_failing();
    cleanup_session_resources(None).expect("no failures left");
    assert_eq!(
        *seen.lock().unwrap_or_else(PoisonError::into_inner),
        [Some("s1".to_owned()), None]
    );
    assert_eq!(failures.load(Ordering::SeqCst), 1);

    unregister_recording();
    cleanup_session_resources(Some("s2")).expect("nothing registered");
    assert_eq!(seen.lock().unwrap_or_else(PoisonError::into_inner).len(), 2);
}
