//! Execution environments of eukhe conversations: the local machine at the
//! conversation's working directory.

use std::collections::HashMap;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_durable::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::types::{EnvFactory, EnvTarget};
use futures::FutureExt;

/// An [`EnvFactory`] building a [`NativeExecutionEnv`] at the conversation's
/// agent `cwd`, else at `session_cwd`. One environment per directory is
/// kept for the session, so the commands it starts are tracked together.
#[must_use]
pub fn env_factory(session_cwd: &Path) -> EnvFactory {
    let session_cwd = session_cwd.to_string_lossy().into_owned();
    let envs: Arc<Mutex<HashMap<String, Arc<dyn ExecutionEnv>>>> = Arc::default();
    Arc::new(move |target: EnvTarget, _cx| {
        let cwd = target.cwd.unwrap_or_else(|| session_cwd.clone());
        let env = Arc::clone(
            envs.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .entry(cwd)
                .or_insert_with_key(|cwd| {
                    Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                        cwd: cwd.clone(),
                        ..NativeExecutionEnvOptions::default()
                    }))
                }),
        );
        futures::future::ready(Ok(Some(env))).boxed()
    })
}

#[cfg(test)]
mod tests {
    use eukhe_chord::context::BACKGROUND_CONTEXT;
    use eukhe_durable::harness::types::EnvTarget;
    use eukhe_durable::storage::MemoryStorage;
    use eukhe_durable::types::ROOT_CONVERSATION_ID;

    use super::*;

    fn target(cwd: Option<&str>) -> EnvTarget {
        EnvTarget {
            conversation_id: ROOT_CONVERSATION_ID,
            cwd: cwd.map(str::to_owned),
            read: Arc::new(eukhe_durable::session::create_session(
                Arc::new(MemoryStorage::new()),
                eukhe_durable::session::SessionOptions::default(),
            )),
        }
    }

    #[tokio::test]
    async fn env_runs_at_the_agent_cwd_else_the_session_cwd() {
        let factory = env_factory(Path::new("/session"));
        let session = factory(target(None), &BACKGROUND_CONTEXT)
            .await
            .expect("env")
            .expect("some env");
        assert_eq!(session.cwd(), "/session");
        let agent = factory(target(Some("/agent")), &BACKGROUND_CONTEXT)
            .await
            .expect("env")
            .expect("some env");
        assert_eq!(agent.cwd(), "/agent");
        let again = factory(target(Some("/agent")), &BACKGROUND_CONTEXT)
            .await
            .expect("env")
            .expect("some env");
        assert!(Arc::ptr_eq(&agent, &again));
    }
}
