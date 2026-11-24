//! Where a session's desktop calls go: this machine's desktop, opened at
//! the session's first computer call and kept for its refs and frames, or
//! (in tests) a fake. Every call blocks, so it runs on a blocking thread;
//! a cancelled tool call cancels the desktop's running call.

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_desktop::{
    ActReport, Desktop, Error, FindQuery, FoundNode, Observation, ObserveOptions, SessionOptions,
    Step, Takeover, Window, WindowFilter, WindowSelector,
};
use tokio::sync::OnceCell;

#[cfg(test)]
use super::fake::FakeDesktop;

/// The desktop a session's computer tools reach.
#[derive(Clone, Default)]
pub enum DesktopPort {
    /// This machine's desktop.
    #[default]
    System,
    #[cfg(test)]
    Fake(Arc<FakeDesktop>),
}

/// An open desktop.
#[derive(Clone)]
pub(super) enum Screen {
    System(Arc<Desktop>),
    #[cfg(test)]
    Fake(Arc<FakeDesktop>),
}

/// Why a desktop call has no answer.
#[derive(Debug, thiserror::Error)]
pub(super) enum PortError {
    #[error(transparent)]
    Desktop(#[from] Error),
    #[error("the desktop call stopped: {0}")]
    Worker(#[from] tokio::task::JoinError),
}

/// A session's desktop, opened once at its first call; an open that
/// fails is tried again at the next call.
pub(super) struct Desktops {
    port: DesktopPort,
    /// The name other sessions see while this one holds input.
    holder: String,
    opened: OnceCell<Screen>,
}

impl Desktops {
    pub(super) fn new(port: DesktopPort, session_id: &str) -> Self {
        Self {
            port,
            holder: format!("eukhe session {session_id}"),
            opened: OnceCell::new(),
        }
    }

    async fn screen(&self) -> Result<&Screen, PortError> {
        self.opened
            .get_or_try_init(|| async {
                match &self.port {
                    DesktopPort::System => {
                        let holder = self.holder.clone();
                        let desktop = tokio::task::spawn_blocking(move || {
                            Desktop::open(SessionOptions {
                                input_lock: eukhe_desktop::default_input_lock()?,
                                holder,
                            })
                        })
                        .await??;
                        Ok(Screen::System(Arc::new(desktop)))
                    }
                    #[cfg(test)]
                    DesktopPort::Fake(fake) => Ok(Screen::Fake(Arc::clone(fake))),
                }
            })
            .await
    }

    /// Run `work` on the session's desktop on a blocking thread; when `cx`
    /// is cancelled first, the desktop's call is cancelled and its answer
    /// awaited.
    pub(super) async fn run<T, F>(&self, cx: &Context, work: F) -> Result<T, PortError>
    where
        T: Send + 'static,
        F: FnOnce(&Screen) -> Result<T, Error> + Send + 'static,
    {
        let screen = self.screen().await?;
        let owned = screen.clone();
        let mut job = tokio::task::spawn_blocking(move || work(&owned));
        let joined = match cx.abort_signal() {
            None => job.await,
            Some(signal) => tokio::select! {
                joined = &mut job => joined,
                _ = signal.cancelled() => {
                    screen.cancel();
                    job.await
                }
            },
        };
        Ok(joined??)
    }
}

impl Screen {
    pub(super) fn windows(&self, filter: WindowFilter) -> Result<Vec<Window>, Error> {
        match self {
            Self::System(desktop) => desktop.read().windows(filter),
            #[cfg(test)]
            Self::Fake(fake) => Ok(fake.windows(&filter)),
        }
    }

    pub(super) fn window(&self, selector: WindowSelector) -> Result<Window, Error> {
        match self {
            Self::System(desktop) => desktop.read().window(selector),
            #[cfg(test)]
            Self::Fake(fake) => fake.window(&selector),
        }
    }

    pub(super) fn observe(
        &self,
        selector: WindowSelector,
        options: ObserveOptions,
    ) -> Result<Observation, Error> {
        match self {
            Self::System(desktop) => desktop.read().observe(selector, options),
            #[cfg(test)]
            Self::Fake(fake) => fake.observe(&selector, options),
        }
    }

    pub(super) fn find(
        &self,
        selector: WindowSelector,
        query: FindQuery,
    ) -> Result<Vec<FoundNode>, Error> {
        match self {
            Self::System(desktop) => desktop.read().find(selector, query),
            #[cfg(test)]
            Self::Fake(fake) => fake.find(&selector),
        }
    }

    pub(super) fn act(
        &self,
        takeover: Takeover,
        selector: WindowSelector,
        steps: Vec<Step>,
    ) -> Result<ActReport, Error> {
        match self {
            Self::System(desktop) => desktop.exec(takeover).act(selector, steps),
            #[cfg(test)]
            Self::Fake(fake) => fake.act(&steps),
        }
    }

    fn cancel(&self) {
        match self {
            Self::System(desktop) => desktop.cancel(),
            #[cfg(test)]
            Self::Fake(fake) => fake.cancel(),
        }
    }
}
