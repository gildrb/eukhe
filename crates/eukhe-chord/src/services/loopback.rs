//! An in-process transport (port of `services/loopback.ts`).

use std::sync::Arc;

use futures::future::BoxFuture;
use futures::FutureExt;

use crate::context::Context;
use crate::error::ChordError;
use crate::types::{
    RemoteServiceTransport, ServiceCall, ServiceMode, ServiceSubscription, ServiceUpdateListener,
};

use super::dispatch::MethodFuture;
use super::provider::RemoteServiceProvider;

/// Connects a provider to a binding without changing remote service
/// semantics.
pub(crate) fn create_loopback_service_transport(
    provider: RemoteServiceProvider,
) -> Arc<dyn RemoteServiceTransport> {
    Arc::new(LoopbackTransport { provider })
}

struct LoopbackTransport {
    provider: RemoteServiceProvider,
}

impl RemoteServiceTransport for LoopbackTransport {
    fn invoke(&self, call: ServiceCall, context: &Context) -> MethodFuture {
        self.provider.invoke(call, context)
    }

    /// Subscribes synchronously, like the TS async arrow function's body.
    fn subscribe(
        &self,
        service_id: &str,
        mode: ServiceMode,
        listener: ServiceUpdateListener,
        _context: &Context,
    ) -> BoxFuture<'static, Result<Box<dyn ServiceSubscription>, ChordError>> {
        let subscription = self
            .provider
            .subscribe(service_id, mode, listener)
            .map(|subscription| Box::new(subscription) as Box<dyn ServiceSubscription>);
        futures::future::ready(subscription).boxed()
    }
}
