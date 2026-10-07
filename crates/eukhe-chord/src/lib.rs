//! Rust port of `@earendil-works/chord` v1.0.4: invocation contexts, strict
//! JSON values, Delta (immutable JSON revisions and exact operation batches),
//! replicated state, services, and facet hosts.
//!
//! Not ported: the esbuild bundler and the `node:vm` facet bundle loader
//! (`bundler.ts`, `node/*`). Rust facets are compiled into the host.
//!
//! - [`context`]: cancellation and typed values ([`context::Context`]).
//! - [`json`]: persistent strict JSON with JS semantics
//!   ([`json::JsonValue`], [`json::to_json`] / [`json::from_json`]).
//! - [`delta`]: revision tracking with overlay drafts ([`delta::track`],
//!   [`delta::Draft`]), exact op batches ([`delta::Op`]), appliers
//!   ([`delta::apply_immutable`]), the wire codec, and [`delta::diff_revisions`].
//! - Replicated state: [`replicated_state`], [`replicated_state_from_source`].
//! - Services: [`define_service`], [`RemoteServiceProvider`],
//!   [`create_remote_service_binding`], the wire grammar
//!   ([`parse_service_call`], ...), and per-subscription codecs
//!   ([`create_service_state_encoder`]). Remote implementations are
//!   [`RemoteServiceObject`]s (method name + JSON args + context → JSON
//!   result); consumers hold [`ServiceHandle`]s.
//! - Facets: [`define_facet`], [`create_facet_host`], loaders.

pub mod context;
pub mod delta;
pub mod json;

mod api;
mod callback;
mod error;
mod facets;
mod services;
mod task;
#[cfg(test)]
mod tests;
mod types;

pub use api::{
    combine_facet_loaders, create_facet_host, create_static_facet_loader, define_local_service,
    define_service, FacetHost,
};
pub use callback::{AsyncCallback, Closer, Disposer, Outcome};
pub use delta::Draft;
pub use error::{AggregateError, BoxError, ChordError, ErrorReporter};
pub use facets::host::{
    define_facet, Facet, FacetEnvironment, FacetOptions, RemoteServiceSource,
    RemoteServiceSourceOpenOptions, ServiceImplementation, ServiceSpawner,
};
pub use facets::loader::{FacetLoader, LoadedFacets};
pub use json::{copy_json, is_json_value, JsonValue};
pub use services::consumer::{
    create_remote_service_binding, RemoteServiceBinding, RemoteServiceBindingOptions,
    RemoteServices, ServiceObserver,
};
pub use services::dispatch::{MethodFuture, RemoteServiceObject, ServiceMember, ServiceObject};
pub use services::errors::{
    is_remote_service_error_code, RemoteServiceError, RemoteServiceErrorCode,
    REMOTE_SERVICE_ERROR_CODES,
};
pub use services::handle::{AccessGuard, ServiceHandle, ServiceMemberHandle};
pub use services::provider::{
    create_remote_service_endpoint, ProviderSubscription, RemoteServiceEndpoint,
    RemoteServiceProvider, ServiceProviderDefinition, ServiceUpdatePublisher,
};
pub use services::state::{
    replicated_state, replicated_state_from_source, AttachedReplicatedState, MutableReplicatedState,
};
pub use services::state_codec::{
    create_service_state_decoder, create_service_state_encoder, ServiceStateDecoder,
    ServiceStateEncoder,
};
pub use services::state_internals::{ReplicatedStateRef, ReplicatedStateSnapshot};
pub use services::wire::{
    catalogue_json, create_service_catalogue_call, create_service_subscribe_call,
    create_service_unsubscribe_call, decode_service_control_call, parse_service_call,
    parse_service_catalogue, parse_service_provider_update, parse_service_subscription_snapshot,
    parse_wire_service_provider_update, parse_wire_service_subscription_snapshot,
    ServiceControlCall, ServiceOp, WireServiceInstanceSnapshot, WireServiceMemberSnapshot,
    WireServiceProviderUpdate, WireServiceSubscriptionSnapshot,
};
pub use types::{
    DeliveryKind, RemoteServiceTransport, ReplicatedState, ReplicatedStateDelivery,
    ReplicatedStateSource, ReplicatedStateSourceAttachment, ReplicatedStateSourceFrame,
    ReplicatedStateSourceOptions, ReplicatedStateSourceSnapshot, Service, ServiceCall,
    ServiceCatalogueEntry, ServiceInstanceAddress, ServiceInstanceSnapshot, ServiceMemberSnapshot,
    ServiceMode, ServiceProviderUpdate, ServiceSubscription, ServiceSubscriptionSnapshot,
    ServiceToken, ServiceUpdateListener, SourceFrameListener, StateListener,
};
