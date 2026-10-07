//! Replicated state and services (port of `services/*`).

pub(crate) mod consumer;
pub(crate) mod dispatch;
pub(crate) mod errors;
pub(crate) mod handle;
pub(crate) mod instances;
pub(crate) mod loopback;
pub(crate) mod provider;
pub(crate) mod state;
pub(crate) mod state_codec;
pub(crate) mod state_internals;
pub(crate) mod wire;
