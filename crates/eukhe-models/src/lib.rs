//! Built-in model catalog subsystem for Eukhe. Fully local: nothing here
//! touches the network.
//!
//! Port of the TS catalog client's local layers:
//! - `packages/ai/src/model-catalog.ts` (strict model catalog schema) ->
//!   [`schema`]
//! - `packages/ai/src/model-compat-schema.ts` -> [`compat`]
//! - `packages/coding-agent/src/core/provider-model-catalog.ts` (transport
//!   pinning) -> [`pinning`]
//! - `packages/coding-agent/src/core/bundled-model-catalog.ts` -> [`bundled`]
//!
//! The packaged `models.bundled.json` (generated at build time from the
//! catalog repo's `models/catalog.v1.json`) is the client-facing catalog
//! contract; the compiled pi-ai table in `eukhe-pi-ai` (converted by
//! [`pi_ai_model`]) is the fallback. Everything the catalog can do is select
//! among transports the client compiled in; it can never introduce a
//! transport or change what a request sends.
//!
//! Ownership: eukhe-models depends on eukhe-pi-ai (compiled transport
//! templates) and eukhe-types (shared `Model`).

pub mod bundled;
pub mod compat;
pub mod pi_ai_model;
pub mod pinning;
pub mod prime_inference;
pub mod schema;
pub mod transports;

mod chain;

pub use chain::ModelCatalog;
pub use eukhe_types::ai::Model;
