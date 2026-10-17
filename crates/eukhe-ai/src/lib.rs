//! Rust port of `@earendil-works/pi-ai` v1.0.4: the `Models` collection,
//! providers, wire APIs, transcript utilities, and authentication.
//!
//! The message and model types live in `eukhe_types::pi_ai`, the shared
//! vocabulary crate, so clients render them without linking this crate.

pub mod api;
pub mod auth;
pub mod capabilities;
pub mod env_api_keys;
pub mod model_catalog;
pub mod models;
pub mod models_generated;
pub mod models_store;
pub mod providers;
pub mod quirks;
pub mod session_resources;
pub mod typebox;
pub mod types;
pub mod utils;
