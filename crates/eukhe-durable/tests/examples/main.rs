//! Runs every example under `examples/` that needs no credentials, against
//! the faux provider where a model is involved, and asserts the outcomes the
//! TS examples (`test/examples/*.ts`) print.
//!
//! Each example exposes `run(out, args, openai_api_key)`; its `main` only
//! forwards stdout, the process arguments, and `OPENAI_API_KEY`.

mod agents;
mod basics;
mod coding;
mod harness;
