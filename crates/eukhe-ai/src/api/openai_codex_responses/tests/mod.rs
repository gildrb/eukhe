//! Port of `test/openai-codex-stream.test.ts`,
//! `test/openai-codex-cache-affinity-e2e.test.ts`, the Codex case of
//! `test/max-thinking.test.ts`, and `test/codex-websocket-cached-probe.ts`.

mod live;
mod socket_tests;
mod sse_tests;
mod support;
mod websocket_tests;
