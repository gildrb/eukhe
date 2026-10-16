# AGENTS.md

Rules for work on eukhe (gildrb/eukhe, branch `main`). eukhe is a fork of
PrimeIntellect-ai/prime-agent (remote `upstream`).

## Repository

- Never set git identity (`user.name`/`user.email`, `-c`, or `GIT_AUTHOR_*`/
  `GIT_COMMITTER_*`) for commits in this repo. Commits use the ambient git config.
  If a commit fails for a missing identity, report it. Allowed: `*_DATE` variables
  (the golden corpus pins them) and throwaway repos created by tests.
- Never add `Co-authored-by` trailers.
- CI: `.github/workflows/ci.yml` on pushes and PRs; `eukhe-release.yml` on
  `eukhe-v*` tags writes `nix/release.json`.
- Prime Intellect stays as a third-party service: provider `prime-inference`,
  `PRIME_API_KEY`, `PRIME_TEAM_ID`, `PRIME_INFERENCE_*`, `api.primeintellect.ai`,
  the model catalog repo `PrimeIntellect-ai/prime-agent-catalog`. Everything that
  names the product is eukhe.

## Style and structure

- Crates are prefixed `eukhe-`. One owned area per crate. `eukhe-types` is the only
  shared vocabulary crate. Dependency direction is in the Crates table. Minimal public
  APIs, no god-modules.
- Private modules with an explicit public crate API. Internals are `pub(crate)`.
- Keep files under 2,000 lines, tests included. Split by responsibility; move related
  tests with extracted code.
- Name modules for what they own, not `utils` or `common`. Follow existing structure:
  `crates/eukhe-core/src/kernel/manager/` (`mod.rs` connects `execution.rs`,
  `requests.rs`, `teardown.rs`); `crates/eukhe-core/src/cron/store/` (`heartbeat.rs`,
  `jobs.rs`, `session_artifacts.rs`).
- Inline format args: `format!("{x}")`.
- Collapse `if` statements (clippy::collapsible_if).
- Method references over closures (clippy::redundant_closure_for_method_calls).
- Exhaustive `match`; no wildcard arms.
- New traits need doc comments: role and expected implementation behavior.
- No opaque positional `bool`/`Option` parameters. Use enums, named methods, or
  newtypes. If unavoidable, add an exact `/*param_name*/` comment.
- Native RPITIT trait methods with explicit `Send` bounds
  (`fn foo(&self) -> impl Future<Output = T> + Send;`), not `#[async_trait]`.
- No single-use helper methods.
- Instrument async work at the definition (`#[tracing::instrument(...)]`), not with
  `.instrument(...)` at call sites.

## Change hygiene

- One logical change per commit or PR.
- Dependency changes regenerate `Cargo.lock` in the same change. A new dependency
  needs a reason; `make deny` must stay clean.
- If a change forces edits across many crate internals, fix the boundary instead.

## Tests

- Whole-object equality over field-by-field checks.
- No tests for statically defined values. No negative tests for removed logic.
- Bug fixes need a regression test that fails without the fix.
- Wait for observable readiness, not fixed sleeps or retry loops. Give a reason at any
  disabled test. Use isolated ports and temp paths; restore shared state.
- Run tests with a clean environment. Inherited `EUKHE_*` variables make test daemons
  write into real `~/.eukhe`:
  `env -i HOME="$HOME" PATH="$PATH" USER="$USER" LANG="$LANG" cargo test --workspace`.

## Lints

- Zero warnings: fmt, clippy, and tests run at `-D warnings`. Enable a new lint family
  only with every current site fixed in the same change.
- Explain each `#[allow(...)]` next to it; keep it narrow. Advisory ignores in
  `deny.toml` need a reason and a review date.

## Critical path

First paint and every frame the user waits on never block on disk sync or
background bookkeeping.

- eukhe is fully local. The only outbound traffic is the model request to the
  provider the user configured and that provider's own auth (explicit login,
  cloud credential metadata), plus MCP servers the user configured, plus the
  Signal service, only while the user runs `eukhe gateway` (through the
  signal-cli the user installed). No telemetry, no catalog fetches, no uploads.
- Startup work never delays the first paint; slow bookkeeping runs on a
  background worker. Changes to the launch path keep the first frame unblocked.

## Merge gates

- `make check`: `cargo fmt --all --check`,
  `cargo clippy --workspace --all-targets -- -D warnings`, `cargo test --workspace`.
- `crates/eukhe-ai/src/models_generated.rs` (with `providers/*_models.rs` and
  `providers/data/*.json`, ported from pi-ai `models.generated.ts`) is the compiled
  fallback model catalog. `eukhe-models` adds the transport templates pi-ai lacks
  (`transports.rs` `SUPPLEMENTAL_TRANSPORTS`).
  `crates/eukhe-models/tests/fixtures/catalog.v1.json` refreshes with
  `scripts/generate-catalog-fixture.py`.

## Crates

|Crate|Purpose|Direct workspace dependencies|
|---|---|---|
|`eukhe-types`|Shared wire and domain types|none|
|`eukhe-build-info`|This build's identity (version + source commit, `build.rs`)|none|
|`eukhe-chord`|Contexts, cancellation, JSON (port of chord)|none|
|`eukhe-ai`|Providers, model catalog, streaming (port of pi-ai)|`eukhe-types`, `eukhe-chord`|
|`eukhe-durable`|Durable Harness, storage, conversations (port of pi-durable)|`eukhe-types`, `eukhe-chord`, `eukhe-ai`|
|`eukhe-models`|Bundled model catalog and transport pinning|`eukhe-types`, `eukhe-ai`|
|`eukhe-docs`|Documents: file tag, edit store, read projection, locked writes, hashline edits, grep, glob (port of omp edit)|none|
|`eukhe-core`|Durable session runtime, tools, skills, kernel, settings, chat memory|`eukhe-types`, `eukhe-chord`, `eukhe-ai`, `eukhe-durable`, `eukhe-models`, `eukhe-docs`|
|`eukhe-daemon`|Supervisor, workers, wire protocol|`eukhe-types`, `eukhe-build-info`, `eukhe-chord`, `eukhe-ai`, `eukhe-durable`, `eukhe-core`, `eukhe-docs`|
|`eukhe-tui`|Terminal UI, daemon-wire client|`eukhe-types`, `eukhe-build-info`|
|`eukhe-gateway`|Signal gateway (`eukhe gateway`): phone chat into the CLI session|`eukhe-types`, `eukhe-tui`|
|`eukhe-dashboard`|Web dashboard (`eukhe dashboard`): loopback HTTP + WebSocket bridge, embedded build-free web app (chat, memory tree), daemon-wire client|`eukhe-types`, `eukhe-tui`|
|`eukhe-cli`|`eukhe` binary, composition root|`eukhe-types`, `eukhe-build-info`, `eukhe-chord`, `eukhe-ai`, `eukhe-durable`, `eukhe-models`, `eukhe-core`, `eukhe-daemon`, `eukhe-tui`, `eukhe-gateway`, `eukhe-dashboard`|

- Dependencies point from higher crates to lower crates only. No cycles.
- `eukhe-tui` and `eukhe-dashboard` render from wire types and events; they do not link the session engine.
- `eukhe-cli` wires crates together; no business logic.

## Reliability

- The daemon is a supervisor. It spawns one worker process per active session.
  Workers restart with backoff. Sessions persist as durable storages under
  `~/.eukhe/sessions/<id>/`, so reattach works after a supervisor restart.
- A storage is an append-only commit log (`main.jsonl`, fsync on each commit).
  Legacy `<id>.jsonl` files are only read: open imports them once. Imports and
  forks build in a staging directory, fsync it, and rename it into place. A
  sweep removes staging directories untouched for 24 hours. A delete removes
  the storage and its legacy file.
- A worker whose supervisor stays unreachable for the lost-exit window
  (default 5 minutes) exits. Work in flight defers the exit by one more window
  at most; the session resumes on a later supervisor.
- The daemon hello reports `eukhe-build-info::DAEMON_BUILD_ID`. A client
  treats a daemon of another build as stale and replaces it on an idle start.
- No stubs, no `todo!()`, no swallowed errors.
