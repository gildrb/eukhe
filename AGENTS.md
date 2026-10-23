# AGENTS.md

Rules for work on eukhe (gildrb/eukhe, branch `main`). Fork of
PrimeIntellect-ai/prime-agent (remote `upstream`).

## Repository

- Never set git identity (`user.name`/`user.email`, `-c`, `GIT_AUTHOR_*`/`GIT_COMMITTER_*`). Commits use the ambient git config. Missing identity: report it. Allowed: `*_DATE` variables (the golden corpus pins them), throwaway repos made by tests.
- No `Co-authored-by` trailers.
- CI runs only on this machine; GitHub runs no gate; no pull requests.
  - `make hooks` installs the prek hooks (`.pre-commit-config.yaml`). pre-commit: `make ci-fast`. pre-push: fmt, secrets, clippy, tests on the touched crates, `bend PROOF.bend`, on the pushed commits in the pushing worktree; no lock.
  - Never skip hooks (`--no-verify`).
  - `scripts/toolchain.env` pins the Bend and Lean releases.
  - Nightly, a systemd user timer runs `scripts/ci_nightly.sh run`: full gate (`make ci-local`) on origin/main. Green only: starts `eukhe-release.yml` for that commit, which releases `eukhe-v<X.Y.P>` (title `Eukhe v<X.Y.P>`, next patch of the `Cargo.toml` series `X.Y.0`) and writes `nix/release.json`. Red releases nothing; `make nightly-status` shows why.
  - `make catalog-pin` moves `scripts/release/catalog-pin.json` to the catalog repo's newest commit; review the diff, commit it.
- Prime Intellect stays only as a third-party service: provider `prime-inference`, `PRIME_API_KEY`, `PRIME_TEAM_ID`, `PRIME_INFERENCE_*`, `api.primeintellect.ai`, catalog repo `PrimeIntellect-ai/prime-agent-catalog`. Every product name is eukhe.

## Style and structure

- Crates are prefixed `eukhe-`; one owned area per crate. `eukhe-types` is the only shared vocabulary crate. Dependency direction: Crates table. Minimal public APIs; no god-modules.
- Private modules, explicit public crate API; internals `pub(crate)`.
- Rust and TypeScript files under 2,000 lines, tests included. Split by responsibility; move related tests with extracted code. Bend files (`LAWS.bend`, `proof/`, `bend/`) have no limit: a complete law set is long; one area's laws stay together.
- Name modules for what they own, never `utils`/`common`. Follow existing structure: `crates/eukhe-core/src/kernel/manager/` (`mod.rs` connects `execution.rs`, `requests.rs`, `teardown.rs`); `crates/eukhe-core/src/cron/store/` (`heartbeat.rs`, `jobs.rs`, `session_artifacts.rs`).
- Inline format args: `format!("{x}")`.
- Collapse `if` statements (clippy::collapsible_if).
- Method references over closures (clippy::redundant_closure_for_method_calls).
- Exhaustive `match`; no wildcard arms.
- No `unsafe` in eukhe code, tests included; every crate inherits `unsafe_code = "forbid"` (`[lints] workspace = true`). One exception: `crates/eukhe-bend/src/ffi.rs`, the C boundary to the compiled Bend core (crate lints = workspace's with `unsafe_code = "deny"`; `ffi.rs` carries the one `allow` with its reason).
- A core call on input eukhe encoded itself goes through `eukhe_bend::expect_core`, the one place eukhe panics on a compiled-core failure (only an inconsistent build); a caller already returning `Result` propagates `eukhe_bend::Error`.
- New traits need doc comments: role, expected implementation behavior.
- No opaque positional `bool`/`Option` parameters: use enums, named methods or newtypes; if unavoidable, an exact `/*param_name*/` comment.
- Native RPITIT trait methods with explicit `Send` bounds (`fn foo(&self) -> impl Future<Output = T> + Send;`), not `#[async_trait]`.
- No single-use helper methods.
- Instrument async work at the definition (`#[tracing::instrument(...)]`), not `.instrument(...)` at call sites.

## Change hygiene

- One logical change per commit or PR.
- Dependency changes regenerate `Cargo.lock` in the same change. A new dependency needs a reason; `make deny` stays clean.
- A change that forces edits across many crate internals: fix the boundary instead.

## Tests

- Whole-object equality over field-by-field checks.
- No tests for statically defined values. No negative tests for removed logic.
- Bug fix: a regression test that fails without the fix.
- Wait for observable readiness; no fixed sleeps or retry loops. Give a reason at any disabled test. Isolated ports and temp paths; restore shared state.
- Clean environment (inherited `EUKHE_*` makes test daemons write into real `~/.eukhe`): `env -i HOME="$HOME" PATH="$PATH" USER="$USER" LANG="$LANG" cargo test --workspace`.
- Laws are the first tests. Laws: root `LAWS.bend`, one section per area (`# ---- <area> ----` and its requirement table). Proofs (the Bend Bank layout): root `PROOF.bend` only imports; `proof/<area>/<law>.bend` holds the fill `def Laws.<law>` and the lemmas only that law uses; `proof/<area>/base.bend` the lemmas two or more laws of the area use; `proof/base.bend` those of two or more areas. A law's area is the `bend/` module its claim calls (`bend/ffi_<area>.bend` is `<area>`). A `proof/` file uses only laws filled in files it imports. `python3 scripts/split_proofs.py` places every lemma by these rules (`--check` fails on a misplaced one). Models: `bend/<area>.bend`. A rule with a Bend model runs as the compiled model: entry `bend/ffi_<area>.bend` (wire format of `bend/wire.bend`, `crates/eukhe-bend/WIRE.md`), called through `eukhe-bend` (`eukhe_bend::call` or a `Stepper`); no Rust copy of the rule, no bridge for it. `make bend-core` regenerates `bend/core.bend`, `crates/eukhe-bend/c/core.c`, `src/entries.rs` (never hand-edit; `make bend-core-check` fails when stale). Bridges (`bend/bridge_<area>.bend` plus a Rust bridge test) remain only for a model abstracting Rust code with no function to replace (a protocol, a concurrency schedule). No law outside `LAWS.bend`, no proof outside the `proof/` files `PROOF.bend` imports, no def in `PROOF.bend`: `scripts/check_laws_wired.py` fails on each.

## Lints

- Zero warnings: fmt, clippy, tests at `-D warnings`. A new lint family only with every current site fixed in the same change.
- Explain each `#[allow(...)]` next to it; keep it narrow. Advisory ignores in `deny.toml` need a reason and a review date.

## Critical path

First paint and every frame the user waits on never block on disk sync or background bookkeeping.

- eukhe is fully local. Only outbound traffic:
  - the model request to the user's configured provider, and its auth (explicit login, cloud credential metadata);
  - user-configured MCP servers;
  - the Signal service, only while `eukhe gateway` runs (through the user's signal-cli);
  - pinned model files from Hugging Face on `eukhe tiny-models download` (each checked against its pinned sha256 before install);
  - uv-managed Python and hash-locked kernel packages on `eukhe kernel install` (uv checks each hash; a session never downloads them);
  - read-only `ssh://` reads to `ssh.hosts` (through the user's `ssh` and `~/.ssh/config`);
  - npm and git traffic of `eukhe package install` and `eukhe package update`.
  
  No telemetry, catalog fetches, uploads, automatic model downloads, or automatic package installs or fetches.
- Startup work never delays the first paint; slow bookkeeping runs on a background worker. Launch-path changes keep the first frame unblocked.

## Merge gates

- `make check`: `cargo fmt --all --check`, `cargo clippy --workspace --all-targets -- -D warnings`, `cargo test --workspace`.
- Before a push: the pre-push hook passes; never bypass hooks. The full gate (`make ci-local`) runs nightly and gates the release.
- `crates/eukhe-ai/src/models_generated.rs` (with `providers/*_models.rs`, `providers/data/*.json`, ported from pi-ai `models.generated.ts`) is the compiled model catalog. Built-in catalog = its union with the bundled snapshot (`eukhe-models` `effective.rs`; laws: `LAWS.bend` section `catalog_union`). `eukhe-models` adds transport templates pi-ai lacks (`transports.rs` `SUPPLEMENTAL_TRANSPORTS`). `scripts/generate-catalog-fixture.py` refreshes `crates/eukhe-models/tests/fixtures/catalog.v1.json`.

## Crates

|Crate|Purpose|Direct workspace dependencies|
|---|---|---|
|`eukhe-types`|Shared wire and domain types|none|
|`eukhe-bend`|Compiled Bend core: every rule with a Bend model, compiled by Bend into `c/core.c` (generated, committed), called through one C entry (`c/shim.c`, `src/ffi.rs`: the only `unsafe`); wire format (`src/wire.rs`, `WIRE.md`); typed rule wrappers over shared vocabulary (`src/rules/`; may depend on `eukhe-types` only)|`eukhe-types`|
|`eukhe-theme`|Single theme source and resolver (TUI, HTML export): theme files, validation, name resolution, color math|none|
|`eukhe-build-info`|This build's identity (`build.rs`): version (the release, or `<series>-dev`) and source (commit, `.dirty.<hash>`, or `src.<hash>`)|none|
|`eukhe-chord`|Contexts, cancellation, JSON (port of chord)|none|
|`eukhe-ai`|Providers, model catalog, streaming (port of pi-ai)|`eukhe-types`, `eukhe-bend`, `eukhe-chord`|
|`eukhe-durable`|Durable Harness, storage, conversations (port of pi-durable)|`eukhe-types`, `eukhe-bend`, `eukhe-chord`, `eukhe-ai`|
|`eukhe-models`|Built-in model catalog (bundled snapshot ∪ compiled catalog), transport pinning|`eukhe-types`, `eukhe-bend`, `eukhe-ai`|
|`eukhe-docs`|Documents: file tag, edit store, read projection, locked writes, hashline edits, grep, glob (port of omp edit)|`eukhe-types`, `eukhe-bend`|
|`eukhe-shell`|In-process bash of the `bash` tool: script interpreter, own coreutils (`grep` on ripgrep's engine), per-step effect classes and approval gate|`eukhe-types`, `eukhe-bend`|
|`eukhe-tiny`|Local tiny models: pinned catalog, `eukhe tiny-models download`, shared worker per model and its election, worker client, role-based model selection|`eukhe-bend`, `eukhe-build-info`|
|`eukhe-tiny-onnx`|Tiny-model worker's ONNX engine (ONNX Runtime loaded at run time): text generation, Whisper speech to text, Kokoro text to speech|`eukhe-tiny`|
|`eukhe-core`|Durable session runtime, tools, skills, kernel, settings, chat memory, tiny-model roles (titles, local judgments)|`eukhe-types`, `eukhe-bend`, `eukhe-theme`, `eukhe-chord`, `eukhe-ai`, `eukhe-durable`, `eukhe-models`, `eukhe-docs`, `eukhe-shell`, `eukhe-tiny`|
|`eukhe-daemon`|Supervisor, workers, wire protocol|`eukhe-types`, `eukhe-bend`, `eukhe-theme`, `eukhe-build-info`, `eukhe-chord`, `eukhe-ai`, `eukhe-durable`, `eukhe-core`, `eukhe-docs`|
|`eukhe-tui`|Terminal UI, daemon-wire client|`eukhe-types`, `eukhe-bend`, `eukhe-theme`, `eukhe-build-info`|
|`eukhe-gateway`|Signal gateway (`eukhe gateway`): phone chat into the CLI session|`eukhe-types`, `eukhe-bend`, `eukhe-tui`|
|`eukhe-dashboard`|Web dashboard (`eukhe dashboard`): loopback HTTP + WebSocket bridge (pairing token, Host/Origin checks, protocol 3, allowed daemon commands), embedded web app (all of `web/` via `build.rs`; `web/` = committed `make dashboard-ui` output of Vite+ `vp build` from `ui/` (Preact, Radix, StyleX)), daemon-wire client|`eukhe-types`, `eukhe-build-info`, `eukhe-tui`|
|`eukhe-cli`|`eukhe` binary, composition root|`eukhe-types`, `eukhe-theme`, `eukhe-build-info`, `eukhe-chord`, `eukhe-ai`, `eukhe-durable`, `eukhe-models`, `eukhe-core`, `eukhe-daemon`, `eukhe-tui`, `eukhe-gateway`, `eukhe-dashboard`, `eukhe-tiny`, `eukhe-tiny-onnx`|

- Dependencies point from higher to lower crates only. No cycles.
- `eukhe-tui` and `eukhe-dashboard` render from wire types and events; they do not link the session engine.
- `eukhe-cli` wires crates together; no business logic.

## Reliability

- The daemon is a supervisor: one worker process per active session; workers restart with backoff. Sessions persist as durable storages in `~/.eukhe/sessions/<id>/`, so reattach works after a supervisor restart.
- A storage is an append-only commit log (`main.jsonl`, fsync per commit). Legacy `<id>.jsonl` files are read only; open imports them once. Imports and forks build in a locked staging directory, fsync it, and rename it into place only when nothing is there. A sweep (boot, every 5 minutes) removes staging directories untouched for 24 hours that no live build holds. A delete removes the storage and its legacy file.
- A worker whose supervisor stays unreachable for the lost-exit window (default 5 minutes) exits; work in flight defers the exit by at most one more window. Idle worker: closes its session. Worker with work: records it busy and exits without abort or close; the next supervisor resumes the run from storage. Work is one set for every idle decision: a run, a compaction, a queued input, an admitted run start, a background job, a user bash, an unsettled child or workflow run (a withdrawn input is not work). A worker with work records it busy every 5 minutes, so a long run still revives. An attached client relaunches a lost supervisor within 60 seconds.
- The daemon hello reports `eukhe-build-info::DAEMON_BUILD_ID`. Only an interactive start replaces a daemon, and only an idle daemon of a lower version (`eukhe-tui` `daemon_build`). A background client never replaces a daemon. A client never replaces a newer daemon or another build of the same version; it tells the user.
- No stubs, no `todo!()`, no swallowed errors.
