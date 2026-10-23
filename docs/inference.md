# Harness laws: inference, local tiny models and reasoning depth

Shared rules (what a law secures, adversary, H1 to H6): [harness.md](harness.md).

### S6. The inference layer

Between harness and wire APIs; decides what a request may ask of a provider.

1. Quirks rulebook: family, model and host settings as data. Rule = layer, target id, directives with values. Compile rejects unknown directive, wrong value type, two rules of one layer+target giving one directive different values. Lookup: host > model > family. No rule → Unknown (no guess; wire API default applies). Explicit `model.compat` beats both. Rule order changes no answer.
2. One target per layer:
   - Family: the one family whose pattern matches the id (or id and name) and whose revision range, if any, holds. Revision (omp taxonomy): from first digit after the prefix in the bare name; a size (`8b`) is not one; none → 0. `qwen3.8-27b` → `qwen-3.8` (`>=3.8`); `qwen3-8b`, `qwq-32b` → `qwen` (`<3.8`).
   - Two families match → `QuirksError::FamilyOverlap`; none wins by id or order. Shipped-rulebook test rejects overlap on any compiled-catalog model. Out-of-catalog overlap → no family: family directives Unknown; error logged once per model id.
   - Model: model id.
   - Host: host naming the wire API (API one host speaks), else naming the provider id, else longest URL fragment in base URL (tie: smaller host id). One host; signals never combine: provider `openrouter` on a loopback base URL (local proxy) gets `openrouter`, not `loopback`. `openrouter` (provider match) adds Anthropic-format `cache_control` marks for `anthropic/` models; `openrouter-url` (custom provider, openrouter.ai base URL) gives other OpenRouter settings, no marks.
3. Forced tool call = tool + retry count. Each request ends with a soft prompt naming the tool. First request sets native forced choice only if supported and free (no prompt-cache invalidation); retries set it if supported. Support per request (`maps_forced_tool_choice`, wire API's predicate). Manual extended thinking: Anthropic and Claude on Bedrock reject forced choice → unsupported, no escalation to an unsent flag; a wire API given one there drops it and warns. No call → retry while retries remain, then `ForcedToolError::NotCalled` (names tool). Nothing forced → no change.
4. ≤ `strict_cap` strict schemas per request, highest `priority` first (default `0`; ties: earlier tool). Rest loose: client validates and repairs arguments. None dropped. Strict-required tool past cap → error.
5. Repetition guard, text and thinking deltas of every stream:
   - Chunk = one complete non-blank output line; lines over 4096 bytes (`MAX_CHUNK_BYTES`) split there on a character boundary, so no-newline loops (`abab…`) are cut.
   - Window = last `k` chunks (`retry.provider.streamRepeatLimit`, default 64); periodic with period `p` if each chunk after the first `p` equals the one `p` earlier. Period 1 to `k / 4` (at least 1) → abort: cycle seen 4 times; period 1 = one chunk `k` times; default cuts ≤ 16-line blocks seen 4 times. Otherwise not cut.
   - State: per `p`, count of consecutive chunks up to the newest equal to the one `p` earlier; periodic at ≥ `k - p`. Holds ≤ `k / 4` chunks, `k / 4` counters, one partial chunk per block, any stream length.
   - Cut → retryable `stream_repeating`; message gives period and last line; failure info records them (`RepeatedLines`, `repeated_lines`). Harness retries with a new request ending in an unlogged note (attempt, period, last line) (harness.md H4.7); a greedy model (`elpis-fast`, refuses temperature ≠ 0) loops on the same request.
   - Example: `qwen3.8-27b` thinking looped 1,359 lines on a 7-line cycle, no line twice in a row; a one-chunk-`k`-times check misses it; this guard cuts at line 77.
   - No text and no tool call = no answer: model error, retried with a note (harness.md H4.7). `length` stop, no answer → length note (harness.md H4.8). Noted retries (cut stream, no answer) spend a `MAX_NOTES` (8) note, not a retry, and go at once.
6. Compaction:
   - Threshold = limit (`contextWindow - reserveTokens`) − margin (`BackgroundMargin`: eukhe session 10% of window, `eukhe-core`; harness library default 32,768 tokens). Over threshold → background compaction; over limit → request blocks until done.
   - Ends mid-run → summary placed at next run boundary; wire `compaction_end` sent then with it, or as a skip if stale behind a later compaction. Queued summary survives run end (aborted run keeps queued writes). Summary write leaves queue unsettled, or a snapshot replaces events that could settle it → `compaction_end` unsuccessful. Summary queued (not placed, not stale) → no new background compaction.
   - Keeps newest `compaction.keepRecentTokens` (eukhe default 40,000; system entries count), ≤ half the threshold so history remains; small windows keep less.
   - Check uses a local input-token estimate. `compaction.providerTokenCount` (default off): ask provider `count_tokens` first (+1 request per generation); no counter or failure → warning, local estimate.
7. Provider operations beyond chat; eight capabilities: `count_tokens`, `list_models`, `embed`, `generate_image`, `tokenize`, `usage`, `web_search`, `compact`.
   - Directive named after the operation = endpoint dialect (`"list_models": "openai"`) or `false`; compile rejects a dialect lacking the operation.
   - Scope-`capabilities` hosts (`openai`, `google`, `llama-cpp`) set only capability directives and `prompt_progress`; wire lookup skips them (local `openai` provider keeps loopback settings).
   - `llama-cpp`: `"prompt_progress": true` → `openai-completions` sends `"return_progress": true`; stream emits `prompt_progress` (`total`, `cache`, `processed`, `time_ms`) per progress chunk before first token. `model.compat.supportsPromptProgress` wins.
   - Missing operation → typed `Unsupported { capability, provider }` before auth or request; never another provider or local estimate (callers request the estimate explicitly).
   - `eukhe provider caps [<provider>]`: support, no request. `eukhe provider models <provider>`: provider's model list.
8. Service tiers (`service_tiers`): entry = provider, wire API, tiers, optional family. Model honors `default` + tiers of entries matching provider, API, and family if named. Shipped:
   - `openrouter`/`openai-completions`: `flex`, `priority` (OpenRouter routes to tier endpoints, bills the serving tier).
   - `openai`/`openai-responses`, `openai-codex`/`openai-codex-responses`: `auto`, `scale`.
   - Families `gpt-priority`, `gpt-priority-explicit-cache`: + `flex`, `priority` on `openai`; + `priority` on `openai-codex` (ChatGPT backend: no flex).

   Readers (`quirks::service_tiers`): `/tier`, `/fast`, connection state (`availableServiceTiers`), image route, completions `service_tier`.
9. Thinking ladder (S10, ladder 0): `thinking_ladder` gives a family a `thinkingLevelMap`. Shipped:
   - `qwen-3.8`: `off` (wire `none`), `low`, `medium`, `xhigh`.
   - `qwen`: `off` (template toggle), `high` (omp's llama.cpp rules for Qwen templates).
   - `grok-4.3`: `off` as `none`; no `minimal`.
   - `grok-4.5`: no `off`, `minimal`.
   - `grok-4.6` (ids `grok-4.6`, `grok-4.7`): no `off`, `minimal`; + `xhigh`.

   Defaults (`thinking_defaults`) fill missing entries: `reasoning` = `off` to `high`; `plain` (no reasoning) = `off`. Stored xAI subscription moves xAI models to `openai-responses`; there, no `thinkingLevelMap` → model's rulebook ladder, else all levels null.
10. Tool calls read at stream end, any stop reason. Reply with tool calls runs them (vLLM, llama.cpp, Ollama stop with `stop` plus calls) (harness.md H4.1). `length` reply runs none (arguments may be cut); each gets `truncated`: repeat the call with complete arguments; write large content as a minimal version first, then extend it with edits (harness.md H4.1). Tool-call markup in text of a call-less reply (five families: Hermes and Qwen JSON, Qwen3-Coder XML, omp "qwen" form, Kimi section tokens, DeepSeek DSML; not in quoted code) → rebuilt if every leaked call parses and names an offered tool: markup leaves the text, stop reason becomes `toolUse`, calls run as tool calls; else retried with a leak note, ≤ `LEAK_NOTES` (2) in a row, then answers as text (harness.md H4.8.3; laws `run_calls_never_answer`, `rec_leak_rebuilt_is_calls`). Code: `eukhe-durable/src/harness/generation/leak.rs` `scan`, `generation.rs` `classify`, `generation/round.rs` `start_tool_round`.
11. Provider default model: `provider_defaults` (provider id → model id, `quirks::provider_default_model`). Read by startup model chain, fallback model template, onboarding after Prime Inference sign-in. Unlisted → no default.
12. Prices missing from catalog rows:
    - `service_tier_prices`: row = provider, wire API, tiers (response `service_tier`, else request's), multiplier, optional model id. Cost = base × multiplier of provider+API+id row, else provider+API row without id; none → base. Shipped: `openai` on `openai-responses`, `openai-completions`: `flex` 0.5; `priority`, `fast` (API's Fast-mode value) 2, `gpt-5.5` 2.5. `openai-codex`: `flex` 0.5; `priority` 2, `gpt-5.5` 2.5.
    - `cache_write_1h_prices`: row = regex on lowercased model id + input-rate multiplier; first match prices 1h cache writes; none → model's cache write rate. Shipped: `claude` 2 (Anthropic's price; Bedrock and gateways reselling Claude at Anthropic list rates charge it too).

    Read by `models::calculate_cost`, `models::apply_service_tier_pricing` (`quirks::cache_write_1h_multiplier`, `quirks::service_tier_multiplier`).
13. Every other model fact a wire API reads is rulebook data (S6.10); wire APIs never test the model id.
    - `adaptive_thinking` (`claude-adaptive`, `claude-adaptive-4-6`): `thinking.type: adaptive` + effort, Anthropic Messages and Bedrock (`models::adaptive_thinking`); explicit `compat.forceAdaptiveThinking` wins.
    - `thinking_block_binding` (`claude-adaptive`): Bedrock sends `thinking.block_binding` (not GovCloud).
    - `prompt_caching` (true: `claude-adaptive`, `claude-adaptive-4-6`, `claude-cached`; false: `claude-uncached`): Bedrock sends `cachePoint` blocks; unnamed models cache only with `AWS_BEDROCK_FORCE_CACHE=1`.
    - `explicit_cache_breakpoints` (`gpt-explicit-cache`, `gpt-priority-explicit-cache`): OpenAI Responses sends `prompt_cache_breakpoint`, `reasoning.context: "all_turns"`.
    - `google_thinking_level` (true: `gemini-3-plus`, `gemini-latest`, `gemma-4`; false: Gemini 2.5 families): Google sends `thinkingLevel`; unnamed → `thinkingBudget`.
    - `thinking_budgets` (`gemini-2.5-pro` 128, 2048, 8192, 32768; `gemini-2.5-flash` 128, 2048, 8192, 24576; `gemini-2.5-flash-lite` 512, 2048, 8192, 24576): Google per-level budget, Gemini API and Vertex. User `thinkingBudgets` wins, clamped to the rule's `minimal`..`high`. No rule → user budget, else `-1` (dynamic).
    - `thinking_defaults.budgets` (1024, 2048, 8192, 16384): budget when neither user nor rule gives one, every token-budget wire API.

    Family `except` regex excludes matches (families stay disjoint). Bedrock effort = model's thinking-level map (native `xhigh`: `xhigh: "xhigh"`), else Bedrock default.

Model `bend/infer.bend`. Laws: `LAWS.bend` section (S6), section `ladder` (S6.9). Proofs: `PROOF.bend` sections `infer`, `quirks`. Free inputs: rulebook, query, directive, model replies, provider support, tools, stream, context sizes.

| Law | Says |
| --- | --- |
| `quirk_unknown_rejected` | Unknown-directive rule → no compile (S6.1). |
| `quirk_clash_rejected` | Same layer/target/directive, different values → no compile (S6.1). |
| `quirk_unknown_when_none` | No rule applies → Unknown (S6.1). |
| `quirk_known_when_some` | Applying rule always answers (S6.1). |
| `quirk_highest_wins` | Compiled: highest applying layer answers (S6.1). |
| `quirk_order_free` | Compiled: swapping two rules changes no answer (S6.1). |
| `quirk_compile_order_free` | Swapping two rules keeps compile outcome (S6.1). |
| `quirk_ladder_explicit_first` | Explicit map beats rulebook ladder (S6.9). |
| `quirk_ladder_rule_second` | No explicit map → rulebook ladder (S6.9). |
| `quirk_ladder_default_last` | Neither → no entries; default ladder gives all (S6.9). |
| `quirk_ladder_offered_exact` | Reasoning model offers a level iff ladder gives a wire string, or no entry and default lists it (S6.9). |
| `quirk_ladder_plain_exact` | Non-reasoning offers exactly plain default (S6.9). |
| `quirk_ladder_shipped_is_s10` | Shipped defaults: offered = S10 ladder of chosen map; S10 laws hold (S6.9). |
| `force_bounded` | ≤ `1 + retries` attempts (S6.3). |
| `force_first_flag` | First attempt flags only if supported and free (S6.3). |
| `force_retry_flag` | Retries flag if supported (S6.3). |
| `force_reports` | Reports a call iff the model called the tool within its attempts (S6.3). |
| `strict_within_cap` | ≤ `cap` strict tools (S6.4). |
| `strict_keeps_every_tool` | Each tool strict or loose, multiplicity kept (S6.4). |
| `strict_by_priority` | Strict priorities ≥ loose ones (S6.4). |
| `guard_cuts_repeats` | One chunk `k` times in a row → cut (S6.5). |
| `guard_cuts_loops` | Periodic `k`-chunk window, period ≤ `k / 4` (at least 1) → cut (S6.5). |
| `guard_keeps_others` | No such window → not cut (S6.5). |
| `compact_starts_early` | Turn growth ≤ margin → compaction before any turn over limit (S6.6). |

Code:
- Rulebook: `eukhe-ai/src/quirks/mod.rs` (`compile`, `Rules::lookup`, `Rulebook::query`, `Rulebook::family`, `Rulebook::check_catalog`, `Quirks`, `ModelKey`, `ThinkingDefaults`), `quirks/revision.rs`, `quirks/tiers.rs` (`service_tiers`, `supports_service_tier`), `quirks/prices.rs` (`service_tier_multiplier`, `cache_write_1h_multiplier`), `quirks/rulebook.json` (shipped), `eukhe-ai/src/models/ladder.rs` (`thinking_level_map`, ladder functions).
- Resolvers (rulebook as detected input): `api/openai_completions/compat.rs` (`detect_compat`, `is_custom_qwen_template_model`), `api/anthropic_messages.rs` (`get_anthropic_compat`, `manual_thinking`), `api/openai_responses.rs` `get_compat`, `api/azure_openai_responses.rs`, `api/openai_codex_responses/request.rs`, `api/bedrock_converse_stream.rs` (strict default, `manual_thinking`), `api/google_shared/stream.rs` (validated function calling), `api/mistral_conversations/payload.rs`, `models/thinking.rs` `adaptive_thinking`.
- Strict, forced: `api/constrained_sampling.rs` (`strict_budget`, `StrictPlan`), `api/simple_options.rs` `maps_forced_tool_choice`; `eukhe-types/src/pi_ai/tool.rs` `Tool::priority`, `eukhe-types/src/pi_ai/settings.rs` `ToolChoice` (`Required`, `Tool(name)`; mapped in every wire API); `eukhe-durable/src/harness/generation/force.rs` (`ForceEscalation`, `ForceReply`, `Forcing`, `ForcedToolError`, `soft_prompt`), `ConversationStreamOptions::force_tool`.
- Guard: `eukhe-ai/src/utils/stream_repeat.rs` (`RepetitionGuard`, `MAX_CHUNK_BYTES`, `StreamRepeat`), `api/lazy.rs` `watched_lazy_stream`.
- Compaction: `eukhe-durable/src/harness/generation/decide.rs` `threshold_for`, `types/settings.rs` (`BackgroundMargin`, `ThresholdTokens`), `eukhe-durable/src/harness/generation.rs` (`threshold_compaction`, `provider_tokens`: provider count, logged fallback); `eukhe-core/src/settings/cvar/table.rs` `COMPACTION_PROVIDER_TOKEN_COUNT`, `eukhe-core/src/durable/settings.rs` (`WindowPercent(10.0)`, repeat limit); `eukhe-daemon/src/worker/durable_host/translator.rs` (`summary_write`, `end_lost_placements`, held ends at a snapshot).
- Capabilities: `eukhe-ai/src/capabilities/` (`Capability`, `Dialect::endpoint`, `capabilities_of`, one module per dialect), `models/capabilities.rs` (`Models` operations), `Directive::Endpoint`, `eukhe-cli/src/provider_command.rs`.

Tie (bridge tests, transcripts byte for byte):
- `harness::generation::infer_bridge::the_rust_quirks_rulebook_equals_the_bend_model` vs `bend/bridge_quirks.bend`: compile, lookup on generated rulebooks, each also with two rules swapped; directives = first of each value type in `Directive::ALL`; queries may name no family or host.
- `durable::effort_bridge::the_rust_reasoning_depth_equals_the_bend_model` (S10): default and rule ladders vs `bend/infer.bend` section 6.
- `the_rust_inference_units_equal_the_bend_model` vs `bend/bridge_infer.bend`: escalation; strict budget; guard on lines in random deltas (random chunks, 1-4 chunk cycles, same with one chunk changed, observed 7-line loop vs windows 27, 28, 32, 64); compaction threshold. Code compares strictly (`>`), so for whole token counts model threshold = limit − margin + 1.

Tests:
- `quirks::tests`: shipped rulebook compiles, no catalog overlap; `families_that_overlap_on_a_catalog_model_are_rejected`, `a_model_two_shipped_families_match_names_no_family`; errors, precedence, order, host/family queries, former hand-written checks; `the_shipped_qwen_families_split_at_the_revision_3_8`.
- `quirks::revision::tests`; `quirks::tiers::tests` (`the_table_keeps_every_answer_of_the_former_predicate`: every compiled-catalog model and tier vs the former hardcoded predicate, kept only in the test); `models::ladder::tests`.
- `openai_completions::tests::tool_choice` (`a_custom_qwen_3_8_model_sends_the_rulebook_ladder`), `openai_completions::tests::service_tier`, `openai_completions::tests::host_quirks` (`a_custom_provider_at_openrouter_ai_sends_no_cache_marks`, `the_openrouter_provider_at_a_loopback_url_keeps_the_openrouter_settings`).
- `constrained_sampling::tests` (`the_strict_budget_keeps_the_highest_priorities_and_the_earlier_of_equals`, `a_strict_plan_sends_tools_past_the_cap_loose_and_drops_none`), `generation::force::tests` (`manual_extended_thinking_has_no_native_forced_choice`), `anthropic_forced_tool_choice` `the_forced_choice_predicate_matches_the_wire`.
- `utils::stream_repeat::tests`: `a_loop_with_no_newline_is_cut_in_bounded_chunks`, `a_long_line_is_chunked_on_character_boundaries`, `the_observed_thinking_loop_is_cut_at_its_77th_line`, `the_observed_thinking_loop_fails_as_repeating_by_default`, `a_cycle_longer_than_a_quarter_of_the_window_is_not_cut`, `a_single_differing_line_restarts_the_window`, `the_guard_keeps_a_quarter_of_the_window`, `the_guard_cuts_where_the_model_does` (all streams of 3 chunk values ≤ 8 chunks, `k` ≤ 12).
- `generation::tests::threshold`; translator `a_summary_write_that_leaves_the_inbox_unsettled_ends_its_compaction`, `a_snapshot_ends_the_compactions_whose_end_it_may_have_replaced`; wire tests `cargo test -p eukhe-ai --test providers`.

Not modelled (tests tie them): model → targets map (S6.2); soft prompt, wire forms of forced choice; delta → chunk split.

#### S6 tool-call argument repair

Before validation (as omp), the client repairs arguments that are not strict JSON or spell a declared type differently.

1. Streaming preview closes incomplete text; final parse does not: `JSON.parse`; else escape raw control characters and invalid string escapes, retry; else relaxed dialect: single quotes, unquoted keys, comments, `True`/`False`/`None`, stray/trailing commas, `0x`/`0b` numbers, unquoted values (`src/main.rs`). Relaxed rejects truncation, trailing characters, non-finite numbers, unquoted values that can hide the next field.
2. Unparsable or non-object → `{ __parseError, __rawJson }` (error, first 512 characters); no text key survives, so half-formed calls never run. Result: `invalid_arguments` error with parse error and raw text.
3. JSON-string key (`"\"path\""`) → plain key, unless the plain key is present.
4. Alternate spellings → declared type: JSON string for object/array; single string for string array; number/boolean for string. String booleans/numbers → value, as before.
5. Each repair → `argument_repaired` warning on the result. Unknown key in a closed schema stays an error.
6. Unavailable tool → `tool_unavailable` naming ≤ 3 offered tools: small edit distance, nearest first; then names ending with the called name's last `_` or `__` segment.

Code: `eukhe-ai/src/utils/json_parse.rs` (`parse_json_with_repair`, `parse_tool_call_arguments`), `json_parse/relaxed.rs`, per-wire-API final parse (`anthropic_messages/events.rs`, `bedrock_converse_stream/events.rs`, `mistral_conversations/consume.rs`, `openai_completions/streaming.rs`, `openai_responses_shared/stream.rs`); `eukhe-durable/src/harness/tool/arguments.rs` (`repair_arguments`, `ArgumentError::NotJson`), `tool/result.rs` (`tool_unavailable_message`).
Tests: `utils::json_parse::tests`, `json_parse::relaxed::tests`, `tool::arguments::tests`, `tool::result::tests`.

#### S6 the built-in model catalog

Feeds `/model`, registry, daemon `get_model_catalog`; user `models.json` on top. Two local sources; no fetch:

1. Bundled `models.bundled.json` beside the executable; release builds it from `PrimeIntellect-ai/prime-agent-catalog` at the commit in `scripts/release/catalog-pin.json`, checking each sha256. Strict parse; entry transports must be compiled in (transport pinning).
2. Compiled: `eukhe-ai` pi-ai tables (`providers/data/*.json`) + Prime Inference entries.

Catalog = union; model = provider + id.

1. Every model of either source, exactly once; neither hides the other's.
2. In both: bundled gives api, `baseUrl`, data (`name`, `reasoning`, `input`, `cost`, `contextWindow`, `maxTokens`), its optional fields; compiled fills missing optional fields (`thinkingLevelMap`, `compat`, `featured`, `headers`) only on the same api.
3. In one: unchanged.
4. Order: bundled, then compiled-only in compiled order. Fields come only from each source's entry, so read order changes nothing.
5. Bundle missing or damaged → compiled catalog.

Example: Claude Haiku 5.5 (compiled, not pinned) is in `/model`. Move the pin to the catalog repo's newest commit:

```sh
make catalog-pin   # validates, records the commit and both sha256
git diff scripts/release/catalog-pin.json   # review, then commit
```

No code touches `~/.eukhe/models/provider-model-catalog.v1.json` (older builds' fetched catalog).

Laws: `LAWS.bend` section `catalog_union` (C1; model `bend/catalog_union.bend`; proofs `PROOF.bend` section `catalog_union`).
Code: `eukhe-models/src/effective.rs` (`effective_catalog`), `chain.rs` (`ModelCatalog::models`), `bundled.rs` (`load_bundled_models`), `pinning.rs`.
Bridge: `effective::bridge::the_rust_union_equals_the_bend_model` vs `bend/bridge_catalog_union.bend`, generated catalogs.
Tests: `chain::tests::a_bundle_without_a_compiled_model_keeps_it`; `eukhe-daemon` `tests/model_catalog_e2e.rs` (`a_bundle_without_a_compiled_model_still_lists_it`: pinned snapshot as bundle, Anthropic login → Claude Haiku 5.5 listed).

#### S6 models.json and the saved default model

One `models.json` loader for every view: registry (`eukhe model list`, `/model`, daemon `get_model_catalog`, onboarding, auxiliary model, memory compactor, RLM, usage) and session model collection.

1. Each `providers.<id>` loads alone; bad entry (wrong type, missing `baseUrl`/`apiKey`, invalid model) drops only that provider, diagnostic names `providers.<id>`.
2. Unreadable/unparsable file → one diagnostic, no custom models.
3. Diagnostics: `eukhe model list` (stderr), `get_model_catalog` `modelsJsonErrors`, each session's settings-error row at open.

Unpinned sessions start on the saved default (`defaultProvider`/`defaultModel`), never silently replaced:

1. Not in catalog or outside a set `enabledModels` → next startup default; one display-only `eukhe.default_model` row names saved default, reason, replacement.
2. Provider lacks credentials → typed `DefaultUnusable` + login hint; no substitute provider; session opens modelless; row names saved default and reason.
3. No replacement → session opens modelless with the row.
4. Memory compactor (no `memory.model`) fails with saved default and reason.

Laws: `default_honoured_or_reported`, `default_quiet_when_honoured`, `default_quiet_when_unset`, `default_unkeyed_never_moves` (model `bend/default_model.bend`; proofs `PROOF.bend` section `default_model`).
Code: `eukhe-core/src/models/custom.rs` (`ModelsConfig::load`), `models/registry.rs` (`compose`), `durable/models/compose.rs`, `models/resolver.rs` (`saved_default_miss`), `durable/models.rs` (`resolve_session_model`, `resolve_open_model`).
Bridge: `durable::models::default_bridge::the_rust_session_model_resolution_equals_the_bend_model` vs `bend/bridge_default_model.bend`.

### S9. Local tiny models

On-machine models per role (as omp): titles `tiny`, typed judgments `judge`, `translate`, text to speech `speech`, speech to text `dictation`.

Catalog `eukhe-tiny/src/catalog.rs` pins each file: Hugging Face repo, commit, size, sha256. Models: `lfm2.5-230m`, `lfm2.5-350m` (text, ONNX q4); `whisper-base`, `whisper-small` (speech to text); `kokoro` (Kokoro-82M, text to speech, misaki lexicon for phonemes).

Download: user only, `eukhe tiny-models download <id>` / `eukhe tiny-models download all`; `eukhe tiny-models list` shows installed, missing, incomplete. Nothing else downloads.

1. Files stage in `<agent dir>/models/tiny/.staging-<id>-<pid>`; sha256 computed while writing.
2. Wrong size or sha256 → stop, staging removed, earlier install untouched. Staging not removable → fails with its own error plus a warning naming the directory.
3. All correct → one rename to `<agent dir>/models/tiny/<id>`: complete or absent.

Worker: one process per model+backend, shared by all eukhe processes. Socket, bind lock, log in `<agent dir>/run/tiny/` (`<id>-onnx.sock`, `.bind.lock`, `.log`), made 0700 by worker and client even if present. Hidden `eukhe tiny-worker <id> --backend onnx --agent-dir <dir>`; agent dir from the starter's command line, never environment (daemon with `--agent-dir` and its worker agree).

1. Client connects, sends `ping`; worker answers launch tag `<build id>|onnx|<device>|<dtype>`.
2. Same tag → use it (joined).
3. Other tag → `shutdown`: worker removes socket, answers `bye`, refuses new connections/requests, finishes other processes' in-flight requests in full, exits; client starts a new one (replaced). New build or device/dtype change never hits a stale worker.
4. No live socket → client starts one (started), detached, own process group; it holds the bind lock only while checking and binding; a live worker answers → it exits, client uses the live one.
5. Exits after 15 idle minutes (`EUKHE_TINY_WORKER_IDLE_MS` for tests), socket removed first.
6. JSON-line requests: `load`; `chat` (messages, prefill, stop strings, max tokens); `transcribe` (audio, language); `speak` (text, voice, speed). One answer each, in order; client builds prompts, parses output. Worker dies mid-request → typed `Crashed` + log path. Lines ≤ 256 MiB each side: longer request → `bad_request`; longer answer → out of protocol; bytes discarded.

Engine `eukhe-tiny-onnx`: ONNX Runtime via `ort`, loaded at run time from `providers.tinyRuntimeLibrary`, else `ORT_DYLIB_PATH`, else `libonnxruntime.so` (nixpkgs `onnxruntime` ≥ 1.24). Nix wrapper and dev shell set `ORT_DYLIB_PATH` to nixpkgs (`--set-default`: user value wins). Build downloads nothing, links no runtime. CPU only. Own tokenizer (`tokenizer.rs`): byte-level BPE from `tokenizer.json` with added tokens, pre-tokenizer regex, ranked merges; other settings → load fails.

Roles (each names a chain):

1. Chain: `modelRoles.<role>` (if set), then `retry.fallbackChains.<role>`; explicit `[]` = primary only; unset → role's catalog models, then session provider model (text roles). `translate`: `lfm2.5-350m` before `lfm2.5-230m` (see Translation).
2. Available: local if installed; provider model if the session's usable model.
3. First available wins; none → `Unavailable`; never outside the chain.

Uses:
- Titles: first user message of a top-level session starts one in background (role `tiny`; `titles.generate: false` disables); turn never waits; failure → none; user names kept. `modelRoles.tiny` unset, no local model → one extra session-provider request. Scripted (faux-script test seam) sessions: no title.
- Judge: `local` provider exposes each text catalog model as classifier `local/<id>` on `classify`. Code-mode `models.classify()` without model (`null`/`undefined`) uses role `judge`: first chain model that is an available classifier (installed local, or provider classifier with configured auth); none → `Unavailable` naming role and chain.
- CLI: `eukhe translate <lang> <text>`, `eukhe say <text> [--out f.wav]`, `eukhe transcribe <file.wav>` → `translate`, `speech`, `dictation`.
- First paint never waits for a model load.

Translation: user turn `Translate from English to <Language>.\nEnglish: <text>`, assistant prefill `<Language>:`. One-line text stops at first line end. Empty reply, or same letters and digits as input (case-insensitive) → `TranslationError::Empty`/`TranslationError::Unchanged`, prints nothing (failing tiny models echo). Letterless input exempt.

Eval: 10 short English sentences (`hello`, `good morning, my friend`, ... `See you tomorrow.`) → German, French, Spanish, Portuguese; greedy; stop at first line end. Echoes = replies equal to input (of 40); chrF = mean (0 to 100) vs one reference:

| Variant | 230m echoes | 230m chrF | 350m echoes | 350m chrF |
| --- | --- | --- | --- | --- |
| system "translator" + user `Translate this text to <Language>:` (old) | 9 | 34 | 0 | 64 |
| instruction in the system prompt only | 24 | 12 | not run | not run |
| language code, not name | 27 | 13 | not run | not run |
| old + one example pair | 2 | 36 | 0 | 41 |
| old + prefill `<Language>: ` | 2 | 52 | 0 | 59 |
| old + one example pair + prefill `<Language>: ` | 1 | 20 | not run | not run |
| user `Translate this text to <Language>:` + prefill `<Language>:`, no system prompt | 16 | 26 | 2 | 53 |
| user `Translate from English to <Language>.\nEnglish: <text>` + prefill `<Language>:` (new) | 1 | 53 | 0 | 65 |
| new without "from English" (`Text:`) | 4 | 47 | 0 | 62 |
| new + the "translator" system prompt | 0 | 49 | 0 | 59 |
| new + one example pair | 0 | 59 | 0 | 59 |

- New recipe: best on `lfm2.5-350m`, near best on `lfm2.5-230m`.
- No example pair: needs one per target language.
- `lfm2.5-230m` is poor (`hello` → German `willkommen`), so built-in `translate` prefers installed `lfm2.5-350m`: `Hallo`, `Vielen Dank.`, `Où est la gare ?`, errors (`Gute Morgensinn, mein Freund`).
- Source English only; eval tested English only.

Dictation (into the TUI draft):

1. `stt.enabled` (default `false`) enables keys; read from the session at each take-starting press; `false` → key shows how to enable.
2. `app.stt.pushToTalk`, `app.stt.toggle`: no default key; bind in `binds.cfg` (S4.5), e.g. `bind f8 "action app.stt.toggle"`. Push-to-talk records while held (terminal resends on auto-repeat; gap > 300 ms, 800 ms after first press, = release). Toggle records until next press.
3. Recorder: first on `PATH` of `pw-record`, `parec`, `arecord` (macOS: `sox`, `ffmpeg`); raw 16 kHz mono 16-bit stdout → temp WAV. Failure → take fails with its stderr; no next program.
4. `dictation` role reads the file like `eukhe transcribe` (local only); text inserted at cursor; empty → "Dictation heard no speech".
5. Status `[REC] recording`, then `[STT] transcribing`. Esc mid-take stops recorder, removes file, shows "Dictation cancelled". Failure → error row.

No `cpal`: `alsa-sys` links `libasound` via `pkg-config` at build time; CI (`ubuntu-24.04`) lacks `libasound2-dev`; Nix would need `alsa-lib`, `pkg-config`. Recorder programs need nothing at build. Client input: no Bend model.
Code: `eukhe-tui/src/dictation.rs` (`Recorder`, `Transcriber`, `SubprocessRecorder`, `run_take`, `wav_bytes`), `session_ui/dictation.rs` (`handle_dictation_key`, `apply_dictation_update`), `status_line.rs`; `eukhe-cli/src/tiny_command.rs` (`RoleTranscriber`, `transcribe_file`).
Tests: `eukhe-tui` `dictation::tests` (fake recorder/transcriber: toggle, hold release, recorder failure, abort stops recorder and removes file; `/bin/sh` subprocess recorders: first found, stderr, no audio, no program), `keybindings::tests::dictation_actions_bind_only_through_binds_cfg`, `status_line::tests::the_dictation_phase_leads_the_line`, `tests/dictation_headless.rs` (TUI on mock daemon: toggle, push-to-talk, Esc, failure, `stt.enabled` off).

Model `bend/tiny.bend`. Laws: `LAWS.bend` section (S9). Proofs: `PROOF.bend` section `tiny`. Free inputs: chain, available set, needs of any processes and tags, worker exits, any order.

| Law | Says |
| --- | --- |
| `tiny_pick_in_chain` | Only available chain models (roles 3). |
| `tiny_pick_first` | First available chain model (roles 3). |
| `tiny_pick_unavailable` | None available → Unavailable (roles 3). |
| `tiny_every_need_served` | Each need: exactly one of started, joined, replaced (worker 1-4). |
| `tiny_worker_current` | Worker has the tag of the last need since the last exit (worker 3). |
| `tiny_same_tag_joins` | Need with the running tag joins (worker 2). |

Code: `eukhe-tiny/src/roles.rs` (`chain`, `pick`, `Candidate`, `FallbackChain`), `election.rs` (`ensure`, `request`, `probe`, `Launcher`, `Got`), `worker.rs` (`launch_tag`, `run_worker`, `bind`, `serve`), `client.rs` (`TinyClient`, `TinyError`), `catalog.rs` (`CATALOG`, `installed`, `install_state`), `download.rs` `download`, `tasks.rs` (prompts, output parsing); `eukhe-tiny-onnx/src/text.rs`, `whisper.rs`, `kokoro.rs`, `runtime.rs`, `tokenizer.rs`; `eukhe-core/src/tiny/` (settings, `resolve`, `title.rs`, `judge.rs` `judge_classifier`), `eukhe-core/src/durable/codemode.rs`; `eukhe-durable/src/codemode/models.rs` `ClassifierDefault`; `eukhe-daemon/src/worker/title.rs`; `eukhe-cli/src/tiny_command.rs`, `tiny_models_command.rs`.

Tie: `eukhe-tiny` `bridge::the_rust_pick_equals_the_bend_model` (`pick`, generated chains and available sets), `bridge::the_rust_election_equals_the_bend_model` (real election: `ensure`, real `serve`, in process, fake engine, generated needs and exits) vs `bend/bridge_tiny.bend`.

Tests:
- `client::tests`: real workers, temp run dir, started on the client's command line without agent dir variable, other `HOME`: started, joined, replaced, idle exit, crash, not installed, client's agent dir served.
- `worker::tests`: shutdown lets another client's in-flight request finish; existing run dir made 0700.
- `protocol::tests`: over-limit line skipped, next read.
- `download::tests` (mock HTTP): bad sha256, wrong size, broken transfer install nothing; partial install replaced only on success; unremovable staging keeps the download's own error.
- `eukhe-core` `tiny::tests` (role resolution; `translate` prefers `lfm2.5-350m`), `tiny::judge::tests` (`judge` model for model-less classify).
- `eukhe-tiny` `tasks::tests`: translate request; echo → `TranslationError::Unchanged`.
- `eukhe-durable` `codemode::tests::calls`: `models.classify(null, …)` asks the default classifier.
- `eukhe-daemon` `tests/session_title_e2e.rs`: supervisor on temp socket and agent dir, mock provider; first prompt titles; `titles.generate: false` titles nothing.
- `eukhe-tiny-onnx` `tokenizer::tests`: ids/text vs ids Hugging Face `tokenizers` once gave for the same files and texts; random text round-trips.
- Real-model (need models + runtime library, else print skip reason): `eukhe-tiny-onnx` `text::tests` (title from `lfm2.5-230m` and, if present, `lfm2.5-350m`, whose graph has a `num_logits_to_keep` input), `whisper::round_trip_tests` (Kokoro speaks, Whisper reads back), `tokenizer::tests` on model files; `eukhe-core` `tiny::smoke_tests` (title, `Models::classify` judgment on `local` via a real worker).

Not modelled: two processes starting a worker at once (bind lock orders; second uses the first's worker).

### S10. Reasoning depth

Thinking level = how much the model thinks before answering. Ladder order: `off`, `minimal`, `low`, `medium`, `high`, `xhigh`, `max`.

Ladder. All ladders and wire values are rulebook data (S6.9); code holds none. Offered levels keep ladder order:

0. Chosen ladder: model's explicit `thinkingLevelMap` (`models.json`, catalog); else, reasoning model of a custom provider: family's rulebook ladder; else none. Built-in providers keep catalog ladders. Custom `qwen3.8-27b`, no map → `off`, `low`, `medium`, `xhigh`.
1. No reasoning → plain default (shipped: `off` only); map ignored.
2. Reasoning, per entry: `null` removes; wire string keeps, sent as is; missing → default ladder (shipped: `off` to `high`, so `xhigh`/`max` need entries), sent in the wire API's own form.
3. So reasoning models may offer `off` only (rest `null`) or nothing (all `null`).
4. Daemon serves offered levels (`availableThinkingLevels`; each catalog model's levels to the picker); clients compute no ladder.

Clamp → offered level:

1. Offered → unchanged.
2. Else first offered above; none → first offered below.
3. None offered → `off`.

Cycle (`cycle_thinking_level`, forward/backward), one offered step:

1. < 2 offered (no reasoning, or `off` only) → no change; daemon answers `null`.
2. Else from clamp of current. Forward: next, last → first. Backward: previous, first → last.
3. Forward visits each offered level once per lap in ladder order; forward and backward cancel.

Session (main conversation stores its level; may be unset):

1. Open settles: stored, else default (`defaultThinkingLevel`, else `medium`); clamped if the session model is in the catalog, else kept.
2. Model switch clamps current level to the new model; set clamps the request (kept without catalog model); cycle sets the step's result.
3. Sent: stored level, else `off`; each provider clamps before sending.
4. Shown (daemon summary, connection state `thinkingLevel`): stored clamped to the model (unclamped without catalog model) = sent. Unset shows `default`, never `off`.

Model `bend/effort.bend`. Laws: `LAWS.bend` section (S10). Proofs: `PROOF.bend` section `effort`. Free inputs: model with or without reasoning, any map (entries missing, `null`, wire string); level; stored level and default; switches, sets, cycle steps in any order.

| Law | Says |
| --- | --- |
| `effort_offered_plain` | No reasoning → `off` only, any map (ladder 1). |
| `effort_offered_null` | `null` entry never offered (ladder 2). |
| `effort_offered_ext` | `xhigh`/`max` only with a wire entry (ladder 2). |
| `effort_offered_kept` | Reasoning model offers each kept level: wire entry, or missing below `xhigh` (ladder 2). |
| `effort_offered_asc` | Strictly ascending, no repeats (ladder). |
| `effort_clamp_offered` | Something offered → every clamp offered; switches land on one (clamp 2, session 2). |
| `effort_clamp_keeps` | Offered level unchanged (clamp 1). |
| `effort_clamp_idem` | Clamp idempotent, even with none offered (clamp 3). |
| `effort_cycle_still` | < 2 offered → no change (cycle 1). |
| `effort_cycle_next` | Forward → next offered (cycle 2). |
| `effort_cycle_wrap` | Forward from last → first (cycle 2). |
| `effort_cycle_prev` | Backward → previous offered (cycle 2). |
| `effort_cycle_wrap_back` | Backward from first → last (cycle 2). |
| `effort_cycle_inverse` | From offered, backward cancels forward (cycle 3). |
| `effort_cycle_inverse_back` | From offered, forward cancels backward (cycle 3). |
| `effort_unset_default` | Unset shows `default`, never `off` (session 4). |
| `effort_settle_offered` | Something offered → open settles on offered (session 1). |
| `effort_stored_is_sent` | After open and any actions, stored = sent (session 1-3). |
| `effort_shown_is_sent` | After open and any actions, shown = sent (session 4). |

Code: `eukhe-ai/src/models/ladder.rs` (`thinking_level_map`, `get_supported_thinking_levels`, `registry_thinking_levels`, `registry_clamp_thinking_level`, `clamp_thinking_level`, `cycle_thinking_level`), provider clamps in `eukhe-ai/src/api/`; `eukhe-core/src/durable/open.rs` `settle_main_agent`; `eukhe-daemon/src/model_switch.rs` (switch, set), `setting_switches.rs` `handle_cycle_thinking_level`, `worker/summary.rs` `thinking_level`, `rpc/model_commands.rs`.

Tie: `eukhe-core` `durable::effort_bridge::the_rust_reasoning_depth_equals_the_bend_model` runs `get_supported_thinking_levels`, `clamp_thinking_level`, `cycle_thinking_level` (both ways, from each level) on catalog models vs `bend/bridge_effort.bend`: edge models (no reasoning, no map, `off`-only, empty ladder, one level, explicit `xhigh` and `max`) and random ones (entries missing, `null`, wire string); must reach every rule.
Tests: `eukhe-core` `durable::open::tests` (`open_settles_an_unset_thinking_level_on_the_clamped_default`); `eukhe-daemon` `setting_switches::tests` (`cycle_thinking_level` without reasoning → `null`; steps wrap both ways; unset shows `default`).
Not modelled: settings order for the default level; level → per-provider wire value.
