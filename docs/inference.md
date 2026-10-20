# Harness laws: inference, local tiny models and reasoning depth

The shared rules (what a law secures, the adversary, H1 to H6) are in [harness.md](harness.md).

### S6. The inference layer

The inference layer is between the harness and the wire APIs. It decides
what a request may ask of a provider.

1. The quirks rulebook gives the settings of a model family, a model, and
   a host as data. A rule has a layer, a target id of that layer, and
   directives with values. The compiler rejects an unknown directive, a
   value of the wrong type, and two rules of one layer and target that
   give one directive different values. A lookup takes the rule of the
   highest layer that applies: host over model over family. When no rule
   applies, the answer is Unknown. The rulebook does not guess. The wire
   API applies its own default, and the explicit `model.compat` wins over
   both. The order of the rules changes no answer.
2. A model names one target per layer. The family is the one family
   whose pattern matches the model id (or the id and name) and whose
   revision range, when it has one, holds for the revision that the id
   names (omp's taxonomy: the revision starts at the first digit after
   the prefix in the bare name; a size such as `8b` is not a revision;
   an id that names no revision has the revision 0). Thus `qwen3.8-27b`
   is in the family `qwen-3.8` (`>=3.8`) and `qwen3-8b`, `qwq-32b` are in
   `qwen` (`<3.8`). Two families
   that match one model are an error (`QuirksError::FamilyOverlap`). No
   family wins by its id or its order. The test of the shipped rulebook
   rejects two families that match one model of the compiled catalog.
   A model out of the catalog that two families match names no family:
   each family directive is then Unknown, and the log shows the error
   one time for each model id. The model is the model id. The host is
   the host that names the wire API (an API that only one host speaks),
   else the host that names the provider id, else the host with the
   longest URL fragment in the base URL (ties: the smaller host id). A
   model names one host only: the signals do not combine. For example,
   the provider `openrouter` with a loopback base URL (a local proxy)
   gets the settings of the `openrouter` host, not those of the
   `loopback` host. Before the rulebook, the code combined the provider
   and URL checks. The host `openrouter` (provider match) gives
   Anthropic-format `cache_control` marks to `anthropic/` models. The
   host `openrouter-url` (a custom provider with an openrouter.ai base
   URL) gives the other OpenRouter settings, but no marks.
3. A forced tool call names a tool and a count of retries. Every request
   of the call ends with a soft prompt that names the tool. The first
   request sets the native forced choice only when the provider supports
   it and it is free (it costs no prompt-cache invalidation). Each retry
   sets it when the provider supports it. The support is calculated for
   each request (`maps_forced_tool_choice`), with the predicate that the
   wire API uses. Under manual extended thinking, Anthropic and Claude on
   Bedrock reject a forced choice, so the request has no support: no
   attempt escalates to a flag that is not sent. A wire API that gets a
   forced choice under manual extended thinking removes it and logs a
   warning. A reply without the call starts a retry while retries
   remain. After the retries, the generation fails with
   `ForcedToolError::NotCalled`, which names the tool. When no tool is
   forced, nothing changes.
4. A provider takes at most `strict_cap` strict tool schemas per request.
   The tools of highest `priority` get them (default `0`: all equal; of
   equal tools, the earlier one first). The other tools are loose: the
   client validates and repairs their arguments. No tool is dropped. A
   tool that requires a strict schema and is past the cap is an error.
5. The repetition guard reads the text and thinking deltas of every
   stream. A chunk is one complete, non-blank output line. A line longer
   than 4096 bytes (`MAX_CHUNK_BYTES`) ends a chunk at that length, on a
   character boundary; the remaining text starts the next chunk. Thus a
   loop with no newline (`abab…`) is also cut. The guard keeps a window
   of the last `k` chunks (setting `retry.provider.streamRepeatLimit`,
   default 64). The window is periodic with period `p` when each chunk in
   it, after the first `p`, is equal to the chunk `p` before it. When the
   window is periodic with a period of 1 to `k / 4` chunks (at least 1),
   the guard aborts the request. Thus a cycle must come at least four
   times. Period 1 is one chunk `k` times in a row. With the default, a
   block of up to 16 lines that comes four times is cut. The stream then
   ends with the retryable `stream_repeating` failure. The failure message
   gives the period and the last line, and the failure info records them
   (`RepeatedLines`, read by `repeated_lines`). The harness retries the
   cut stream, but not with the same request: a model decodes the same
   request in the same way, and a model that decodes greedily (for
   example `elpis-fast`, which refuses a temperature other than 0) loops
   on it again. The retry's request ends with a harness note that gives
   the attempt, the period and the last line (docs/harness.md H4.7). The
   run does not log the note. A stream with no periodic window of `k`
   chunks is not cut. For
   each period `p`, the guard keeps a counter: the number of chunks in a
   row, up to the newest, that are equal to the chunk `p` before them. The
   window is periodic with period `p` when this counter is `k - p` or
   more. Thus the guard keeps at most `k / 4` chunks and `k / 4` counters,
   and one partial chunk for each block, for all lengths of the stream.
   Example: in a real session, `qwen3.8-27b` looped in its thinking for
   1,359 lines on a cycle of 7 lines, and no line came two times in a
   row. The rule before this one (one chunk `k` times in a row) did not
   cut it. This guard cuts it at line 77. A reply that ends with no text
   and no tool call (for example only thinking, when the guard did not
   cut it) is no answer either: the harness fails it as a model error and
   retries it with a note that says that the reply gave no text
   (docs/harness.md H4.7). A `length` stop with no answer gets a length
   note (docs/harness.md H4.8). A noted retry (a cut stream, no answer)
   spends a note of the generation's own budget (`MAX_NOTES`, 8), not a
   retry of the retry policy, and goes out at once, with no backoff.
6. Compaction starts on the background path when the context is more
   than the threshold: the limit (`contextWindow - reserveTokens`) less a
   margin (`BackgroundMargin`). The eukhe session sets the margin to 10%
   of the context window (`eukhe-core`); the default of the harness
   library is 32,768 tokens. A context more than the limit blocks the
   request until compaction ends. A background compaction that ends
   during a run places its summary at the run's next boundary; its wire
   `compaction_end` goes out then, with that summary, or as a skip when
   the summary went stale behind a later compaction. The queued summary
   stays after a run end (an aborted run keeps its queued writes). When
   the summary write leaves the queue with no settlement, or a snapshot
   replaces the events that could settle it, the `compaction_end` goes
   out as unsuccessful. While a summary is in the queue (not placed, not
   stale), no background compaction starts. The compaction keeps the most
   recent `compaction.keepRecentTokens` of the context (eukhe default
   40,000; system entries count). The kept part is at most half of the
   threshold, so a compaction always has history to summarize. With a
   small context window, the compaction thus keeps less than the setting.
   The threshold check uses a local estimate of the request's input
   tokens. When `compaction.providerTokenCount` is on (default off), the
   check asks the provider's token counter (`count_tokens`) first. This
   adds one request to the provider per generation. When the provider has
   no counter or the count fails, the check logs a warning and uses the
   local estimate.
7. A provider can have more operations than the chat stream. The
   capability surface names eight: `count_tokens`, `list_models`,
   `embed`, `generate_image`, `tokenize`, `usage`, `web_search` and
   `compact`. The rulebook gives the support as data: the directive with
   the name of the operation has the dialect of the endpoint (for
   example `"list_models": "openai"`), or `false`. The compiler rejects a
   dialect that has no implementation of that operation. A host of scope
   `capabilities` (`openai`, `google`, `llama-cpp`) serves only these
   lookups. It sets only capability directives and `prompt_progress`,
   and the wire lookup skips it, so it changes no other request setting:
   a local `openai` provider keeps the loopback settings. The
   `llama-cpp` host sets `"prompt_progress": true`: an
   `openai-completions` request then sends `"return_progress": true`,
   and the stream gives a `prompt_progress` event (`total`, `cache`,
   `processed`, `time_ms`) for each progress chunk, before the first
   token. `model.compat.supportsPromptProgress` wins over the rulebook.
   An operation
   that the provider does not have fails with the typed error
   `Unsupported { capability, provider }` before auth or a request. It
   never uses another provider or the local estimate. A caller that
   wants the estimate asks for it. `eukhe provider caps [<provider>]`
   shows the support and sends no request. `eukhe provider models
   <provider>` asks the provider for its model list.
8. The service tiers that a provider honors are rulebook data
   (`service_tiers`): each entry names a provider, a wire API, the tiers,
   and optionally a family. A model honors `default`, and each tier of
   each entry whose provider and API are the model's and whose family,
   when the entry names one, is the model's family. The shipped table:
   `openrouter` over `openai-completions` honors `flex` and `priority`
   (OpenRouter routes to tier endpoints and bills the tier that served
   the request); `openai` over `openai-responses` and `openai-codex` over
   `openai-codex-responses` honor `auto` and `scale`; the families
   `gpt-priority` and `gpt-priority-explicit-cache` add `flex` and
   `priority` on `openai` and `priority` on `openai-codex` (the ChatGPT
   backend has no flex tier). The
   `/tier` and `/fast` commands, the connection state
   (`availableServiceTiers`), the image route and the completions request
   (`service_tier`) all read this table (`quirks::service_tiers`).
9. The thinking ladder of a model is rulebook data (S10, the ladder 0).
   The directive `thinking_ladder` gives a family its ladder as a
   `thinkingLevelMap`. The shipped ladders: `qwen-3.8` offers `off` (wire
   `none`), `low`, `medium` and `xhigh`; `qwen` offers `off` (the
   template toggle) and `high` (omp's llama.cpp rules for the Qwen
   templates); `grok-4.3` sends `off` as `none` and removes `minimal`;
   `grok-4.5` removes `off` and `minimal`; `grok-4.6` (the ids
   `grok-4.6` and `grok-4.7`) removes `off` and `minimal` and adds
   `xhigh`. The default ladders (`thinking_defaults`) give the levels
   where a ladder has no entry: `reasoning` lists `off` to `high`,
   `plain` (a model without reasoning) lists `off`. A stored xAI
   subscription moves the xAI models to `openai-responses`; a model
   there without a `thinkingLevelMap` gets the rulebook's ladder of its
   model, else a map that sets every level to null.
10. The harness reads the tool calls at the end of a stream, whatever
    the stop reason. A reply with a tool call runs its calls: vLLM,
    llama.cpp and Ollama send the stop reason `stop` with tool calls
    (docs/harness.md H4.1). A reply that hit the output limit (stop
    reason `length`) runs none of its calls: their arguments can be cut.
    Each call gets a `truncated` result that tells the model to make the
    call again with complete arguments, and to write large content as a
    minimal version first, then extend it with edits. Some models write a
    tool call as markup in the text, not in the tool-call channel. In a
    reply with no tool call, the harness reads the markup of five
    families (Hermes and Qwen JSON, Qwen3-Coder XML, the omp "qwen" form,
    Kimi section tokens, DeepSeek DSML), but not in quoted code. When
    every leaked call parses and names a tool that the request offered,
    the harness rebuilds the calls: the markup leaves the text, the stop
    reason becomes `toolUse`, and the calls run as tool calls. Else the
    reply is retried with a leak note, at most `LEAK_NOTES` (2) in a row;
    then it answers as text (docs/harness.md H4.8, laws
    `run_calls_never_answer`, `rec_leak_rebuilt_is_calls`). Code:
    `eukhe-durable/src/harness/generation/leak.rs` (`scan`),
    `generation.rs` `classify`, `generation/round.rs`
    `start_tool_round`.
11. The default model of each provider is rulebook data
   (`provider_defaults`: provider id to model id,
   `quirks::provider_default_model`). The startup model chain, the
   fallback model template and the onboarding's model after the Prime
   Inference sign-in read it. A provider that the table does not name
   has no default.
12. The prices that a catalog row does not carry are rulebook data.
   `service_tier_prices`: each row names a provider, a wire API, the
   tiers it prices (the `service_tier` of the response, else of the
   request), a multiplier, and optionally a model id. A response at a
   tier costs the base price times the multiplier of the row of the
   model's provider, API and id, else of the row of its provider and API
   without a model id; with no row the cost stays the base price. The
   shipped table: `openai` over `openai-responses` and
   `openai-completions` prices `flex` at 0.5 and `priority` and `fast`
   (the value that the API reports for Fast mode) at 2, `gpt-5.5` at
   2.5; `openai-codex` prices `flex` at 0.5 and `priority` at 2,
   `gpt-5.5` at 2.5. `cache_write_1h_prices`: each row names a regex on
   the lowercased model id and a multiplier of the input rate; the first
   row that matches prices the model's 1h cache writes, and a model with
   no row pays its own cache write rate for them. The shipped table:
   `claude` at 2 (Anthropic's price, which Bedrock and the gateways that
   resell Claude at Anthropic's list rates charge too).
   `models::calculate_cost` and `models::apply_service_tier_pricing`
   read these tables (`quirks::cache_write_1h_multiplier`,
   `quirks::service_tier_multiplier`).
13. Every other fact of a model that a wire API reads is rulebook data
   too (S6.10): a wire API asks the rulebook, never the model id.
   - `adaptive_thinking` (families `claude-adaptive`,
     `claude-adaptive-4-6`): the model takes `thinking.type: adaptive`
     with an effort, on Anthropic Messages and on Bedrock alike
     (`models::adaptive_thinking`). An explicit
     `compat.forceAdaptiveThinking` of the model wins over it.
   - `thinking_block_binding` (`claude-adaptive`): Bedrock sends
     `thinking.block_binding` (not on GovCloud).
   - `prompt_caching` (`claude-adaptive`, `claude-adaptive-4-6`,
     `claude-cached`: true; `claude-uncached`: false): Bedrock sends
     `cachePoint` blocks. A model that no rule names caches only with
     `AWS_BEDROCK_FORCE_CACHE=1`.
   - `explicit_cache_breakpoints` (`gpt-explicit-cache`,
     `gpt-priority-explicit-cache`): an OpenAI Responses request sends
     `prompt_cache_breakpoint` and `reasoning.context: "all_turns"`.
   - `google_thinking_level` (`gemini-3-plus`, `gemini-latest`,
     `gemma-4`: true; the Gemini 2.5 families: false): a Google request
     sends `thinkingLevel`; a model that no rule names sends
     `thinkingBudget`.
   - `thinking_budgets` (`gemini-2.5-pro` 128, 2048, 8192, 32768;
     `gemini-2.5-flash` 128, 2048, 8192, 24576; `gemini-2.5-flash-lite`
     512, 2048, 8192, 24576): the Google budget of each level, on the
     Gemini API and on Vertex alike. The user's `thinkingBudgets` wins,
     held inside the rule's `minimal` to `high`. A model with no rule
     sends the user's budget, else `-1` (dynamic).
   - `thinking_defaults.budgets` (1024, 2048, 8192, 16384): the budget
     of a level where neither the user nor a rule gives one, for every
     wire API that sends a token budget.

   A family may give an `except` regex: a model that it matches is not
   in the family, so the families stay disjoint. The Bedrock effort is
   the model's thinking-level map (a native `xhigh` model says
   `xhigh: "xhigh"` there), else the Bedrock default effort.

Model: `bend/infer.bend`. Laws: `LAWS.bend` section (S6) and
`laws/ladder.bend` (S6.9). Proofs:
`bend/proof_infer.bend`, `bend/proof_quirks.bend`. Every input is free:
any rulebook, query and directive; any replies of the model; any provider
support; any tools; any stream; any context sizes.

| Law | Says |
| --- | --- |
| `quirk_unknown_rejected` | A rulebook with a rule of an unknown directive does not compile (S6.1). |
| `quirk_clash_rejected` | Two rules of one layer, target and directive with different values do not compile (S6.1). |
| `quirk_unknown_when_none` | With no rule that applies, the answer is Unknown (S6.1). |
| `quirk_known_when_some` | A rule that applies always gives an answer (S6.1). |
| `quirk_highest_wins` | In a rulebook that compiles, the rule of the highest layer that applies gives the answer (S6.1). |
| `quirk_order_free` | In a rulebook that compiles, the order of two rules changes no answer (S6.1). |
| `quirk_compile_order_free` | The order of two rules does not change whether the rulebook compiles (S6.1). |
| `quirk_ladder_explicit_first` | The explicit thinking-level map is the chosen ladder, over the rulebook's ladder (S6.9). |
| `quirk_ladder_rule_second` | With no explicit map, the rulebook's ladder is the chosen ladder (S6.9). |
| `quirk_ladder_default_last` | With neither, the chosen ladder has no entry: the default ladder gives every level (S6.9). |
| `quirk_ladder_offered_exact` | A reasoning model offers a level exactly when its chosen ladder gives it a wire string, or gives it no entry and the default ladder lists it (S6.9). |
| `quirk_ladder_plain_exact` | A model without reasoning offers exactly the levels of the plain default ladder (S6.9). |
| `quirk_ladder_shipped_is_s10` | With the shipped default ladders, the offered levels are the S10 ladder of the chosen map, so every S10 law holds for them (S6.9). |
| `force_bounded` | A forced call makes at most `1 + retries` attempts (S6.3). |
| `force_first_flag` | The first attempt sets the native flag only when it is supported and free (S6.3). |
| `force_retry_flag` | Every retry sets the native flag when it is supported (S6.3). |
| `force_reports` | A forced call reports a call exactly when the model called the tool within its attempts (S6.3). |
| `strict_within_cap` | At most `cap` tools get strict schemas (S6.4). |
| `strict_keeps_every_tool` | Every tool is strict or loose, as many times as it was given (S6.4). |
| `strict_by_priority` | Every strict tool has a priority of at least every loose tool (S6.4). |
| `guard_cuts_repeats` | A stream that repeats a chunk `k` times in a row is cut (S6.5). |
| `guard_cuts_loops` | A stream with a window of `k` chunks that is periodic, with a period of at most `k / 4` (at least 1), is cut (S6.5). |
| `guard_keeps_others` | A stream with no window of `k` chunks that is periodic, with a period of at most `k / 4` (at least 1), is not cut (S6.5). |
| `compact_starts_early` | When each turn grows the context by at most the margin, compaction starts before any turn over the limit (S6.6). |

Code: `eukhe-ai/src/quirks/mod.rs` (`compile`, `Rules::lookup`,
`Rulebook::query`, `Rulebook::family`, `Rulebook::check_catalog`,
`Quirks`, `ModelKey`, `ThinkingDefaults`), `quirks/revision.rs`,
`quirks/tiers.rs` (`service_tiers`, `supports_service_tier`),
`quirks/prices.rs` (`service_tier_multiplier`,
`cache_write_1h_multiplier`),
`eukhe-ai/src/models/ladder.rs` (`thinking_level_map`, the ladder
functions) and `quirks/rulebook.json` (the shipped
rules); the resolvers that take the rulebook as their detected input:
`api/openai_completions/compat.rs` `detect_compat`,
`is_custom_qwen_template_model`; `api/anthropic_messages.rs`
`get_anthropic_compat`, `manual_thinking`; `api/openai_responses.rs`
`get_compat`;
`api/azure_openai_responses.rs`, `api/openai_codex_responses/request.rs`,
`api/bedrock_converse_stream.rs` (strict default, `manual_thinking`),
`models/thinking.rs` `adaptive_thinking`,
`api/google_shared/stream.rs` (validated function calling),
`api/mistral_conversations/payload.rs`;
`api/constrained_sampling.rs` `strict_budget`, `StrictPlan`;
`eukhe-types/src/pi_ai/tool.rs` `Tool::priority`;
`eukhe-types/src/pi_ai/settings.rs` `ToolChoice` (`Required`,
`Tool(name)`), mapped in every wire API;
`api/simple_options.rs` `maps_forced_tool_choice`;
`eukhe-durable/src/harness/generation/force.rs` (`ForceEscalation`,
`ForceReply`, `Forcing`, `ForcedToolError`, `soft_prompt`) and the option
`ConversationStreamOptions::force_tool`;
`eukhe-ai/src/utils/stream_repeat.rs` (`RepetitionGuard`,
`MAX_CHUNK_BYTES`, `StreamRepeat`), `api/lazy.rs` `watched_lazy_stream`;
`eukhe-durable/src/harness/generation/decide.rs` `threshold_for`,
`types/settings.rs` `BackgroundMargin`, `ThresholdTokens`;
`eukhe-durable/src/harness/generation.rs` `threshold_compaction`,
`provider_tokens` (the provider count and its logged fallback);
`eukhe-core/src/settings/cvar/table.rs`
`COMPACTION_PROVIDER_TOKEN_COUNT`;
`eukhe-core/src/durable/settings.rs` (`WindowPercent(10.0)`, the repeat
limit); `eukhe-daemon/src/worker/durable_host/translator.rs`
(`summary_write`, `end_lost_placements`, the held ends at a snapshot);
`eukhe-ai/src/capabilities/` (`Capability`, `Dialect::endpoint`,
`capabilities_of`, one module per dialect), `models/capabilities.rs`
(the `Models` operations), `Directive::Endpoint`;
`eukhe-cli/src/provider_command.rs`.

Tie: the bridge tests
`harness::generation::infer_bridge::the_rust_quirks_rulebook_equals_the_bend_model`
(compile and lookup on generated rulebooks, each also with two rules
swapped, against `bend/bridge_quirks.bend`; the directives are the first
of each value type in `Directive::ALL`, and a query can name no family
or no host),
`durable::effort_bridge::the_rust_reasoning_depth_equals_the_bend_model`
(S10: the rulebook's default ladders and rule ladders against
`bend/infer.bend` section 6) and
`the_rust_inference_units_equal_the_bend_model` (the escalation, the
strict budget, the guard on lines fed in random deltas: random chunks,
cycles of 1 to 4 chunks, the same cycles with one chunk changed, and the
observed loop of 7 lines against windows of 27, 28, 32 and 64 chunks, and
the compaction threshold, against `bend/bridge_infer.bend`) compare the
transcripts byte for byte. The code compares token counts strictly
(`>`), so for whole token counts the model threshold is the limit less
the margin, plus one. Regression tests: `quirks::tests` (the shipped
rulebook compiles and no two families match one catalog model;
`families_that_overlap_on_a_catalog_model_are_rejected`;
`a_model_two_shipped_families_match_names_no_family`; errors;
precedence; order; host and family queries; the former hand-written
checks; `the_shipped_qwen_families_split_at_the_revision_3_8`),
`quirks::revision::tests`, `quirks::tiers::tests`
(`the_table_keeps_every_answer_of_the_former_predicate`: every model of
the compiled catalog and every tier, against the former hardcoded
predicate, kept only in the test),
`models::ladder::tests`, `openai_completions::tests::tool_choice`
(`a_custom_qwen_3_8_model_sends_the_rulebook_ladder`),
`openai_completions::tests::service_tier`,
`openai_completions::tests::host_quirks`
(`a_custom_provider_at_openrouter_ai_sends_no_cache_marks`,
`the_openrouter_provider_at_a_loopback_url_keeps_the_openrouter_settings`),
`constrained_sampling::tests`
(`the_strict_budget_keeps_the_highest_priorities_and_the_earlier_of_equals`,
`a_strict_plan_sends_tools_past_the_cap_loose_and_drops_none`),
`generation::force::tests`
(`manual_extended_thinking_has_no_native_forced_choice`), the
`anthropic_forced_tool_choice` test
`the_forced_choice_predicate_matches_the_wire`,
`utils::stream_repeat::tests` (`a_loop_with_no_newline_is_cut_in_bounded_chunks`,
`a_long_line_is_chunked_on_character_boundaries`,
`the_observed_thinking_loop_is_cut_at_its_77th_line`,
`the_observed_thinking_loop_fails_as_repeating_by_default`,
`a_cycle_longer_than_a_quarter_of_the_window_is_not_cut`,
`a_single_differing_line_restarts_the_window`,
`the_guard_keeps_a_quarter_of_the_window`, and
`the_guard_cuts_where_the_model_does`: every stream of three chunk values
up to 8 chunks, for every `k` up to 12),
`generation::tests::threshold`, the translator tests
`a_summary_write_that_leaves_the_inbox_unsettled_ends_its_compaction` and
`a_snapshot_ends_the_compactions_whose_end_it_may_have_replaced`, and the
provider wire tests (`cargo test -p eukhe-ai --test providers`). Not
modelled: the query map from a model to its targets (S6.2), the soft
prompt and wire forms of a forced choice, and the split of deltas into
chunks. Their tests tie them.

#### S6 tool-call argument repair

A model can send tool-call arguments that are not strict JSON, or that
use another spelling of a declared type. The client repairs these
arguments before validation. It does as omp does.

1. The streaming preview of the arguments closes an incomplete text.
   The final parse does not. It reads the full text with `JSON.parse`.
   When that fails, it escapes raw control characters and invalid escapes
   in strings, and tries again. When that fails too, it reads a relaxed
   dialect: single quotes, unquoted keys, comments, `True`, `False` and
   `None`, stray and trailing commas, `0x` and `0b` numbers, and an
   unquoted value such as `src/main.rs`. The relaxed dialect rejects a
   truncated text, characters after the value, a number that is not
   finite, and an unquoted value that can hide the next field.
2. When no parse reads the text, or the value is not an object, the
   arguments become `{ __parseError, __rawJson }`. They keep the parse
   error and the first 512 characters of the text. No key of the text
   stays, so a half-formed call never runs. The tool result is an
   `invalid_arguments` error. It gives the parse error and the raw text
   to the model.
3. A key in a JSON string (`"\"path\""`) becomes the plain key. This
   does not occur when the plain key is also in the call.
4. A value in another spelling of its declared type becomes that type:
   a JSON string of a declared object or array, a single string for an
   array of strings, and a number or boolean for a string. The string
   spellings of a boolean or number become the value, as before.
5. Each repair is an `argument_repaired` warning on the tool result. An
   unknown key of a closed schema stays an error.
6. A call of a tool that is not available gets a `tool_unavailable`
   result. The message names at most three of the offered tools. First
   come the names at a small edit distance, nearest first. Then come the
   names that end with the last `_` or `__` segment of the called name.

Code: `eukhe-ai/src/utils/json_parse.rs` (`parse_json_with_repair`,
`parse_tool_call_arguments`), `json_parse/relaxed.rs`, the final parse
of each wire API (`anthropic_messages/events.rs`,
`bedrock_converse_stream/events.rs`, `mistral_conversations/consume.rs`,
`openai_completions/streaming.rs`, `openai_responses_shared/stream.rs`);
`eukhe-durable/src/harness/tool/arguments.rs` (`repair_arguments`,
`ArgumentError::NotJson`); `tool/result.rs` (`tool_unavailable_message`).
Regression tests: `utils::json_parse::tests`,
`json_parse::relaxed::tests`, `tool::arguments::tests`, and
`tool::result::tests`.

#### S6 the built-in model catalog

The built-in model catalog is the list of models that the `/model` menu,
the registry and the daemon's `get_model_catalog` use. The user's
`models.json` goes on top of it. It has two sources. Both are on this
machine: eukhe does not fetch a catalog.

1. The bundled catalog, `models.bundled.json` beside the executable. A
   release makes it from the catalog repository
   (`PrimeIntellect-ai/prime-agent-catalog`) at the commit in
   `scripts/release/catalog-pin.json` and checks the sha256 of each
   file. The parse is strict, and each entry must use a transport that
   the client compiles in (transport pinning).
2. The compiled catalog, the pi-ai tables of `eukhe-ai`
   (`providers/data/*.json`) and the Prime Inference entries.

The built-in catalog is the union of the two sources. A model is its
provider and id.

1. Each model of either source is in the catalog. Neither source hides
   a model of the other. Each model is in the catalog one time.
2. When the two sources have a model, the bundled entry gives its api,
   its `baseUrl`, its data (`name`, `reasoning`, `input`, `cost`,
   `contextWindow`, `maxTokens`) and each optional field that it has.
   The compiled entry gives each optional field that the bundled entry
   does not have (`thinkingLevelMap`, `compat`, `featured`, `headers`),
   but only when the two entries use the same api.
3. A model that only one source has comes from that source with no
   change.
4. The order is the bundled entries in bundled order, then the compiled
   models that the bundle does not have, in compiled order. The fields
   of a model come only from its entry in each source, thus the order in
   which eukhe reads the sources changes no model.
5. Without a bundled catalog, or with a damaged one, the catalog is the
   compiled catalog.

Thus a model that the compiled catalog has and the pinned catalog does
not have (for example Claude Haiku 5.5) is in the `/model` menu.

Every week, `.github/workflows/catalog-pin.yml` moves the pin to the
newest commit of the catalog repository. It runs the same validation as
`make catalog-pin`, records the commit and both sha256, and opens a pull
request. CI runs on that pull request.

Older builds kept a fetched catalog in
`~/.eukhe/models/provider-model-catalog.v1.json`. No current code reads
or writes that file.

Laws: `laws/catalog_union.bend` (C1, the model in
`bend/catalog_union.bend`, the proofs in `bend/proof_catalog_union.bend`).
Code: `eukhe-models/src/effective.rs` (`effective_catalog`),
`chain.rs` (`ModelCatalog::models`), `bundled.rs`
(`load_bundled_models`), `pinning.rs`. Bridge:
`effective::bridge::the_rust_union_equals_the_bend_model` runs the code
against `bend/bridge_catalog_union.bend` on generated catalogs.
Regression tests: `chain::tests::a_bundle_without_a_compiled_model_keeps_it`;
`eukhe-daemon` `tests/model_catalog_e2e.rs`
(`a_bundle_without_a_compiled_model_still_lists_it`: the pinned catalog
snapshot as the bundle, an Anthropic login, and the daemon's catalog has
Claude Haiku 5.5).

#### S6 models.json and the saved default model

One loader reads `models.json` for every view: the registry (`eukhe
model list`, the `/model` menu, the daemon's `get_model_catalog`,
onboarding, the auxiliary model, the memory compactor, RLM, usage) and
the model collection of a session.

1. Each `providers.<id>` entry loads alone. A bad entry (a wrong type, a
   missing `baseUrl` or `apiKey`, a model that is not valid) drops only
   that provider, and a diagnostic names `providers.<id>`. The other
   providers stay.
2. A file that eukhe cannot read or parse is one diagnostic and gives no
   custom models.
3. The diagnostics show in `eukhe model list` (stderr), in the
   `modelsJsonErrors` list of the `get_model_catalog` reply, and in the
   settings-error row of each session at open.

A session that no request pins starts on the saved default
(`defaultProvider`/`defaultModel`). eukhe never moves past it in
silence:

1. When the catalog does not have it, or a set `enabledModels` scope
   does not include it, the session runs on the next startup default.
   One `eukhe.default_model` row (display-only) names the saved default,
   the reason and the model in its place.
2. When its provider has no credentials, the resolution is the typed
   error `DefaultUnusable` with the login hint. No other provider takes
   its place: the session opens with no model and the row names the
   saved default and the reason.
3. When no other model can take its place, the session also opens with
   no model and the row.
4. The memory compactor (no `memory.model`) fails its call with the
   saved default and the reason.

Laws: `default_honoured_or_reported`, `default_quiet_when_honoured`,
`default_quiet_when_unset`, `default_unkeyed_never_moves` (the model in
`bend/default_model.bend`, the proofs in
`bend/proof_default_model.bend`). Code: `eukhe-core/src/models/custom.rs`
(`ModelsConfig::load`), `models/registry.rs` (`compose`),
`durable/models/compose.rs`, `models/resolver.rs`
(`saved_default_miss`), `durable/models.rs` (`resolve_session_model`,
`resolve_open_model`). Bridge:
`durable::models::default_bridge::the_rust_session_model_resolution_equals_the_bend_model`
runs the resolution against `bend/bridge_default_model.bend`.

### S9. Local tiny models

A local tiny model is a small model that runs on this machine. eukhe uses
it for some workloads (roles): session titles (`tiny`), typed judgments
(`judge`), translation (`translate`), text to speech (`speech`) and speech
to text (`dictation`). It is done as omp does it.

The catalog (`eukhe-tiny/src/catalog.rs`) pins each model. Each file
names its Hugging Face repository, the commit, the size and the sha256.
The models: `lfm2.5-230m` and `lfm2.5-350m` (text, ONNX q4), `whisper-base`
and `whisper-small` (speech to text), `kokoro` (Kokoro-82M, text to speech,
with the misaki lexicon for its phonemes).

Download. Only the user starts a download:
`eukhe tiny-models download <id>` or `eukhe tiny-models download all`.
`eukhe tiny-models list` shows each model as installed, missing or
incomplete. Nothing else downloads a model.

1. The download writes each file into a staging directory
   (`<agent dir>/models/tiny/.staging-<id>-<pid>`). It computes the sha256
   while it writes.
2. A file of another size or another sha256 stops the download. The
   staging directory is removed. An earlier install does not change. If
   the staging directory cannot be removed, the download still fails
   with its own error, and a warning names the directory.
3. When all files are correct, one rename installs the directory as
   `<agent dir>/models/tiny/<id>`. Thus a model is complete or absent.

The worker. One worker process serves one model and backend, for every
eukhe process. Its socket, bind lock and log are in
`<agent dir>/run/tiny/` (`<id>-onnx.sock`, `.bind.lock`, `.log`). The
worker and the client make this directory 0700, also when it exists
already. The worker is
`eukhe tiny-worker <id> --backend onnx --agent-dir <dir>`, a hidden
command. It gets the agent dir of the process that starts it on its
command line, never from its environment. Thus a daemon started with
`--agent-dir` and a worker it starts use the same directory.

1. A process that needs a model connects to the socket and sends `ping`.
   The worker answers with its launch tag:
   `<build id>|onnx|<device>|<dtype>`.
2. Same tag: the process uses the worker (joined).
3. Another tag: the process sends `shutdown`. The worker removes its
   socket and answers `bye`. It takes no more connections or requests.
   The requests of other processes that are in progress get their full
   answers; then the worker exits. The process starts a new worker
   (replaced). Thus a new build or a changed device or dtype setting
   never uses a stale worker.
4. No live socket: the process starts a worker (started). The worker
   starts detached, in its own process group. It takes the bind lock
   only while it checks the socket and binds it. If a live worker
   answers, the new worker exits and the process uses the live one.
5. The worker exits after 15 minutes without a request
   (`EUKHE_TINY_WORKER_IDLE_MS` changes the window for tests). It
   removes its socket first.
6. Requests are JSON lines: `load`, `chat` (messages, prefill, stop
   strings, max tokens), `transcribe` (audio, language), `speak` (text,
   voice, speed). Each request gets one answer, in order. The client
   makes the prompt and reads the output. If the worker stops during a
   request, the client gets a typed error (`Crashed`) with the log path.
   Each side reads a line of at most 256 MiB. The worker answers a
   longer request line with `bad_request`; the client treats a longer
   answer line as out of protocol. Neither side keeps the bytes of a
   longer line.

The engine (`eukhe-tiny-onnx`) is ONNX Runtime through the `ort` crate.
The worker loads the runtime library at run time:
`providers.tinyRuntimeLibrary`, else `ORT_DYLIB_PATH`, else
`libonnxruntime.so` (nixpkgs `onnxruntime`, 1.24 or later). The Nix
package wrapper and the dev shell set `ORT_DYLIB_PATH` to the nixpkgs
library (`--set-default`: a value the user sets wins). The build
downloads nothing and links no runtime. Inference is on the CPU. The
text tokenizer is eukhe's own (`tokenizer.rs`): the byte-level BPE of
the model's `tokenizer.json`, with its added tokens, its pre-tokenizer
regex and its ranked merges. A file with any other setting does not
load.

Roles. A role names a chain of models:

1. The chain is `modelRoles.<role>` (when set), then
   `retry.fallbackChains.<role>`. An explicit `[]` keeps the role on
   its primary model only. An unset chain is the built-in priority: the
   catalog models of the role, then the session's provider model (for a
   text role). For `translate`, `lfm2.5-350m` comes before
   `lfm2.5-230m` (see Translation).
2. A local model is available when it is installed. A provider model is
   available when it is the session's usable model.
3. A task uses the first available model of the chain. When no model of
   the chain is available, the task fails as `Unavailable`. It never uses
   a model outside the chain.

Uses. The first user message of a top-level session starts a title in
the background (role `tiny`; `titles.generate: false` turns it off). The
turn does not wait for it. A failure leaves the session without a title.
A user name is never replaced. With `modelRoles.tiny` unset and no local
model installed, the title is one more request to the session's provider.
A scripted session (the faux-script test seam) takes no title. The
`local` provider serves each text catalog model as a classifier model
(`local/<id>`) on the `classify` path. A code-mode `models.classify()`
call with no model (`null` or `undefined`) uses the `judge` role. Its
model is the first model of the chain that is an available classifier
model: an installed local model, or a provider classifier model with
configured auth. When no model is available, the call fails with
`Unavailable`, and the message names the role and its chain.
`eukhe translate <lang> <text>`, `eukhe say <text> [--out f.wav]` and
`eukhe transcribe <file.wav>` use the roles `translate`, `speech` and
`dictation`. First paint never waits for a model load.

Translation. The request is one user turn,
`Translate from English to <Language>.\nEnglish: <text>`, and the
assistant turn starts with `<Language>:`. A text of one line stops at
the first line end. If the reply is empty, or has the same letters and
digits as the input (case ignored), the translation fails with a typed
error (`TranslationError::Empty`, `TranslationError::Unchanged`) and
prints nothing. A tiny model that does not translate repeats its input,
so such a reply is never the answer. An input with no letters is
exempt. This recipe won a fixed eval: 10 short English sentences
(`hello`, `good morning, my friend`, ... `See you tomorrow.`) into
German, French, Spanish and Portuguese, greedy, each variant stopped at
the first line end. The table gives the echoes (replies equal to the
input) out of 40 and the mean chrF (0 to 100) against one reference
translation:

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

The new recipe is the best on `lfm2.5-350m` and close to the best on
`lfm2.5-230m`. The example pair needs one example per target language, so
eukhe does not use it. `lfm2.5-230m` still translates badly even with the
new recipe (`hello` into German gives `willkommen`). Thus the built-in
`translate` chain takes `lfm2.5-350m` first when it is installed.
`lfm2.5-350m` gives `Hallo`, `Vielen Dank.` and `Où est la gare ?`, but
it also makes errors (`Gute Morgensinn, mein Freund`). The prompt names
English as the source language. The eval tested English sources only.

Dictation. The TUI types speech into the editor draft:

1. `stt.enabled` (default `false`) turns on the dictation keys. The TUI
   reads the value from the session at each key press that starts a
   take. When the value is `false`, the key shows how to turn it on.
2. The actions `app.stt.pushToTalk` and `app.stt.toggle` have no default
   key. The user binds them in `binds.cfg` (S4.5), for example
   `bind f8 "action app.stt.toggle"`. Push-to-talk records while the key
   is held: the terminal sends the key again at each auto-repeat, and a
   gap of more than 300 ms (800 ms after the first press) is the
   release. Toggle records until the next press of its key.
3. The recorder is the first program on `PATH` of `pw-record`, `parec`
   and `arecord` (on macOS: `sox`, then `ffmpeg`). It writes raw 16 kHz
   mono 16-bit samples to its stdout, and the TUI writes them to a
   temporary WAV file. When the program fails, the take fails with the
   stderr of the program. eukhe does not try the next program.
4. The `dictation` role reads the file as `eukhe transcribe` does (local
   models only). The text goes into the draft at the cursor. An empty
   text shows "Dictation heard no speech".
5. The status line shows `[REC] recording`, then `[STT] transcribing`.
   Esc during a take stops the recorder, removes the file and shows
   "Dictation cancelled". A failure shows as an error row.

eukhe does not use the `cpal` crate. `cpal` needs `alsa-sys`, which
links `libasound` through `pkg-config` at build time. The CI runners
(`ubuntu-24.04`) do not install `libasound2-dev`, and the Nix build
would need `alsa-lib` and `pkg-config`. A recorder program needs
nothing at build time. Dictation is client input: it has no Bend model.
Code: `eukhe-tui/src/dictation.rs` (`Recorder`, `Transcriber`,
`SubprocessRecorder`, `run_take`, `wav_bytes`);
`session_ui/dictation.rs` (`handle_dictation_key`,
`apply_dictation_update`); `status_line.rs`;
`eukhe-cli/src/tiny_command.rs` (`RoleTranscriber`, `transcribe_file`).
Tests: `eukhe-tui` `dictation::tests` (a fake recorder and transcriber:
toggle, the hold release, a recorder failure, an abort that stops the
recorder and removes the file; the subprocess recorder with `/bin/sh`
programs: the first program found, its stderr, no audio, no program),
`keybindings::tests::dictation_actions_bind_only_through_binds_cfg`,
`status_line::tests::the_dictation_phase_leads_the_line` and
`tests/dictation_headless.rs` (the TUI on a mock daemon: toggle,
push-to-talk, Esc, a failure, `stt.enabled` off).

Model: `bend/tiny.bend`. Laws: `LAWS.bend` section (S9). Proofs:
`bend/proof_tiny.bend`. Every input is free: any chain, any set of
available models, any needs of any processes with any tags, any worker
exits, in any order.

| Law | Says |
| --- | --- |
| `tiny_pick_in_chain` | A task uses only a model of its chain that is available (roles 3). |
| `tiny_pick_first` | A task uses the first available model of its chain (roles 3). |
| `tiny_pick_unavailable` | With no model of the chain available, the task fails as Unavailable (roles 3). |
| `tiny_every_need_served` | Each need gets exactly one outcome: started, joined or replaced (worker 1-4). |
| `tiny_worker_current` | After any events, the worker runs with the tag of the last need since the last exit (worker 3). |
| `tiny_same_tag_joins` | A need with the tag of the running worker joins it (worker 2). |

Code: `eukhe-tiny/src/roles.rs` `chain`, `pick`, `Candidate`,
`FallbackChain`; `election.rs` `ensure`, `request`, `probe`, `Launcher`,
`Got`; `worker.rs` `launch_tag`, `run_worker`, `bind`, `serve`;
`client.rs` `TinyClient`, `TinyError`; `catalog.rs` `CATALOG`,
`installed`, `install_state`; `download.rs` `download`; `tasks.rs`
(prompts and output parsing); `eukhe-tiny-onnx/src/text.rs`,
`whisper.rs`, `kokoro.rs`, `runtime.rs`, `tokenizer.rs`;
`eukhe-core/src/tiny/` (settings, `resolve`, `title.rs`, `judge.rs`
`judge_classifier`); `eukhe-core/src/durable/codemode.rs`;
`eukhe-durable/src/codemode/models.rs` `ClassifierDefault`;
`eukhe-daemon/src/worker/title.rs`; `eukhe-cli/src/tiny_command.rs`,
`tiny_models_command.rs`.

Tie: the bridge tests `bridge::the_rust_pick_equals_the_bend_model` and
`bridge::the_rust_election_equals_the_bend_model` (`eukhe-tiny`) run
`pick` on generated chains and available sets, and the real election
(`ensure`, the real `serve`, in process, with a fake engine) on generated
needs and exits, against `bend/bridge_tiny.bend`. Regression tests:
`client::tests` (real worker processes in a temp run dir, started on the
client's command line with no agent dir variable and another `HOME`:
started, joined, replaced, idle exit, crash, not installed, the
client's agent dir served); `worker::tests` (a shutdown lets another
client's request in progress finish with its answer; an existing run
dir is made 0700); `protocol::tests` (a line over the limit is skipped
and the next line read); `download::tests` (a mock HTTP server: a bad
sha256, a wrong size and a broken transfer install nothing; a partial
install is replaced only on success; a staging dir that cannot be
removed keeps the download's own error);
`eukhe-core` `tiny::tests` (role resolution; `translate` takes
`lfm2.5-350m` first) and `tiny::judge::tests`
(the `judge` model of a classification with no model); `eukhe-tiny`
`tasks::tests` (the translate request; a reply that repeats the input
is `TranslationError::Unchanged`);
`eukhe-durable` `codemode::tests::calls` (`models.classify(null, …)`
asks the default classifier); `eukhe-daemon`
`tests/session_title_e2e.rs` (a supervisor on a temp socket and agent
dir, a mock provider: the first prompt titles the session, and
`titles.generate: false` titles nothing); `eukhe-tiny-onnx`
`tokenizer::tests` (ids and text against the ids that Hugging Face
`tokenizers` gave once for the same files and texts, and random text
that encodes and decodes back to itself). Real-model tests run only
with the models and the runtime library given (else they print why they
skip): `eukhe-tiny-onnx` `text::tests` (a title from `lfm2.5-230m` and,
when present, from `lfm2.5-350m`, whose graph has a `num_logits_to_keep`
input),
`whisper::round_trip_tests` (Kokoro speaks a sentence, Whisper reads it
back) and the `tokenizer::tests` on the model files; `eukhe-core`
`tiny::smoke_tests` (a title and a `Models::classify` judgment on the
`local` provider, through a real worker). Not modelled: two processes
that start a worker at the same time (the bind lock orders them; the
second one uses the first worker).

### S10. Reasoning depth

The reasoning depth (thinking level) of a session sets how much the
model thinks before it answers. The levels, in ladder order, are `off`,
`minimal`, `low`, `medium`, `high`, `xhigh` and `max`.

The ladder of a model. Every ladder and every wire value is rulebook
data (S6.9); the code holds none. A model offers some levels of the
ladder, in ladder order:

0. The chosen ladder is the explicit `thinkingLevelMap` of the model
   (`models.json`, the catalog); else, for a reasoning model of a custom
   provider, the rulebook's ladder for its family; else no ladder.
   Built-in providers keep the ladders of their catalog. Thus the custom
   model `qwen3.8-27b` with no map offers `off`, `low`, `medium` and
   `xhigh`.
1. A model without reasoning offers the levels of the plain default
   ladder (shipped: `off` only). Its map has no effect.
2. A reasoning model keeps each level by its entry in the chosen ladder.
   A `null` entry removes the level. A wire string keeps the level, and
   the request sends that string. A missing entry takes the default
   ladder (shipped: `off` to `high`, so `xhigh` and `max` need an
   explicit entry); such a level goes out in the wire API's own form.
3. Thus a reasoning model can offer `off` only (each other entry is
   `null`) or no level (each entry is `null`).
4. The daemon serves the offered levels (`availableThinkingLevels`, and
   each catalog model's levels to the model picker); clients compute no
   ladder.

The clamp. The clamp moves a level to a level that the model offers:

1. An offered level does not change.
2. Another level goes to the first offered level up the ladder from it.
   When there is no such level, it goes to the first offered level down
   the ladder from it.
3. When the model offers no level, the clamp is `off`.

The cycle. A cycle step (`cycle_thinking_level`, forward or backward)
moves one level along the offered levels:

1. When the model offers fewer than two levels, the step changes
   nothing. This is true for a model without reasoning and for a model
   that offers `off` only. The daemon answers `null`.
2. Else the step starts at the clamp of the current level. Forward goes
   to the next offered level. From the last offered level it goes to
   the first. Backward goes to the offered level before. From the first
   offered level it goes to the last.
3. Thus forward visits each offered level one time in each lap, in
   ladder order. A backward step cancels a forward step, and a forward
   step cancels a backward step.

The session. The main conversation stores its level. The level can be
unset:

1. Open settles the stored level. It takes the stored level, else the
   default (`defaultThinkingLevel` in the settings, else `medium`). When
   the session model is in the catalog, open clamps this level to the
   model. Without a catalog model, open keeps the level.
2. A model switch clamps the current level to the new model. A set
   clamps the requested level to the model (without a catalog model it
   keeps the requested level). A cycle step sets the level that the
   step gives.
3. The sent level. The durable runtime sends the stored level, else
   `off`. Each provider clamps this level to the model before it sends
   the request.
4. The displayed level. The daemon summary and the connection state
   (`thinkingLevel`) show the stored level clamped to the model (the
   stored level without a catalog model). Thus they show the level that
   the requests send. An unset level shows as `default`, never as
   `off`.

Model: `bend/effort.bend`. Laws: `LAWS.bend` section (S10). Proofs:
`bend/proof_effort.bend`. Every input is free: any model, with or
without reasoning, with any map (each entry missing, `null` or a wire
string); any level; any stored level and default; any model switches,
sets and cycle steps, in any order.

| Law | Says |
| --- | --- |
| `effort_offered_plain` | A model without reasoning offers `off` only, with any map (ladder 1). |
| `effort_offered_null` | A reasoning model never offers a level with a `null` entry (ladder 2). |
| `effort_offered_ext` | A model offers `xhigh` or `max` only with a wire entry for it (ladder 2). |
| `effort_offered_kept` | A reasoning model offers each level that its map keeps: a wire entry, or a missing entry below `xhigh` (ladder 2). |
| `effort_offered_asc` | The offered levels go up the ladder strictly: no level comes two times (ladder). |
| `effort_clamp_offered` | When the model offers a level, the clamp of each level is an offered level. Thus a model switch lands on an offered level (clamp 2, session 2). |
| `effort_clamp_keeps` | The clamp does not change an offered level (clamp 1). |
| `effort_clamp_idem` | A second clamp changes nothing, also when the model offers no level (clamp 3). |
| `effort_cycle_still` | With fewer than two offered levels, a cycle step changes nothing (cycle 1). |
| `effort_cycle_next` | Forward from an offered level goes to the next offered level (cycle 2). |
| `effort_cycle_wrap` | Forward from the last offered level goes to the first (cycle 2). |
| `effort_cycle_prev` | Backward from an offered level goes to the offered level before it (cycle 2). |
| `effort_cycle_wrap_back` | Backward from the first offered level goes to the last (cycle 2). |
| `effort_cycle_inverse` | From an offered level, a backward step cancels a forward step (cycle 3). |
| `effort_cycle_inverse_back` | From an offered level, a forward step cancels a backward step (cycle 3). |
| `effort_unset_default` | An unset level shows as `default`, never as `off` (session 4). |
| `effort_settle_offered` | When the model offers a level, open settles on an offered level (session 1). |
| `effort_stored_is_sent` | After open and any actions, the session stores the level that it sends (session 1-3). |
| `effort_shown_is_sent` | After open and any actions, the display shows the level that the session sends (session 4). |

Code: `eukhe-ai/src/models/ladder.rs` `thinking_level_map`,
`get_supported_thinking_levels`, `registry_thinking_levels`,
`registry_clamp_thinking_level`,
`clamp_thinking_level`, `cycle_thinking_level`; the provider clamps in
`eukhe-ai/src/api/`; `eukhe-core/src/durable/open.rs`
`settle_main_agent`; `eukhe-daemon/src/model_switch.rs` (model switch,
set); `setting_switches.rs` `handle_cycle_thinking_level`;
`worker/summary.rs` `thinking_level`; `rpc/model_commands.rs`.

Tie: the bridge test
`durable::effort_bridge::the_rust_reasoning_depth_equals_the_bend_model`
(`eukhe-core`) runs `get_supported_thinking_levels`,
`clamp_thinking_level` and `cycle_thinking_level` (forward and
backward, from each ladder level) on catalog models against
`bend/bridge_effort.bend`. The models are the edge models (no
reasoning, no map, an `off`-only ladder, an empty ladder, one level,
explicit `xhigh` and `max`) and random models (each entry missing,
`null` or a wire string). The test requires that the models reach each
rule. Regression tests: `eukhe-core` `durable::open::tests`
(`open_settles_an_unset_thinking_level_on_the_clamped_default`: open
settles an unset level on the clamped default); `eukhe-daemon`
`setting_switches::tests` (`cycle_thinking_level` without reasoning
answers `null`; forward and backward steps wrap; an unset level shows
as `default`). Not modelled:
the order of the settings that give the default level, and the mapping
of a level to the wire value of each provider.
