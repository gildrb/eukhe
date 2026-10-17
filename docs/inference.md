# Harness laws: inference

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
   whose pattern matches the model id (or the id and name). Two families
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
   loop with no newline (`abab…`) is also cut, and the guard keeps at
   most one chunk in memory for each block. When one chunk comes `k`
   times in a row (setting `retry.provider.streamRepeatLimit`, default
   64), the guard aborts the request. The stream then ends with the
   retryable `stream_repeating` failure, which the harness treats like a
   stall. A stream that never repeats a chunk `k` times in a row is not
   cut.
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

Model: `bend/infer.bend`. Laws: `LAWS.bend` section (S6). Proofs:
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
| `force_bounded` | A forced call makes at most `1 + retries` attempts (S6.3). |
| `force_first_flag` | The first attempt sets the native flag only when it is supported and free (S6.3). |
| `force_retry_flag` | Every retry sets the native flag when it is supported (S6.3). |
| `force_reports` | A forced call reports a call exactly when the model called the tool within its attempts (S6.3). |
| `strict_within_cap` | At most `cap` tools get strict schemas (S6.4). |
| `strict_keeps_every_tool` | Every tool is strict or loose, as many times as it was given (S6.4). |
| `strict_by_priority` | Every strict tool has a priority of at least every loose tool (S6.4). |
| `guard_cuts_repeats` | A stream that repeats a chunk `k` times in a row is cut (S6.5). |
| `guard_keeps_others` | A stream that never repeats a chunk `k` times in a row is not cut (S6.5). |
| `compact_starts_early` | When each turn grows the context by at most the margin, compaction starts before any turn over the limit (S6.6). |

Code: `eukhe-ai/src/quirks/mod.rs` (`compile`, `Rules::lookup`,
`Rulebook::query`, `Rulebook::check_catalog`, `Quirks`) and
`quirks/rulebook.json` (the shipped
rules); the resolvers that take the rulebook as their detected input:
`api/openai_completions/compat.rs` `detect_compat`,
`is_custom_qwen_template_model`; `api/anthropic_messages.rs`
`get_anthropic_compat`, `manual_thinking`; `api/openai_responses.rs`
`get_compat`;
`api/azure_openai_responses.rs`, `api/openai_codex_responses/request.rs`,
`api/bedrock_converse_stream.rs` (strict default, `manual_thinking`),
`bedrock_converse_stream/convert.rs` `supports_adaptive_thinking`,
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
`types/settings.rs` `BackgroundMargin`;
`eukhe-core/src/durable/settings.rs` (`WindowPercent(10.0)`, the repeat
limit); `eukhe-daemon/src/worker/durable_host/translator.rs`
(`summary_write`, `end_lost_placements`, the held ends at a snapshot).

Tie: the bridge tests
`harness::generation::infer_bridge::the_rust_quirks_rulebook_equals_the_bend_model`
(compile and lookup on generated rulebooks, each also with two rules
swapped, against `bend/bridge_quirks.bend`; the directives are the first
of each value type in `Directive::ALL`, and a query can name no family
or no host) and
`the_rust_inference_units_equal_the_bend_model` (the escalation, the
strict budget, the guard on lines fed in random deltas, and the
compaction threshold, against `bend/bridge_infer.bend`) compare the
transcripts byte for byte. The code compares token counts strictly
(`>`), so for whole token counts the model threshold is the limit less
the margin, plus one. Regression tests: `quirks::tests` (the shipped
rulebook compiles and no two families match one catalog model;
`families_that_overlap_on_a_catalog_model_are_rejected`;
`a_model_two_shipped_families_match_names_no_family`; errors;
precedence; order; host and family queries; the former hand-written
checks), `openai_completions::tests::host_quirks`
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
`a_long_line_is_chunked_on_character_boundaries`),
`generation::tests::threshold`, the translator tests
`a_summary_write_that_leaves_the_inbox_unsettled_ends_its_compaction` and
`a_snapshot_ends_the_compactions_whose_end_it_may_have_replaced`, and the
provider wire tests (`cargo test -p eukhe-ai --test providers`). Not
modelled: the query map from a model to its targets (S6.2), the soft
prompt and wire forms of a forced choice, and the split of deltas into
chunks. Their tests tie them.
