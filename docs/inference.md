# Harness laws: inference and local tiny models

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
   lookups. It sets only capability directives, and the wire lookup skips
   it, so it changes no request: a local `openai` provider keeps the
   loopback settings. An operation
   that the provider does not have fails with the typed error
   `Unsupported { capability, provider }` before auth or a request. It
   never uses another provider or the local estimate. A caller that
   wants the estimate asks for it. `eukhe provider caps [<provider>]`
   shows the support and sends no request. `eukhe provider models
   <provider>` asks the provider for its model list.

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
`libonnxruntime.so` (nixpkgs `onnxruntime`, 1.24 or later). The build
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
   text role).
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
`eukhe-core` `tiny::tests` (role resolution) and `tiny::judge::tests`
(the `judge` model of a classification with no model);
`eukhe-durable` `codemode::tests::calls` (`models.classify(null, …)`
asks the default classifier); `eukhe-daemon`
`tests/session_title_e2e.rs` (a supervisor on a temp socket and agent
dir, a mock provider: the first prompt titles the session, and
`titles.generate: false` titles nothing); `eukhe-tiny-onnx`
`tokenizer::tests` (ids and text against the ids that Hugging Face
`tokenizers` gave once for the same files and texts, and random text
that encodes and decodes back to itself). Real-model tests run only
with the models and the runtime library given (else they print why they
skip): `eukhe-tiny-onnx` `text::tests` (a title from `lfm2.5-230m`),
`whisper::round_trip_tests` (Kokoro speaks a sentence, Whisper reads it
back) and the `tokenizer::tests` on the model files; `eukhe-core`
`tiny::smoke_tests` (a title and a `Models::classify` judgment on the
`local` provider, through a real worker). Not modelled: two processes
that start a worker at the same time (the bind lock orders them; the
second one uses the first worker).

Not done:

1. Nix packaging. The Nix package does not set the runtime library, so
   local models do not run after a Nix install without more settings.
   The package wrapper must set `ORT_DYLIB_PATH`, for example
   `--set-default ORT_DYLIB_PATH ${onnxruntime}/lib/libonnxruntime.so`.
   Until then, the user sets `providers.tinyRuntimeLibrary` or
   `ORT_DYLIB_PATH`.
2. Push-to-talk. eukhe does not record audio. There are two options:
   - The `cpal` crate. It needs `alsa-sys`, which links `libasound`
     through `pkg-config` at build time. The dev shell and the Nix files
     do not supply them.
   - No new crate. Record with `pw-record`, `parec` or `arecord` to a
     temporary 16 kHz WAV file. Then transcribe the file as
     `eukhe transcribe` does.
