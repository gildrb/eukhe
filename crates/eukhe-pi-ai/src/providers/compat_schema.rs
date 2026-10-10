//! Port of pi-ai `src/providers/compat-schema.ts`: per-API and provider-level compat `TypeBox` schemas.

use eukhe_types::pi_ai::JsonValue;

use crate::providers::model_schema::model_cost_schema;
use crate::typebox::{Options, TSchema, Type};

type Properties = Vec<(&'static str, TSchema)>;

fn desc(text: &str) -> Options {
    Options::new().set("description", text)
}

fn desc_default(text: &str, default: impl Into<JsonValue>) -> Options {
    desc(text).set("default", default)
}

fn compat_options(text: &str) -> Options {
    desc(text).set("additionalProperties", true)
}

fn literals(values: &[&str]) -> Vec<TSchema> {
    values.iter().map(|value| Type::literal(*value)).collect()
}

/// `sessionAffinityFormat(options)`.
fn session_affinity_format(options: Options) -> TSchema {
    Type::union_with(
        literals(&["openai", "openai-nosession", "openrouter"]),
        options,
    )
}

/// `SessionAffinityFormatSchema`.
#[must_use]
pub fn session_affinity_format_schema() -> TSchema {
    session_affinity_format(desc(
        "Session-affinity header format used to route related requests consistently.",
    ))
}

/// `thinkingTokenBudgetField(options)`.
fn thinking_token_budget_field(options: Options) -> TSchema {
    Type::union_with(
        literals(&[
            "thinking_token_budget",
            "thinking_budget",
            "thinking_budget_tokens",
        ]),
        options,
    )
}

/// `ThinkingTokenBudgetFieldSchema`.
#[must_use]
pub fn thinking_token_budget_field_schema() -> TSchema {
    thinking_token_budget_field(desc(
        "Top-level request field name used by OpenAI-compatible endpoints to cap reasoning tokens. \"thinking_token_budget\" is used by vLLM, \"thinking_budget\" by Qwen, DashScope, or SGLang, and \"thinking_budget_tokens\" by llama.cpp.",
    ))
}

/// `ChatTemplateKwargValueSchema`.
#[must_use]
pub fn chat_template_kwarg_value_schema() -> TSchema {
    Type::union([
        Type::string(),
        Type::number(),
        Type::boolean(),
        Type::null(),
        Type::object([
            (
                "$var",
                Type::union(literals(&[
                    "thinking.enabled",
                    "thinking.effort",
                    "thinking.budget",
                ])),
            ),
            ("omitWhenOff", Type::optional(Type::boolean())),
        ]),
    ])
}

/// `percentileCutoffs(metric)`.
fn percentile_cutoffs(metric: &str) -> TSchema {
    let cutoff = |percentile: &str| {
        Type::optional(Type::number_with(desc(&format!(
            "{metric} at the {percentile} percentile."
        ))))
    };
    Type::object([
        ("p50", cutoff("50th")),
        ("p75", cutoff("75th")),
        ("p90", cutoff("90th")),
        ("p99", cutoff("99th")),
    ])
}

fn optional_string_array(text: &str) -> TSchema {
    Type::optional(Type::array_with(Type::string(), desc(text)))
}

fn optional_price(text: &str) -> TSchema {
    Type::optional(Type::union_with(
        [Type::number(), Type::string()],
        desc(text),
    ))
}

/// `OpenRouterRoutingSchema`.
#[must_use]
#[allow(clippy::too_many_lines)] // One TS schema literal, ported property by property.
pub fn open_router_routing_schema() -> TSchema {
    Type::object_with(
        [
            (
                "allow_fallbacks",
                Type::optional(Type::boolean_with(desc_default(
                    "Whether to allow backup providers to serve requests.",
                    true,
                ))),
            ),
            (
                "require_parameters",
                Type::optional(Type::boolean_with(desc_default(
                    "Whether to filter providers to only those that support all parameters in the request.",
                    false,
                ))),
            ),
            (
                "data_collection",
                Type::optional(Type::union_with(
                    literals(&["deny", "allow"]),
                    desc_default(
                        "Data collection setting. \"allow\": allow providers that may store or train on data. \"deny\": only use providers that do not collect user data.",
                        "allow",
                    ),
                )),
            ),
            (
                "zdr",
                Type::optional(Type::boolean_with(desc(
                    "Whether to restrict routing to only ZDR (Zero Data Retention) endpoints.",
                ))),
            ),
            (
                "enforce_distillable_text",
                Type::optional(Type::boolean_with(desc(
                    "Whether to restrict routing to only models that allow text distillation.",
                ))),
            ),
            (
                "order",
                optional_string_array(
                    "An ordered list of provider names or slugs to try in sequence, falling back to the next if unavailable.",
                ),
            ),
            (
                "only",
                optional_string_array(
                    "List of provider names or slugs to exclusively allow for this request.",
                ),
            ),
            (
                "ignore",
                optional_string_array("List of provider names or slugs to skip for this request."),
            ),
            (
                "quantizations",
                optional_string_array(
                    "A list of quantization levels to filter providers by, for example [\"fp16\", \"bf16\", \"fp8\", \"fp6\", \"int8\", \"int4\", \"fp4\", \"fp32\"].",
                ),
            ),
            (
                "sort",
                Type::optional(Type::union_with(
                    [
                        Type::string(),
                        Type::object([
                            (
                                "by",
                                Type::optional(Type::string_with(desc(
                                    "The sorting metric, such as \"price\", \"throughput\", or \"latency\".",
                                ))),
                            ),
                            (
                                "partition",
                                Type::optional(Type::union_with(
                                    [Type::string(), Type::null()],
                                    desc_default("Partitioning strategy: \"model\" or \"none\".", "model"),
                                )),
                            ),
                        ]),
                    ],
                    desc(
                        "Sorting strategy. Can be a string such as \"price\", \"throughput\", or \"latency\", or an object.",
                    ),
                )),
            ),
            (
                "max_price",
                Type::optional(Type::object_with(
                    [
                        ("prompt", optional_price("Price per million prompt tokens.")),
                        (
                            "completion",
                            optional_price("Price per million completion tokens."),
                        ),
                        ("image", optional_price("Price per image.")),
                        ("audio", optional_price("Price per audio unit.")),
                        ("request", optional_price("Price per request.")),
                    ],
                    desc("Maximum price per million tokens in USD."),
                )),
            ),
            (
                "preferred_min_throughput",
                Type::optional(Type::union_with(
                    [
                        Type::number(),
                        percentile_cutoffs("Minimum tokens per second"),
                    ],
                    desc(
                        "Preferred minimum throughput in tokens per second. A number applies to p50.",
                    ),
                )),
            ),
            (
                "preferred_max_latency",
                Type::optional(Type::union_with(
                    [
                        Type::number(),
                        percentile_cutoffs("Maximum latency in seconds"),
                    ],
                    desc("Preferred maximum latency in seconds. A number applies to p50."),
                )),
            ),
        ],
        desc(
            "OpenRouter provider routing preferences. Controls which upstream providers OpenRouter routes requests to. Sent as the provider field in the OpenRouter API request body. See https://openrouter.ai/docs/guides/routing/provider-selection.",
        ),
    )
}

/// `VercelGatewayRoutingSchema`.
#[must_use]
pub fn vercel_gateway_routing_schema() -> TSchema {
    Type::object_with(
        [
            (
                "only",
                optional_string_array(
                    "List of provider slugs to exclusively use for this request, for example [\"bedrock\", \"anthropic\"].",
                ),
            ),
            (
                "order",
                optional_string_array(
                    "List of provider slugs to try in order, for example [\"anthropic\", \"openai\"].",
                ),
            ),
        ],
        desc(
            "Vercel AI Gateway routing preferences. Controls which upstream providers the gateway routes requests to. See https://vercel.com/docs/ai-gateway/models-and-providers/provider-options.",
        ),
    )
}

/// `AnthropicAllowedFallbackModelSchema`.
#[must_use]
pub fn anthropic_allowed_fallback_model_schema() -> TSchema {
    Type::object_with(
        [
            (
                "provider",
                Type::string_with(Options::new().set("minLength", 1)),
            ),
            (
                "model",
                Type::string_with(Options::new().set("minLength", 1)),
            ),
            ("cost", model_cost_schema()),
        ],
        desc("An Anthropic server-side refusal fallback model with local pricing metadata."),
    )
}

/// `optionalCompatBoolean(options)`.
fn optional_compat_boolean(options: Options) -> TSchema {
    Type::optional(Type::boolean_with(options))
}

/// `optionalSessionAffinityFormat(options)`.
fn optional_session_affinity_format(options: Options) -> TSchema {
    Type::optional(session_affinity_format(options))
}

/// `Type.Optional(Type.Boolean(options))` written inline in the TS.
fn optional_boolean(options: Options) -> TSchema {
    Type::optional(Type::boolean_with(options))
}

#[allow(clippy::too_many_lines)] // One TS schema literal, ported property by property.
fn openai_completions_compat_properties() -> Properties {
    vec![
        (
            "supportsStore",
            optional_boolean(desc(
                "Whether the provider supports the store field. Default: auto-detected from URL.",
            )),
        ),
        (
            "supportsDeveloperRole",
            optional_compat_boolean(desc(
                "Whether the provider supports the developer role instead of system. Default: auto-detected from URL.",
            )),
        ),
        (
            "supportsReasoningEffort",
            optional_boolean(desc(
                "Whether the provider supports reasoning_effort. Default: auto-detected from URL.",
            )),
        ),
        (
            "supportsUsageInStreaming",
            optional_boolean(desc_default(
                "Whether the provider supports stream_options.include_usage for token usage in streaming responses.",
                true,
            )),
        ),
        (
            "supportsFinishReason",
            optional_boolean(desc_default(
                "Whether streamed responses include finish_reason. When false, pi infers stop or toolUse when the stream ends.",
                true,
            )),
        ),
        (
            "maxTokensField",
            Type::optional(Type::union_with(
                literals(&["max_completion_tokens", "max_tokens"]),
                desc("Which field to use for max tokens. Default: auto-detected from URL."),
            )),
        ),
        (
            "requiresToolResultName",
            optional_boolean(desc(
                "Whether tool results require the name field. Default: auto-detected from URL.",
            )),
        ),
        (
            "requiresAssistantAfterToolResult",
            optional_boolean(desc(
                "Whether a user message after tool results requires an assistant message in between. Default: auto-detected from URL.",
            )),
        ),
        (
            "requiresThinkingAsText",
            optional_boolean(desc(
                "Whether thinking blocks must be converted to text blocks with <thinking> delimiters. Default: auto-detected from URL.",
            )),
        ),
        (
            "requiresReasoningContentOnAssistantMessages",
            optional_boolean(desc(
                "Whether all replayed assistant messages must include an empty reasoning_content field when reasoning is enabled. Default: auto-detected from URL.",
            )),
        ),
        (
            "thinkingFormat",
            Type::optional(Type::union_with(
                literals(&[
                    "openai",
                    "openrouter",
                    "deepseek",
                    "together",
                    "baseten",
                    "zai",
                    "qwen",
                    "chat-template",
                    "qwen-chat-template",
                    "string-thinking",
                    "ant-ling",
                ]),
                desc(
                    "Format for reasoning or thinking parameters. When omitted, Pi auto-detects the format from the provider URL. \"openai\" uses reasoning_effort, \"openrouter\" uses reasoning.effort, \"deepseek\" uses thinking.type plus reasoning_effort when supported, \"together\" uses reasoning.enabled plus reasoning_effort when supported, \"baseten\" uses configurable chat_template_args plus reasoning_effort when supported, \"zai\" uses thinking.type, \"qwen\" uses top-level enable_thinking, \"qwen-chat-template\" uses chat_template_kwargs.enable_thinking and preserve_thinking, \"chat-template\" uses configurable chat_template_kwargs, \"string-thinking\" uses top-level thinking, and \"ant-ling\" uses reasoning.effort only when the mapped effort is non-null.",
                ),
            )),
        ),
        (
            "chatTemplateKwargs",
            Type::optional(Type::record_with(
                Type::string(),
                chat_template_kwarg_value_schema(),
                desc(
                    "Kwargs sent as chat_template_kwargs when thinkingFormat is \"chat-template\". Use $var with \"thinking.enabled\", \"thinking.effort\", or \"thinking.budget\" for pi-controlled values.",
                ),
            )),
        ),
        (
            "chatTemplateArgs",
            Type::optional(Type::record_with(
                Type::string(),
                chat_template_kwarg_value_schema(),
                desc(
                    "Arguments sent as chat_template_args when thinkingFormat is \"baseten\". Use $var with \"thinking.enabled\", \"thinking.effort\", or \"thinking.budget\" for pi-controlled values.",
                ),
            )),
        ),
        (
            "openRouterRouting",
            Type::optional(open_router_routing_schema()),
        ),
        (
            "vercelGatewayRouting",
            Type::optional(vercel_gateway_routing_schema()),
        ),
        (
            "zaiToolStream",
            optional_boolean(desc_default(
                "Whether z.ai supports top-level tool_stream for streaming tool call deltas.",
                false,
            )),
        ),
        (
            "thinkingTokenBudgetField",
            Type::optional(thinking_token_budget_field(desc(
                "Top-level request field used to cap reasoning tokens from thinkingBudgets. Reasoning and the answer share max_tokens on these endpoints. \"thinking_token_budget\" is vLLM, \"thinking_budget\" is Qwen, DashScope, or SGLang, and \"thinking_budget_tokens\" is llama.cpp. Off by default and not set on the generated catalog.",
            ))),
        ),
        (
            "supportsThinkingTokenBudget",
            optional_boolean(desc_default(
                "Alias for thinkingTokenBudgetField: \"thinking_token_budget\" (vLLM). Prefer thinkingTokenBudgetField.",
                false,
            )),
        ),
        (
            "supportsOpenAIGrammarTools",
            optional_compat_boolean(desc_default(
                "Whether the provider supports OpenAI custom tools with Lark or regex grammar formats. When false, grammar-constrained tools fall back to normal function tools. The generated catalog enables this for capable models.",
                false,
            )),
        ),
        (
            "supportsMidConvoSystemMessages",
            optional_compat_boolean(desc_default(
                "Whether the exact model accepts system or developer messages after the conversation has started. When false, later system messages are folded into the leading system message. The generated catalog enables this for verified models.",
                false,
            )),
        ),
        (
            "supportsMidConvoToolAdditions",
            optional_boolean(desc_default(
                "Whether system messages can introduce additional tools mid-conversation. Requires supportsMidConvoSystemMessages. The generated catalog enables this for capable models.",
                false,
            )),
        ),
        (
            "supportsStrictMode",
            optional_compat_boolean(desc_default(
                "Whether the provider supports the strict field in tool definitions. Generated capable models enable it explicitly.",
                false,
            )),
        ),
        (
            "cacheControlFormat",
            Type::optional(Type::literal_with(
                "anthropic",
                desc(
                    "Cache control convention for prompt caching. Anthropic applies cache_control markers to the system prompt, last tool definition, and last user, assistant, or tool-result text content.",
                ),
            )),
        ),
        (
            "sendSessionAffinityHeaders",
            optional_compat_boolean(desc(
                "Whether to send session-affinity data from options.sessionId. Default: true for OpenRouter endpoints, false otherwise.",
            )),
        ),
        (
            "sessionAffinityFormat",
            optional_session_affinity_format(desc(
                "Session-affinity header format. openai sends session_id, x-client-request-id, and x-session-affinity; openai-nosession sends x-client-request-id and x-session-affinity; openrouter sends x-session-id. Does not affect prompt_cache_key. Default: auto-detected.",
            )),
        ),
        (
            "supportsLongCacheRetention",
            optional_compat_boolean(desc(
                "Whether the provider supports long prompt cache retention (prompt_cache_retention: \"24h\" or Anthropic-style cache_control.ttl: \"1h\", depending on format). Default: auto-detected from provider and URL.",
            )),
        ),
        (
            "vllmPriority",
            Type::optional(Type::number_with(desc(
                "vLLM scheduler priority sent as the top-level priority request field. Lower values are handled earlier and the server default is 0. Only meaningful with --scheduling-policy priority. Off by default and not set on the generated catalog.",
            ))),
        ),
    ]
}

/// `OpenAICompletionsCompatSchema`.
#[must_use]
pub fn openai_completions_compat_schema() -> TSchema {
    Type::object_with(
        openai_completions_compat_properties(),
        compat_options(
            "Compatibility settings for OpenAI-compatible completions APIs. Use this to override URL-based auto-detection for custom providers.",
        ),
    )
}

fn openai_responses_compat_properties() -> Properties {
    vec![
        (
            "supportsDeveloperRole",
            optional_compat_boolean(desc_default(
                "Whether the provider supports the developer role instead of system.",
                true,
            )),
        ),
        (
            "supportsMidConvoSystemMessages",
            optional_compat_boolean(desc_default(
                "Whether the exact model accepts developer or system messages after the conversation has started. When false, later system messages are folded into the leading system message. The generated catalog enables this for verified models.",
                false,
            )),
        ),
        (
            "sessionAffinityFormat",
            optional_session_affinity_format(desc(
                "Session-affinity header format. openai sends session_id and x-client-request-id; openai-nosession sends x-client-request-id; openrouter sends x-session-id. Does not affect prompt_cache_key. Default: auto-detected.",
            )),
        ),
        (
            "supportsLongCacheRetention",
            optional_compat_boolean(desc_default(
                "Whether the provider supports long prompt cache retention. This uses prompt_cache_options.ttl: \"30m\" on GPT-5.6+ and prompt_cache_retention: \"24h\" on earlier models.",
                true,
            )),
        ),
        (
            "supportsStrictMode",
            optional_compat_boolean(desc(
                "Whether the provider supports strict JSON-schema function tools. Defaults are API-specific; generated OpenAI models enable it explicitly.",
            )),
        ),
        (
            "supportsOpenAIGrammarTools",
            optional_compat_boolean(desc_default(
                "Whether to emit OpenAI custom tools with Lark or regex grammar formats. When false, grammar-constrained tools fall back to normal function tools. The generated catalog enables this for capable models.",
                false,
            )),
        ),
        (
            "supportsAdditionalTools",
            optional_boolean(desc_default(
                "Whether the model supports message-anchored additional_tools input items.",
                false,
            )),
        ),
        (
            "supportsToolSearch",
            optional_boolean(desc_default(
                "Whether the model supports client-executed tool search for transcript-anchored additions.",
                false,
            )),
        ),
        (
            "supportsExplicitPromptCacheMode",
            optional_boolean(desc_default(
                "Whether the model accepts prompt_cache_options. Older OpenAI models reject the parameter.",
                false,
            )),
        ),
        (
            "supportsMaxOutputTokens",
            optional_boolean(desc_default(
                "Whether the provider accepts max_output_tokens. Some Codex-protocol gateways reject it.",
                true,
            )),
        ),
    ]
}

/// `OpenAIResponsesCompatSchema`.
#[must_use]
pub fn openai_responses_compat_schema() -> TSchema {
    Type::object_with(
        openai_responses_compat_properties(),
        compat_options("Compatibility settings for OpenAI Responses APIs."),
    )
}

fn anthropic_messages_compat_properties() -> Properties {
    vec![
        (
            "supportsEagerToolInputStreaming",
            optional_boolean(desc_default(
                "Whether the provider accepts per-tool eager_input_streaming. When false, the Anthropic provider omits tools[].eager_input_streaming and sends the legacy fine-grained-tool-streaming-2025-05-14 beta header for tool-enabled requests.",
                true,
            )),
        ),
        (
            "supportsLongCacheRetention",
            optional_compat_boolean(desc_default(
                "Whether the provider supports Anthropic long cache retention through cache_control.ttl.",
                true,
            )),
        ),
        (
            "sendSessionAffinityHeaders",
            optional_compat_boolean(desc(
                "Whether to send x-session-affinity from options.sessionId when caching is enabled. Required for providers like Fireworks that use session affinity for prompt cache routing; requests to the same replica maximize cache hits. Default: true for OpenRouter endpoints, false otherwise.",
            )),
        ),
        (
            "sessionAffinityFormat",
            Type::optional(Type::literal_with(
                "openrouter",
                desc(
                    "Session-affinity format. openrouter sends x-session-id; when unset, sends x-session-affinity.",
                ),
            )),
        ),
        (
            "supportsCacheControlOnTools",
            optional_boolean(desc_default(
                "Whether the provider supports Anthropic-style cache_control markers on tool definitions. When false, cache_control is omitted from tool parameters. Some Anthropic-compatible providers, such as Fireworks, do not support this field on tools and may reject or ignore it.",
                true,
            )),
        ),
        (
            "supportsTemperature",
            optional_boolean(desc_default(
                "Whether the model accepts the Anthropic temperature request field. Claude Opus 4.7+ rejects non-default values.",
                true,
            )),
        ),
        (
            "forceAdaptiveThinking",
            optional_boolean(desc_default(
                "Whether to force adaptive thinking (thinking.type: adaptive plus output_config.effort) regardless of model ID. Built-in models that require adaptive thinking set this in generated metadata. Custom Anthropic-compatible providers can set this to true for any model whose upstream requires the adaptive format. Set false to opt out on overridden built-in models.",
                false,
            )),
        ),
        (
            "allowEmptySignature",
            optional_boolean(desc_default(
                "Whether to replay empty thinking signatures instead of converting thinking to text.",
                false,
            )),
        ),
        (
            "supportsStrictTools",
            optional_boolean(desc_default(
                "Whether the provider supports Anthropic strict tool schemas. Generated Anthropic models enable it explicitly.",
                false,
            )),
        ),
        (
            "supportsMidConvoEffort",
            optional_boolean(desc_default(
                "Whether the exact model transport supports effort-only system messages and thinking binding controls.",
                false,
            )),
        ),
        (
            "supportsMidConvoSystemMessages",
            optional_compat_boolean(desc_default(
                "Whether the exact model accepts system-role messages inside the conversation. When false, later system messages are folded into the top-level system prompt.",
                false,
            )),
        ),
        (
            "supportsMidConvoToolChanges",
            optional_boolean(desc_default(
                "Whether the exact model accepts mid-conversation tool_addition and tool_removal blocks. Requires supportsMidConvoSystemMessages.",
                false,
            )),
        ),
        (
            "allowedFallbackModels",
            Type::optional(Type::array_with(
                anthropic_allowed_fallback_model_schema(),
                Options::new().set("maxItems", 3).set(
                    "description",
                    "Models Anthropic accepts for server-side refusal fallback, with local pricing metadata for returned fallback responses. When absent or empty, callers must omit fallbacks; Anthropic rejects the field for models with no permitted fallback targets.",
                ),
            )),
        ),
    ]
}

/// `AnthropicMessagesCompatSchema`.
#[must_use]
pub fn anthropic_messages_compat_schema() -> TSchema {
    Type::object_with(
        anthropic_messages_compat_properties(),
        compat_options("Compatibility settings for Anthropic Messages-compatible APIs."),
    )
}

fn bedrock_compat_properties() -> Properties {
    vec![(
        "supportsStrictMode",
        optional_compat_boolean(desc_default(
            "Whether the model supports Bedrock strict tool schemas.",
            false,
        )),
    )]
}

/// `BedrockCompatSchema`.
#[must_use]
pub fn bedrock_compat_schema() -> TSchema {
    Type::object_with(
        bedrock_compat_properties(),
        compat_options("Compatibility settings for Amazon Bedrock models."),
    )
}

fn mistral_conversations_compat_properties() -> Properties {
    vec![(
        "supportsMidConvoSystemMessages",
        optional_compat_boolean(desc_default(
            "Whether the exact model accepts system messages after the conversation has started. When false, later system messages are folded into the leading system message.",
            false,
        )),
    )]
}

/// `MistralConversationsCompatSchema`.
#[must_use]
pub fn mistral_conversations_compat_schema() -> TSchema {
    Type::object_with(
        mistral_conversations_compat_properties(),
        compat_options("Compatibility settings for the Mistral chat API."),
    )
}

/// `ProviderCompatPropertyOverrides`.
fn provider_compat_property_overrides() -> Properties {
    vec![
        (
            "supportsDeveloperRole",
            optional_compat_boolean(desc(
                "Whether the provider supports the developer role instead of system. Defaults are API-specific.",
            )),
        ),
        (
            "supportsMidConvoSystemMessages",
            optional_compat_boolean(desc_default(
                "Whether the exact model accepts system or developer messages after the conversation has started. When false, later system messages are folded into the leading system message.",
                false,
            )),
        ),
        (
            "sessionAffinityFormat",
            optional_session_affinity_format(desc(
                "Session-affinity header format. Defaults are API-specific or auto-detected.",
            )),
        ),
        (
            "supportsLongCacheRetention",
            optional_compat_boolean(desc(
                "Whether the provider supports long prompt cache retention. Defaults are API-specific or auto-detected.",
            )),
        ),
        (
            "supportsStrictMode",
            optional_compat_boolean(desc(
                "Whether the provider supports strict tool schemas. Defaults are API-specific.",
            )),
        ),
        (
            "supportsOpenAIGrammarTools",
            optional_compat_boolean(desc_default(
                "Whether the provider supports OpenAI custom tools with Lark or regex grammar formats. When false, grammar-constrained tools fall back to normal function tools.",
                false,
            )),
        ),
        (
            "sendSessionAffinityHeaders",
            optional_compat_boolean(desc(
                "Whether to send session-affinity data from options.sessionId. Defaults are API-specific.",
            )),
        ),
    ]
}

/// `mergeCompatProperties(propertyGroups, overrides)`.
///
/// Provider-level models.json compatibility is API-agnostic, so it needs one superset. Every
/// duplicate property requires explicit generic metadata, while API-specific schemas retain their
/// own defaults and descriptions.
///
/// # Panics
///
/// When a duplicate property has no override, or an override resolves no duplicate (the TS
/// throws at module load).
fn merge_compat_properties(property_groups: Vec<Properties>, overrides: Properties) -> Properties {
    let mut merged: Properties = Vec::new();
    let mut duplicate_names: Vec<&'static str> = Vec::new();
    let has_override = |name: &str| overrides.iter().any(|(key, _)| *key == name);

    for properties in property_groups {
        for (name, schema) in properties {
            if let Some((_, slot)) = merged.iter_mut().find(|(key, _)| *key == name) {
                if !duplicate_names.contains(&name) {
                    duplicate_names.push(name);
                }
                assert!(
                    has_override(name),
                    "Duplicate compatibility schema property requires an override: {name}"
                );
                *slot = schema;
            } else {
                merged.push((name, schema));
            }
        }
    }

    for (name, _) in &overrides {
        assert!(
            duplicate_names.contains(name),
            "Compatibility schema override does not resolve a duplicate property: {name}"
        );
    }

    // `{ ...merged, ...overrides }`: every override names an existing key, so it keeps its slot.
    for (name, schema) in overrides {
        if let Some((_, slot)) = merged.iter_mut().find(|(key, _)| *key == name) {
            *slot = schema;
        } else {
            merged.push((name, schema));
        }
    }
    merged
}

/// `ProviderCompatSchema`.
#[must_use]
pub fn provider_compat_schema() -> TSchema {
    // `CompatSchemasByApi` order: openai-completions, openai-responses, anthropic-messages,
    // bedrock-converse-stream, mistral-conversations.
    let properties = merge_compat_properties(
        vec![
            openai_completions_compat_properties(),
            openai_responses_compat_properties(),
            anthropic_messages_compat_properties(),
            bedrock_compat_properties(),
            mistral_conversations_compat_properties(),
        ],
        provider_compat_property_overrides(),
    );
    Type::object_with(
        properties,
        compat_options("Provider and model compatibility overrides."),
    )
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    /// `Compile(schema).Default({})`: each top-level property's `default`.
    fn default_of(schema: &TSchema, name: &str) -> Option<JsonValue> {
        schema.json()["properties"][name].get("default").cloned()
    }

    #[test]
    fn preserves_property_types_in_the_provider_superset() {
        let schema = provider_compat_schema();
        assert!(schema.json().get("required").is_none());
        assert_eq!(
            schema.json()["properties"]["supportsStore"]["type"],
            json!("boolean")
        );
        assert_eq!(
            schema.json()["properties"]["sessionAffinityFormat"]["anyOf"],
            json!([
                { "type": "string", "const": "openai" },
                { "type": "string", "const": "openai-nosession" },
                { "type": "string", "const": "openrouter" }
            ])
        );
    }

    #[test]
    fn preserves_api_specific_defaults() {
        let completions = openai_completions_compat_schema();
        assert_eq!(default_of(&completions, "thinkingFormat"), None);
        assert_eq!(default_of(&completions, "supportsLongCacheRetention"), None);
        assert_eq!(
            default_of(&openai_responses_compat_schema(), "supportsDeveloperRole"),
            Some(json!(true))
        );
        let anthropic = anthropic_messages_compat_schema();
        assert_eq!(default_of(&anthropic, "sendSessionAffinityHeaders"), None);
        assert_eq!(
            default_of(&anthropic, "supportsLongCacheRetention"),
            Some(json!(true))
        );
        assert_eq!(
            default_of(&bedrock_compat_schema(), "supportsStrictMode"),
            Some(json!(false))
        );
    }

    #[test]
    fn does_not_assign_api_specific_defaults_to_the_provider_superset() {
        let schema = provider_compat_schema();
        for name in [
            "supportsDeveloperRole",
            "sendSessionAffinityHeaders",
            "supportsLongCacheRetention",
            "supportsStrictMode",
        ] {
            assert_eq!(default_of(&schema, name), None, "{name}");
        }
    }
}
