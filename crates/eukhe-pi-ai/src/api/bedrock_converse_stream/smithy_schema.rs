//! The Smithy shapes of `ConverseStream` (request body and response events),
//! generated from the schemas of `@aws-sdk/client-bedrock-runtime` 3.1127.0
//! (`ConverseStreamRequest$`, `ConverseStreamResponse$`). Member order is the
//! schema order, which is the order the SDK serializes and deserializes in.
//! HTTP-bound members (`modelId`, the label in the path) are omitted.
//!
//! Generated; do not edit by hand.

use super::shape_codec::{Shape, StructShape};

/// `ConverseStreamRequest` (body members).
pub(super) static REQUEST: &StructShape = &CONVERSE_STREAM_REQUEST;

/// `ConverseStreamOutput` (the event-stream union).
pub(super) static STREAM_OUTPUT: &StructShape = &CONVERSE_STREAM_OUTPUT;

static CONVERSE_STREAM_REQUEST: StructShape = StructShape {
    name: "ConverseStreamRequest",
    members: &[
        ("messages", Shape::List(&Shape::Struct(&MESSAGE))),
        ("system", Shape::List(&Shape::Union(&SYSTEM_CONTENT_BLOCK))),
        ("inferenceConfig", Shape::Struct(&INFERENCE_CONFIGURATION)),
        ("toolConfig", Shape::Struct(&TOOL_CONFIGURATION)),
        (
            "guardrailConfig",
            Shape::Struct(&GUARDRAIL_STREAM_CONFIGURATION),
        ),
        ("additionalModelRequestFields", Shape::Document),
        (
            "promptVariables",
            Shape::Map(&Shape::Union(&PROMPT_VARIABLE_VALUES)),
        ),
        (
            "additionalModelResponseFieldPaths",
            Shape::List(&Shape::String),
        ),
        ("requestMetadata", Shape::Map(&Shape::String)),
        (
            "performanceConfig",
            Shape::Struct(&PERFORMANCE_CONFIGURATION),
        ),
        ("serviceTier", Shape::Struct(&SERVICE_TIER)),
        ("outputConfig", Shape::Struct(&OUTPUT_CONFIG)),
    ],
};

static MESSAGE: StructShape = StructShape {
    name: "Message",
    members: &[
        ("role", Shape::String),
        ("content", Shape::List(&Shape::Union(&CONTENT_BLOCK))),
    ],
};

static CONTENT_BLOCK: StructShape = StructShape {
    name: "ContentBlock",
    members: &[
        ("text", Shape::String),
        ("image", Shape::Struct(&IMAGE_BLOCK)),
        ("document", Shape::Struct(&DOCUMENT_BLOCK)),
        ("video", Shape::Struct(&VIDEO_BLOCK)),
        ("audio", Shape::Struct(&AUDIO_BLOCK)),
        ("toolUse", Shape::Struct(&TOOL_USE_BLOCK)),
        ("toolResult", Shape::Struct(&TOOL_RESULT_BLOCK)),
        (
            "guardContent",
            Shape::Union(&GUARDRAIL_CONVERSE_CONTENT_BLOCK),
        ),
        ("cachePoint", Shape::Struct(&CACHE_POINT_BLOCK)),
        ("reasoningContent", Shape::Union(&REASONING_CONTENT_BLOCK)),
        ("citationsContent", Shape::Struct(&CITATIONS_CONTENT_BLOCK)),
        ("searchResult", Shape::Struct(&SEARCH_RESULT_BLOCK)),
        ("toolAddition", Shape::Struct(&TOOL_ADDITION_BLOCK)),
        ("toolRemoval", Shape::Struct(&TOOL_REMOVAL_BLOCK)),
    ],
};

static IMAGE_BLOCK: StructShape = StructShape {
    name: "ImageBlock",
    members: &[
        ("format", Shape::String),
        ("source", Shape::Union(&IMAGE_SOURCE)),
        ("error", Shape::Struct(&ERROR_BLOCK)),
    ],
};

static IMAGE_SOURCE: StructShape = StructShape {
    name: "ImageSource",
    members: &[
        ("bytes", Shape::Blob),
        ("s3Location", Shape::Struct(&S3_LOCATION)),
    ],
};

static S3_LOCATION: StructShape = StructShape {
    name: "S3Location",
    members: &[("uri", Shape::String), ("bucketOwner", Shape::String)],
};

static ERROR_BLOCK: StructShape = StructShape {
    name: "ErrorBlock",
    members: &[("message", Shape::String)],
};

static DOCUMENT_BLOCK: StructShape = StructShape {
    name: "DocumentBlock",
    members: &[
        ("name", Shape::String),
        ("source", Shape::Union(&DOCUMENT_SOURCE)),
        ("format", Shape::String),
        ("context", Shape::String),
        ("citations", Shape::Struct(&CITATIONS_CONFIG)),
    ],
};

static DOCUMENT_SOURCE: StructShape = StructShape {
    name: "DocumentSource",
    members: &[
        ("bytes", Shape::Blob),
        ("s3Location", Shape::Struct(&S3_LOCATION)),
        ("text", Shape::String),
        (
            "content",
            Shape::List(&Shape::Union(&DOCUMENT_CONTENT_BLOCK)),
        ),
    ],
};

static DOCUMENT_CONTENT_BLOCK: StructShape = StructShape {
    name: "DocumentContentBlock",
    members: &[("text", Shape::String)],
};

static CITATIONS_CONFIG: StructShape = StructShape {
    name: "CitationsConfig",
    members: &[("enabled", Shape::Boolean)],
};

static VIDEO_BLOCK: StructShape = StructShape {
    name: "VideoBlock",
    members: &[
        ("format", Shape::String),
        ("source", Shape::Union(&VIDEO_SOURCE)),
    ],
};

static VIDEO_SOURCE: StructShape = StructShape {
    name: "VideoSource",
    members: &[
        ("bytes", Shape::Blob),
        ("s3Location", Shape::Struct(&S3_LOCATION)),
    ],
};

static AUDIO_BLOCK: StructShape = StructShape {
    name: "AudioBlock",
    members: &[
        ("format", Shape::String),
        ("source", Shape::Union(&AUDIO_SOURCE)),
        ("error", Shape::Struct(&ERROR_BLOCK)),
    ],
};

static AUDIO_SOURCE: StructShape = StructShape {
    name: "AudioSource",
    members: &[
        ("bytes", Shape::Blob),
        ("s3Location", Shape::Struct(&S3_LOCATION)),
    ],
};

static TOOL_USE_BLOCK: StructShape = StructShape {
    name: "ToolUseBlock",
    members: &[
        ("toolUseId", Shape::String),
        ("name", Shape::String),
        ("input", Shape::Document),
        ("type", Shape::String),
    ],
};

static TOOL_RESULT_BLOCK: StructShape = StructShape {
    name: "ToolResultBlock",
    members: &[
        ("toolUseId", Shape::String),
        (
            "content",
            Shape::List(&Shape::Union(&TOOL_RESULT_CONTENT_BLOCK)),
        ),
        ("status", Shape::String),
        ("type", Shape::String),
    ],
};

static TOOL_RESULT_CONTENT_BLOCK: StructShape = StructShape {
    name: "ToolResultContentBlock",
    members: &[
        ("json", Shape::Document),
        ("text", Shape::String),
        ("image", Shape::Struct(&IMAGE_BLOCK)),
        ("document", Shape::Struct(&DOCUMENT_BLOCK)),
        ("video", Shape::Struct(&VIDEO_BLOCK)),
        ("searchResult", Shape::Struct(&SEARCH_RESULT_BLOCK)),
    ],
};

static SEARCH_RESULT_BLOCK: StructShape = StructShape {
    name: "SearchResultBlock",
    members: &[
        ("source", Shape::String),
        ("title", Shape::String),
        (
            "content",
            Shape::List(&Shape::Struct(&SEARCH_RESULT_CONTENT_BLOCK)),
        ),
        ("citations", Shape::Struct(&CITATIONS_CONFIG)),
    ],
};

static SEARCH_RESULT_CONTENT_BLOCK: StructShape = StructShape {
    name: "SearchResultContentBlock",
    members: &[("text", Shape::String)],
};

static GUARDRAIL_CONVERSE_CONTENT_BLOCK: StructShape = StructShape {
    name: "GuardrailConverseContentBlock",
    members: &[
        ("text", Shape::Struct(&GUARDRAIL_CONVERSE_TEXT_BLOCK)),
        ("image", Shape::Struct(&GUARDRAIL_CONVERSE_IMAGE_BLOCK)),
    ],
};

static GUARDRAIL_CONVERSE_TEXT_BLOCK: StructShape = StructShape {
    name: "GuardrailConverseTextBlock",
    members: &[
        ("text", Shape::String),
        ("qualifiers", Shape::List(&Shape::String)),
    ],
};

static GUARDRAIL_CONVERSE_IMAGE_BLOCK: StructShape = StructShape {
    name: "GuardrailConverseImageBlock",
    members: &[
        ("format", Shape::String),
        ("source", Shape::Union(&GUARDRAIL_CONVERSE_IMAGE_SOURCE)),
    ],
};

static GUARDRAIL_CONVERSE_IMAGE_SOURCE: StructShape = StructShape {
    name: "GuardrailConverseImageSource",
    members: &[("bytes", Shape::Blob)],
};

static CACHE_POINT_BLOCK: StructShape = StructShape {
    name: "CachePointBlock",
    members: &[("type", Shape::String), ("ttl", Shape::String)],
};

static REASONING_CONTENT_BLOCK: StructShape = StructShape {
    name: "ReasoningContentBlock",
    members: &[
        ("reasoningText", Shape::Struct(&REASONING_TEXT_BLOCK)),
        ("redactedContent", Shape::Blob),
    ],
};

static REASONING_TEXT_BLOCK: StructShape = StructShape {
    name: "ReasoningTextBlock",
    members: &[("text", Shape::String), ("signature", Shape::String)],
};

static CITATIONS_CONTENT_BLOCK: StructShape = StructShape {
    name: "CitationsContentBlock",
    members: &[
        (
            "content",
            Shape::List(&Shape::Union(&CITATION_GENERATED_CONTENT)),
        ),
        ("citations", Shape::List(&Shape::Struct(&CITATION))),
    ],
};

static CITATION_GENERATED_CONTENT: StructShape = StructShape {
    name: "CitationGeneratedContent",
    members: &[("text", Shape::String)],
};

static CITATION: StructShape = StructShape {
    name: "Citation",
    members: &[
        ("title", Shape::String),
        ("source", Shape::String),
        (
            "sourceContent",
            Shape::List(&Shape::Union(&CITATION_SOURCE_CONTENT)),
        ),
        ("location", Shape::Union(&CITATION_LOCATION)),
    ],
};

static CITATION_SOURCE_CONTENT: StructShape = StructShape {
    name: "CitationSourceContent",
    members: &[("text", Shape::String)],
};

static CITATION_LOCATION: StructShape = StructShape {
    name: "CitationLocation",
    members: &[
        ("web", Shape::Struct(&WEB_LOCATION)),
        ("documentChar", Shape::Struct(&DOCUMENT_CHAR_LOCATION)),
        ("documentPage", Shape::Struct(&DOCUMENT_PAGE_LOCATION)),
        ("documentChunk", Shape::Struct(&DOCUMENT_CHUNK_LOCATION)),
        (
            "searchResultLocation",
            Shape::Struct(&SEARCH_RESULT_LOCATION),
        ),
    ],
};

static WEB_LOCATION: StructShape = StructShape {
    name: "WebLocation",
    members: &[("url", Shape::String), ("domain", Shape::String)],
};

static DOCUMENT_CHAR_LOCATION: StructShape = StructShape {
    name: "DocumentCharLocation",
    members: &[
        ("documentIndex", Shape::Number),
        ("start", Shape::Number),
        ("end", Shape::Number),
    ],
};

static DOCUMENT_PAGE_LOCATION: StructShape = StructShape {
    name: "DocumentPageLocation",
    members: &[
        ("documentIndex", Shape::Number),
        ("start", Shape::Number),
        ("end", Shape::Number),
    ],
};

static DOCUMENT_CHUNK_LOCATION: StructShape = StructShape {
    name: "DocumentChunkLocation",
    members: &[
        ("documentIndex", Shape::Number),
        ("start", Shape::Number),
        ("end", Shape::Number),
    ],
};

static SEARCH_RESULT_LOCATION: StructShape = StructShape {
    name: "SearchResultLocation",
    members: &[
        ("searchResultIndex", Shape::Number),
        ("start", Shape::Number),
        ("end", Shape::Number),
    ],
};

static TOOL_ADDITION_BLOCK: StructShape = StructShape {
    name: "ToolAdditionBlock",
    members: &[("tool", Shape::Struct(&TOOL_REFERENCE))],
};

static TOOL_REFERENCE: StructShape = StructShape {
    name: "ToolReference",
    members: &[
        ("type", Shape::String),
        ("name", Shape::String),
        ("serverName", Shape::String),
    ],
};

static TOOL_REMOVAL_BLOCK: StructShape = StructShape {
    name: "ToolRemovalBlock",
    members: &[("tool", Shape::Struct(&TOOL_REFERENCE))],
};

static SYSTEM_CONTENT_BLOCK: StructShape = StructShape {
    name: "SystemContentBlock",
    members: &[
        ("text", Shape::String),
        (
            "guardContent",
            Shape::Union(&GUARDRAIL_CONVERSE_CONTENT_BLOCK),
        ),
        ("cachePoint", Shape::Struct(&CACHE_POINT_BLOCK)),
    ],
};

static INFERENCE_CONFIGURATION: StructShape = StructShape {
    name: "InferenceConfiguration",
    members: &[
        ("maxTokens", Shape::Number),
        ("temperature", Shape::Number),
        ("topP", Shape::Number),
        ("stopSequences", Shape::List(&Shape::String)),
    ],
};

static TOOL_CONFIGURATION: StructShape = StructShape {
    name: "ToolConfiguration",
    members: &[
        ("tools", Shape::List(&Shape::Union(&TOOL))),
        ("toolChoice", Shape::Union(&TOOL_CHOICE)),
    ],
};

static TOOL: StructShape = StructShape {
    name: "Tool",
    members: &[
        ("toolSpec", Shape::Struct(&TOOL_SPECIFICATION)),
        ("systemTool", Shape::Struct(&SYSTEM_TOOL)),
        ("cachePoint", Shape::Struct(&CACHE_POINT_BLOCK)),
    ],
};

static TOOL_SPECIFICATION: StructShape = StructShape {
    name: "ToolSpecification",
    members: &[
        ("name", Shape::String),
        ("inputSchema", Shape::Union(&TOOL_INPUT_SCHEMA)),
        ("description", Shape::String),
        ("strict", Shape::Boolean),
    ],
};

static TOOL_INPUT_SCHEMA: StructShape = StructShape {
    name: "ToolInputSchema",
    members: &[("json", Shape::Document)],
};

static SYSTEM_TOOL: StructShape = StructShape {
    name: "SystemTool",
    members: &[("name", Shape::String)],
};

static TOOL_CHOICE: StructShape = StructShape {
    name: "ToolChoice",
    members: &[
        ("auto", Shape::Struct(&AUTO_TOOL_CHOICE)),
        ("any", Shape::Struct(&ANY_TOOL_CHOICE)),
        ("tool", Shape::Struct(&SPECIFIC_TOOL_CHOICE)),
    ],
};

static AUTO_TOOL_CHOICE: StructShape = StructShape {
    name: "AutoToolChoice",
    members: &[],
};

static ANY_TOOL_CHOICE: StructShape = StructShape {
    name: "AnyToolChoice",
    members: &[],
};

static SPECIFIC_TOOL_CHOICE: StructShape = StructShape {
    name: "SpecificToolChoice",
    members: &[("name", Shape::String)],
};

static GUARDRAIL_STREAM_CONFIGURATION: StructShape = StructShape {
    name: "GuardrailStreamConfiguration",
    members: &[
        ("guardrailIdentifier", Shape::String),
        ("guardrailVersion", Shape::String),
        ("trace", Shape::String),
        ("streamProcessingMode", Shape::String),
    ],
};

static PROMPT_VARIABLE_VALUES: StructShape = StructShape {
    name: "PromptVariableValues",
    members: &[("text", Shape::String)],
};

static PERFORMANCE_CONFIGURATION: StructShape = StructShape {
    name: "PerformanceConfiguration",
    members: &[("latency", Shape::String)],
};

static SERVICE_TIER: StructShape = StructShape {
    name: "ServiceTier",
    members: &[("type", Shape::String)],
};

static OUTPUT_CONFIG: StructShape = StructShape {
    name: "OutputConfig",
    members: &[
        ("textFormat", Shape::Struct(&OUTPUT_FORMAT)),
        ("effort", Shape::String),
    ],
};

static OUTPUT_FORMAT: StructShape = StructShape {
    name: "OutputFormat",
    members: &[
        ("type", Shape::String),
        ("structure", Shape::Union(&OUTPUT_FORMAT_STRUCTURE)),
    ],
};

static OUTPUT_FORMAT_STRUCTURE: StructShape = StructShape {
    name: "OutputFormatStructure",
    members: &[("jsonSchema", Shape::Struct(&JSON_SCHEMA_DEFINITION))],
};

static JSON_SCHEMA_DEFINITION: StructShape = StructShape {
    name: "JsonSchemaDefinition",
    members: &[
        ("schema", Shape::String),
        ("name", Shape::String),
        ("description", Shape::String),
    ],
};

static CONVERSE_STREAM_OUTPUT: StructShape = StructShape {
    name: "ConverseStreamOutput",
    members: &[
        ("messageStart", Shape::Struct(&MESSAGE_START_EVENT)),
        (
            "contentBlockStart",
            Shape::Struct(&CONTENT_BLOCK_START_EVENT),
        ),
        (
            "contentBlockDelta",
            Shape::Struct(&CONTENT_BLOCK_DELTA_EVENT),
        ),
        ("contentBlockStop", Shape::Struct(&CONTENT_BLOCK_STOP_EVENT)),
        ("messageStop", Shape::Struct(&MESSAGE_STOP_EVENT)),
        ("metadata", Shape::Struct(&CONVERSE_STREAM_METADATA_EVENT)),
        (
            "internalServerException",
            Shape::Struct(&INTERNAL_SERVER_EXCEPTION),
        ),
        (
            "modelStreamErrorException",
            Shape::Struct(&MODEL_STREAM_ERROR_EXCEPTION),
        ),
        ("validationException", Shape::Struct(&VALIDATION_EXCEPTION)),
        ("throttlingException", Shape::Struct(&THROTTLING_EXCEPTION)),
        (
            "serviceUnavailableException",
            Shape::Struct(&SERVICE_UNAVAILABLE_EXCEPTION),
        ),
    ],
};

static MESSAGE_START_EVENT: StructShape = StructShape {
    name: "MessageStartEvent",
    members: &[("role", Shape::String)],
};

static CONTENT_BLOCK_START_EVENT: StructShape = StructShape {
    name: "ContentBlockStartEvent",
    members: &[
        ("start", Shape::Union(&CONTENT_BLOCK_START)),
        ("contentBlockIndex", Shape::Number),
    ],
};

static CONTENT_BLOCK_START: StructShape = StructShape {
    name: "ContentBlockStart",
    members: &[
        ("toolUse", Shape::Struct(&TOOL_USE_BLOCK_START)),
        ("toolResult", Shape::Struct(&TOOL_RESULT_BLOCK_START)),
        ("image", Shape::Struct(&IMAGE_BLOCK_START)),
    ],
};

static TOOL_USE_BLOCK_START: StructShape = StructShape {
    name: "ToolUseBlockStart",
    members: &[
        ("toolUseId", Shape::String),
        ("name", Shape::String),
        ("type", Shape::String),
    ],
};

static TOOL_RESULT_BLOCK_START: StructShape = StructShape {
    name: "ToolResultBlockStart",
    members: &[
        ("toolUseId", Shape::String),
        ("type", Shape::String),
        ("status", Shape::String),
    ],
};

static IMAGE_BLOCK_START: StructShape = StructShape {
    name: "ImageBlockStart",
    members: &[("format", Shape::String)],
};

static CONTENT_BLOCK_DELTA_EVENT: StructShape = StructShape {
    name: "ContentBlockDeltaEvent",
    members: &[
        ("delta", Shape::Union(&CONTENT_BLOCK_DELTA)),
        ("contentBlockIndex", Shape::Number),
    ],
};

static CONTENT_BLOCK_DELTA: StructShape = StructShape {
    name: "ContentBlockDelta",
    members: &[
        ("text", Shape::String),
        ("toolUse", Shape::Struct(&TOOL_USE_BLOCK_DELTA)),
        (
            "toolResult",
            Shape::List(&Shape::Union(&TOOL_RESULT_BLOCK_DELTA)),
        ),
        (
            "reasoningContent",
            Shape::Union(&REASONING_CONTENT_BLOCK_DELTA),
        ),
        ("citation", Shape::Struct(&CITATIONS_DELTA)),
        ("image", Shape::Struct(&IMAGE_BLOCK_DELTA)),
    ],
};

static TOOL_USE_BLOCK_DELTA: StructShape = StructShape {
    name: "ToolUseBlockDelta",
    members: &[("input", Shape::String)],
};

static TOOL_RESULT_BLOCK_DELTA: StructShape = StructShape {
    name: "ToolResultBlockDelta",
    members: &[("text", Shape::String), ("json", Shape::Document)],
};

static REASONING_CONTENT_BLOCK_DELTA: StructShape = StructShape {
    name: "ReasoningContentBlockDelta",
    members: &[
        ("text", Shape::String),
        ("redactedContent", Shape::Blob),
        ("signature", Shape::String),
    ],
};

static CITATIONS_DELTA: StructShape = StructShape {
    name: "CitationsDelta",
    members: &[
        ("title", Shape::String),
        ("source", Shape::String),
        (
            "sourceContent",
            Shape::List(&Shape::Struct(&CITATION_SOURCE_CONTENT_DELTA)),
        ),
        ("location", Shape::Union(&CITATION_LOCATION)),
    ],
};

static CITATION_SOURCE_CONTENT_DELTA: StructShape = StructShape {
    name: "CitationSourceContentDelta",
    members: &[("text", Shape::String)],
};

static IMAGE_BLOCK_DELTA: StructShape = StructShape {
    name: "ImageBlockDelta",
    members: &[
        ("source", Shape::Union(&IMAGE_SOURCE)),
        ("error", Shape::Struct(&ERROR_BLOCK)),
    ],
};

static CONTENT_BLOCK_STOP_EVENT: StructShape = StructShape {
    name: "ContentBlockStopEvent",
    members: &[("contentBlockIndex", Shape::Number)],
};

static MESSAGE_STOP_EVENT: StructShape = StructShape {
    name: "MessageStopEvent",
    members: &[
        ("stopReason", Shape::String),
        ("additionalModelResponseFields", Shape::Document),
    ],
};

static CONVERSE_STREAM_METADATA_EVENT: StructShape = StructShape {
    name: "ConverseStreamMetadataEvent",
    members: &[
        ("usage", Shape::Struct(&TOKEN_USAGE)),
        ("metrics", Shape::Struct(&CONVERSE_STREAM_METRICS)),
        ("trace", Shape::Struct(&CONVERSE_STREAM_TRACE)),
        (
            "performanceConfig",
            Shape::Struct(&PERFORMANCE_CONFIGURATION),
        ),
        ("serviceTier", Shape::Struct(&SERVICE_TIER)),
    ],
};

static TOKEN_USAGE: StructShape = StructShape {
    name: "TokenUsage",
    members: &[
        ("inputTokens", Shape::Number),
        ("outputTokens", Shape::Number),
        ("totalTokens", Shape::Number),
        ("cacheReadInputTokens", Shape::Number),
        ("cacheWriteInputTokens", Shape::Number),
        ("cacheDetails", Shape::List(&Shape::Struct(&CACHE_DETAIL))),
    ],
};

static CACHE_DETAIL: StructShape = StructShape {
    name: "CacheDetail",
    members: &[("ttl", Shape::String), ("inputTokens", Shape::Number)],
};

static CONVERSE_STREAM_METRICS: StructShape = StructShape {
    name: "ConverseStreamMetrics",
    members: &[("latencyMs", Shape::Number)],
};

static CONVERSE_STREAM_TRACE: StructShape = StructShape {
    name: "ConverseStreamTrace",
    members: &[
        ("guardrail", Shape::Struct(&GUARDRAIL_TRACE_ASSESSMENT)),
        ("promptRouter", Shape::Struct(&PROMPT_ROUTER_TRACE)),
    ],
};

static GUARDRAIL_TRACE_ASSESSMENT: StructShape = StructShape {
    name: "GuardrailTraceAssessment",
    members: &[
        ("modelOutput", Shape::List(&Shape::String)),
        (
            "inputAssessment",
            Shape::Map(&Shape::Struct(&GUARDRAIL_ASSESSMENT)),
        ),
        (
            "outputAssessments",
            Shape::Map(&Shape::List(&Shape::Struct(&GUARDRAIL_ASSESSMENT))),
        ),
        ("actionReason", Shape::String),
    ],
};

static GUARDRAIL_ASSESSMENT: StructShape = StructShape {
    name: "GuardrailAssessment",
    members: &[
        (
            "topicPolicy",
            Shape::Struct(&GUARDRAIL_TOPIC_POLICY_ASSESSMENT),
        ),
        (
            "contentPolicy",
            Shape::Struct(&GUARDRAIL_CONTENT_POLICY_ASSESSMENT),
        ),
        (
            "wordPolicy",
            Shape::Struct(&GUARDRAIL_WORD_POLICY_ASSESSMENT),
        ),
        (
            "sensitiveInformationPolicy",
            Shape::Struct(&GUARDRAIL_SENSITIVE_INFORMATION_POLICY_ASSESSMENT),
        ),
        (
            "contextualGroundingPolicy",
            Shape::Struct(&GUARDRAIL_CONTEXTUAL_GROUNDING_POLICY_ASSESSMENT),
        ),
        (
            "automatedReasoningPolicy",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_POLICY_ASSESSMENT),
        ),
        (
            "invocationMetrics",
            Shape::Struct(&GUARDRAIL_INVOCATION_METRICS),
        ),
        (
            "appliedGuardrailDetails",
            Shape::Struct(&APPLIED_GUARDRAIL_DETAILS),
        ),
    ],
};

static GUARDRAIL_TOPIC_POLICY_ASSESSMENT: StructShape = StructShape {
    name: "GuardrailTopicPolicyAssessment",
    members: &[("topics", Shape::List(&Shape::Struct(&GUARDRAIL_TOPIC)))],
};

static GUARDRAIL_TOPIC: StructShape = StructShape {
    name: "GuardrailTopic",
    members: &[
        ("name", Shape::String),
        ("type", Shape::String),
        ("action", Shape::String),
        ("detected", Shape::Boolean),
    ],
};

static GUARDRAIL_CONTENT_POLICY_ASSESSMENT: StructShape = StructShape {
    name: "GuardrailContentPolicyAssessment",
    members: &[(
        "filters",
        Shape::List(&Shape::Struct(&GUARDRAIL_CONTENT_FILTER)),
    )],
};

static GUARDRAIL_CONTENT_FILTER: StructShape = StructShape {
    name: "GuardrailContentFilter",
    members: &[
        ("type", Shape::String),
        ("confidence", Shape::String),
        ("action", Shape::String),
        ("filterStrength", Shape::String),
        ("detected", Shape::Boolean),
    ],
};

static GUARDRAIL_WORD_POLICY_ASSESSMENT: StructShape = StructShape {
    name: "GuardrailWordPolicyAssessment",
    members: &[
        (
            "customWords",
            Shape::List(&Shape::Struct(&GUARDRAIL_CUSTOM_WORD)),
        ),
        (
            "managedWordLists",
            Shape::List(&Shape::Struct(&GUARDRAIL_MANAGED_WORD)),
        ),
    ],
};

static GUARDRAIL_CUSTOM_WORD: StructShape = StructShape {
    name: "GuardrailCustomWord",
    members: &[
        ("match", Shape::String),
        ("action", Shape::String),
        ("detected", Shape::Boolean),
    ],
};

static GUARDRAIL_MANAGED_WORD: StructShape = StructShape {
    name: "GuardrailManagedWord",
    members: &[
        ("match", Shape::String),
        ("type", Shape::String),
        ("action", Shape::String),
        ("detected", Shape::Boolean),
    ],
};

static GUARDRAIL_SENSITIVE_INFORMATION_POLICY_ASSESSMENT: StructShape = StructShape {
    name: "GuardrailSensitiveInformationPolicyAssessment",
    members: &[
        (
            "piiEntities",
            Shape::List(&Shape::Struct(&GUARDRAIL_PII_ENTITY_FILTER)),
        ),
        (
            "regexes",
            Shape::List(&Shape::Struct(&GUARDRAIL_REGEX_FILTER)),
        ),
    ],
};

static GUARDRAIL_PII_ENTITY_FILTER: StructShape = StructShape {
    name: "GuardrailPiiEntityFilter",
    members: &[
        ("match", Shape::String),
        ("type", Shape::String),
        ("action", Shape::String),
        ("detected", Shape::Boolean),
    ],
};

static GUARDRAIL_REGEX_FILTER: StructShape = StructShape {
    name: "GuardrailRegexFilter",
    members: &[
        ("action", Shape::String),
        ("name", Shape::String),
        ("match", Shape::String),
        ("regex", Shape::String),
        ("detected", Shape::Boolean),
    ],
};

static GUARDRAIL_CONTEXTUAL_GROUNDING_POLICY_ASSESSMENT: StructShape = StructShape {
    name: "GuardrailContextualGroundingPolicyAssessment",
    members: &[(
        "filters",
        Shape::List(&Shape::Struct(&GUARDRAIL_CONTEXTUAL_GROUNDING_FILTER)),
    )],
};

static GUARDRAIL_CONTEXTUAL_GROUNDING_FILTER: StructShape = StructShape {
    name: "GuardrailContextualGroundingFilter",
    members: &[
        ("type", Shape::String),
        ("threshold", Shape::Number),
        ("score", Shape::Number),
        ("action", Shape::String),
        ("detected", Shape::Boolean),
    ],
};

static GUARDRAIL_AUTOMATED_REASONING_POLICY_ASSESSMENT: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningPolicyAssessment",
    members: &[(
        "findings",
        Shape::List(&Shape::Union(&GUARDRAIL_AUTOMATED_REASONING_FINDING)),
    )],
};

static GUARDRAIL_AUTOMATED_REASONING_FINDING: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningFinding",
    members: &[
        (
            "valid",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_VALID_FINDING),
        ),
        (
            "invalid",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_INVALID_FINDING),
        ),
        (
            "satisfiable",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_SATISFIABLE_FINDING),
        ),
        (
            "impossible",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_IMPOSSIBLE_FINDING),
        ),
        (
            "translationAmbiguous",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_TRANSLATION_AMBIGUOUS_FINDING),
        ),
        (
            "tooComplex",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_TOO_COMPLEX_FINDING),
        ),
        (
            "noTranslations",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_NO_TRANSLATIONS_FINDING),
        ),
    ],
};

static GUARDRAIL_AUTOMATED_REASONING_VALID_FINDING: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningValidFinding",
    members: &[
        (
            "translation",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_TRANSLATION),
        ),
        (
            "claimsTrueScenario",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_SCENARIO),
        ),
        (
            "supportingRules",
            Shape::List(&Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_RULE)),
        ),
        (
            "logicWarning",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_LOGIC_WARNING),
        ),
    ],
};

static GUARDRAIL_AUTOMATED_REASONING_TRANSLATION: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningTranslation",
    members: &[
        (
            "premises",
            Shape::List(&Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_STATEMENT)),
        ),
        (
            "claims",
            Shape::List(&Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_STATEMENT)),
        ),
        (
            "untranslatedPremises",
            Shape::List(&Shape::Struct(
                &GUARDRAIL_AUTOMATED_REASONING_INPUT_TEXT_REFERENCE,
            )),
        ),
        (
            "untranslatedClaims",
            Shape::List(&Shape::Struct(
                &GUARDRAIL_AUTOMATED_REASONING_INPUT_TEXT_REFERENCE,
            )),
        ),
        ("confidence", Shape::Number),
    ],
};

static GUARDRAIL_AUTOMATED_REASONING_STATEMENT: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningStatement",
    members: &[("logic", Shape::String), ("naturalLanguage", Shape::String)],
};

static GUARDRAIL_AUTOMATED_REASONING_INPUT_TEXT_REFERENCE: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningInputTextReference",
    members: &[("text", Shape::String)],
};

static GUARDRAIL_AUTOMATED_REASONING_SCENARIO: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningScenario",
    members: &[(
        "statements",
        Shape::List(&Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_STATEMENT)),
    )],
};

static GUARDRAIL_AUTOMATED_REASONING_RULE: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningRule",
    members: &[
        ("identifier", Shape::String),
        ("policyVersionArn", Shape::String),
    ],
};

static GUARDRAIL_AUTOMATED_REASONING_LOGIC_WARNING: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningLogicWarning",
    members: &[
        ("type", Shape::String),
        (
            "premises",
            Shape::List(&Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_STATEMENT)),
        ),
        (
            "claims",
            Shape::List(&Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_STATEMENT)),
        ),
    ],
};

static GUARDRAIL_AUTOMATED_REASONING_INVALID_FINDING: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningInvalidFinding",
    members: &[
        (
            "translation",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_TRANSLATION),
        ),
        (
            "contradictingRules",
            Shape::List(&Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_RULE)),
        ),
        (
            "logicWarning",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_LOGIC_WARNING),
        ),
    ],
};

static GUARDRAIL_AUTOMATED_REASONING_SATISFIABLE_FINDING: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningSatisfiableFinding",
    members: &[
        (
            "translation",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_TRANSLATION),
        ),
        (
            "claimsTrueScenario",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_SCENARIO),
        ),
        (
            "claimsFalseScenario",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_SCENARIO),
        ),
        (
            "logicWarning",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_LOGIC_WARNING),
        ),
    ],
};

static GUARDRAIL_AUTOMATED_REASONING_IMPOSSIBLE_FINDING: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningImpossibleFinding",
    members: &[
        (
            "translation",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_TRANSLATION),
        ),
        (
            "contradictingRules",
            Shape::List(&Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_RULE)),
        ),
        (
            "logicWarning",
            Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_LOGIC_WARNING),
        ),
    ],
};

static GUARDRAIL_AUTOMATED_REASONING_TRANSLATION_AMBIGUOUS_FINDING: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningTranslationAmbiguousFinding",
    members: &[
        (
            "options",
            Shape::List(&Shape::Struct(
                &GUARDRAIL_AUTOMATED_REASONING_TRANSLATION_OPTION,
            )),
        ),
        (
            "differenceScenarios",
            Shape::List(&Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_SCENARIO)),
        ),
    ],
};

static GUARDRAIL_AUTOMATED_REASONING_TRANSLATION_OPTION: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningTranslationOption",
    members: &[(
        "translations",
        Shape::List(&Shape::Struct(&GUARDRAIL_AUTOMATED_REASONING_TRANSLATION)),
    )],
};

static GUARDRAIL_AUTOMATED_REASONING_TOO_COMPLEX_FINDING: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningTooComplexFinding",
    members: &[],
};

static GUARDRAIL_AUTOMATED_REASONING_NO_TRANSLATIONS_FINDING: StructShape = StructShape {
    name: "GuardrailAutomatedReasoningNoTranslationsFinding",
    members: &[],
};

static GUARDRAIL_INVOCATION_METRICS: StructShape = StructShape {
    name: "GuardrailInvocationMetrics",
    members: &[
        ("guardrailProcessingLatency", Shape::Number),
        ("usage", Shape::Struct(&GUARDRAIL_USAGE)),
        ("guardrailCoverage", Shape::Struct(&GUARDRAIL_COVERAGE)),
    ],
};

static GUARDRAIL_USAGE: StructShape = StructShape {
    name: "GuardrailUsage",
    members: &[
        ("topicPolicyUnits", Shape::Number),
        ("contentPolicyUnits", Shape::Number),
        ("wordPolicyUnits", Shape::Number),
        ("sensitiveInformationPolicyUnits", Shape::Number),
        ("sensitiveInformationPolicyFreeUnits", Shape::Number),
        ("contextualGroundingPolicyUnits", Shape::Number),
        ("contentPolicyImageUnits", Shape::Number),
        ("automatedReasoningPolicyUnits", Shape::Number),
        ("automatedReasoningPolicies", Shape::Number),
    ],
};

static GUARDRAIL_COVERAGE: StructShape = StructShape {
    name: "GuardrailCoverage",
    members: &[
        (
            "textCharacters",
            Shape::Struct(&GUARDRAIL_TEXT_CHARACTERS_COVERAGE),
        ),
        ("images", Shape::Struct(&GUARDRAIL_IMAGE_COVERAGE)),
    ],
};

static GUARDRAIL_TEXT_CHARACTERS_COVERAGE: StructShape = StructShape {
    name: "GuardrailTextCharactersCoverage",
    members: &[("guarded", Shape::Number), ("total", Shape::Number)],
};

static GUARDRAIL_IMAGE_COVERAGE: StructShape = StructShape {
    name: "GuardrailImageCoverage",
    members: &[("guarded", Shape::Number), ("total", Shape::Number)],
};

static APPLIED_GUARDRAIL_DETAILS: StructShape = StructShape {
    name: "AppliedGuardrailDetails",
    members: &[
        ("guardrailId", Shape::String),
        ("guardrailVersion", Shape::String),
        ("guardrailArn", Shape::String),
        ("guardrailOrigin", Shape::List(&Shape::String)),
        ("guardrailOwnership", Shape::String),
    ],
};

static PROMPT_ROUTER_TRACE: StructShape = StructShape {
    name: "PromptRouterTrace",
    members: &[("invokedModelId", Shape::String)],
};

static INTERNAL_SERVER_EXCEPTION: StructShape = StructShape {
    name: "InternalServerException",
    members: &[("message", Shape::String)],
};

static MODEL_STREAM_ERROR_EXCEPTION: StructShape = StructShape {
    name: "ModelStreamErrorException",
    members: &[
        ("message", Shape::String),
        ("originalStatusCode", Shape::Number),
        ("originalMessage", Shape::String),
    ],
};

static VALIDATION_EXCEPTION: StructShape = StructShape {
    name: "ValidationException",
    members: &[("message", Shape::String)],
};

static THROTTLING_EXCEPTION: StructShape = StructShape {
    name: "ThrottlingException",
    members: &[("message", Shape::String)],
};

static SERVICE_UNAVAILABLE_EXCEPTION: StructShape = StructShape {
    name: "ServiceUnavailableException",
    members: &[("message", Shape::String)],
};
