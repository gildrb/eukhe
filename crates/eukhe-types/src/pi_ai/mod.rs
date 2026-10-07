//! Serializable data types of `@earendil-works/pi-ai` v1.0.4 (`types.ts`):
//! messages, content blocks, usage, stream events, tools, contexts, models
//! with their compat settings, and the image/classifier result types.
//!
//! JSON shapes match the TS wire format: camelCase keys, tags (`type`,
//! `role`) serialized first, optional fields omitted when absent, numbers
//! printed like `JSON.stringify` (see [`js_number`]). The runtime-only types
//! (stream options and callbacks) live in `eukhe_pi_ai::types`.

mod api;
mod classifier;
mod compat;
mod content;
mod context;
mod event;
mod images;
pub mod js_number;
mod message;
mod model;
pub mod nullable;
mod routing;
mod settings;
mod string_enum;
mod tool;
mod tool_schema;
mod usage;

pub use indexmap::IndexMap;

pub use api::{
    Api, ClassifierApi, ImageApi, KnownApi, KnownClassifierApi, KnownImageApi, KnownProvider,
    ProviderId,
};
pub use classifier::{
    ClassifierAnswer, ClassifierBoolCriteria, ClassifierContext, ClassifierQuestion,
    ClassifierResult, ClassifierStopReason,
};
pub use compat::{
    AnthropicAllowedFallbackModel, AnthropicMessagesCompat, AnthropicSessionAffinityFormat,
    BedrockCompat, CacheControlFormat, MaxTokensField, MistralConversationsCompat, ModelCompat,
    OpenAICompletionsCompat, OpenAIResponsesCompat, ThinkingFormat,
};
pub use content::{
    AssistantContentBlock, CacheBreakpoint, ContentBlockText, ImageContent, SystemContent,
    TextContent, TextSignaturePhase, TextSignatureV1, ThinkingContent, ToolCall, UserContent,
    UserContentBlock,
};
pub use context::{Context, TranscriptContext};
pub use event::AssistantMessageEvent;
pub use images::{
    AssistantImages, ImagesContext, ImagesInputContent, ImagesOutputContent, ImagesStopReason,
};
pub use message::{
    AssistantMessage, AssistantMessageDiagnostic, DeferredHandle, DiagnosticCode,
    DiagnosticErrorInfo, Message, NestedToolCallRecord, NestedToolCallStatus, NestedToolCalls,
    SystemMessage, ToolResultMessage, UserMessage,
};
pub use model::{
    AnyModel, ChatModelType, ClassifierModel, ImageModel, Modality, Model, ModelCost,
    ModelCostRates, ModelCostTier, ModelImageInputLimits, ModelImageResizeOptions,
    ModelInputLimits, ModelType,
};
pub use routing::{
    DataCollection, OpenRouterMaxPrice, OpenRouterPercentiles, OpenRouterRouting, OpenRouterSort,
    OpenRouterSortOptions, OpenRouterThreshold, PriceValue, VercelGatewayRouting,
};
pub use settings::{
    CacheRetention, ChatTemplateKwargValue, ChatTemplateVar, ChatTemplateVarRef, ModelPromptCache,
    ModelThinkingLevel, ProviderEnv, ProviderHeaders, ProviderResponse, SamplingParams,
    SamplingParamsByThinkingLevel, ServiceTier, SessionAffinityFormat, ThinkingBudgets,
    ThinkingLevel, ThinkingLevelMap, ThinkingTokenBudgetField, ToolChoice, Transport,
};
pub use tool::{
    ConstrainedSamplingConfig, GrammarFormat, GrammarVariants, JsonSchemaStrictness, Tool,
    ToolConstrainedSampling, ToolReference,
};
pub use tool_schema::ToolSchema;
pub use usage::{DoneReason, ErrorReason, StopReason, Usage, UsageCost};

/// TS `JsonValue`.
pub type JsonValue = serde_json::Value;

/// TS `JsonObject = { [key: string]: JsonValue }`.
pub type JsonObject = serde_json::Map<String, JsonValue>;

#[cfg(test)]
mod tests;
