//! Model subsystem: the local registry (bundled/compiled catalog plus the
//! user's models.json), the resolver, and Prime Inference private models.

pub use allowlist::{model_allowed, ModelAllowlistRefusal};
pub use registry::{
    resolve_request_auth, ModelRegistry, ProviderRequestConfig, ResolvedRequestAuth,
    SetModelSelectionError,
};

pub mod allowlist;
pub(crate) mod custom;
pub mod image_model_routing;
pub(crate) mod prime_inference;
pub(crate) mod registry;
pub(crate) mod resolver;
pub(crate) mod session_restore;

pub use custom::{
    apply_model_override, load_custom_models, merge_compat, parse_models_config,
    strip_json_comments, validate_config, CustomModelsResult, ModelOverride, ModelsConfig,
    ProviderOverride,
};
pub use image_model_routing::{
    resolve_image_model_override, ImageModelRoutingInputs, ResolvedImageModel,
};
pub use prime_inference::{is_private_prime_inference_model, private_prime_inference_models};
pub use resolver::{
    build_fallback_model, failover_candidates, find_exact_model_reference_match,
    find_initial_model, find_preferred_default_model, initial_model_unavailable_message,
    resolve_cli_model, resolve_model_scope_from_models, InitialModelOptions, ResolveCliModelResult,
    ScopedModel, PRIME_INFERENCE_DEFAULT_MODEL_ID,
};
pub use session_restore::find_session_model;
