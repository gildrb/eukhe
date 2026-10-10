//! Prime Inference catalog constants: the provider's base URL (the compiled
//! transport tuple its entries pin to) and the private-model id predicate.
//! The Prime Inference models themselves ship compiled
//! ([`crate::transports::prime_inference_offline_entries`]).

/// The Prime Inference API base URL (the compiled transport's `baseUrl`).
pub const PRIME_INFERENCE_BASE_URL: &str = "https://api.pinference.ai/api/v1";

/// Whether a model id is private (internal/, dev/, or alias-qualified with `:`).
#[must_use]
pub fn is_private_prime_inference_model_id(model_id: &str) -> bool {
    let normalized = model_id.to_ascii_lowercase();
    normalized.starts_with("internal/")
        || normalized.starts_with("dev/")
        || normalized.contains(':')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private_ids_are_recognized() {
        assert!(is_private_prime_inference_model_id("internal/foo"));
        assert!(is_private_prime_inference_model_id("DEV/bar"));
        assert!(is_private_prime_inference_model_id("x:y"));
        assert!(!is_private_prime_inference_model_id(
            "anthropic/claude-fable-5"
        ));
    }
}
