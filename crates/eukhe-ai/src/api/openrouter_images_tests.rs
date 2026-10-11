//! Port of `test/openrouter-images.test.ts` (the mocked `openai` client
//! becomes a mock `fetch`) and `test/images.test.ts` (live, ignored).

use base64::Engine as _;
use eukhe_chord::context::AbortController;
use eukhe_types::pi_ai::{
    ImageContent, ImageModel, ImagesContext, ImagesStopReason, TextContent, UserContentBlock,
};
use serde_json::json;

use crate::api::system_one_shared::test_fetch::{json_response, mock_fetch, recorded, Requests};
use crate::image_models::get_image_model;
use crate::images::generate_images;
use crate::types::{ImagesOptions, ProviderImagesOptions, ProviderRequestOptions};

fn image_model(id: &str, name: &str, output: &[&str]) -> ImageModel {
    serde_json::from_value(json!({
        "type": "image",
        "id": id,
        "name": name,
        "api": "openrouter-images",
        "provider": "openrouter",
        "baseUrl": "https://openrouter.ai/api/v1",
        "input": ["text", "image"],
        "output": output,
        "cost": { "input": 0.015, "output": 0.03, "cacheRead": 0, "cacheWrite": 0 },
    }))
    .expect("model")
}

fn dog() -> ImagesContext {
    ImagesContext {
        input: vec![UserContentBlock::Text(TextContent::new("Generate a dog"))],
    }
}

fn fake_openrouter() -> (crate::types::FetchFunction, Requests) {
    mock_fetch(|_| {
        json_response(
            200,
            &json!({
                "id": "img-1",
                "usage": {
                    "prompt_tokens": 12,
                    "completion_tokens": 34,
                    "prompt_tokens_details": { "cached_tokens": 0 },
                },
                "choices": [{
                    "message": {
                        "content": "Here is your image.",
                        "images": [{ "image_url": "data:image/png;base64,ZmFrZS1wbmc=" }],
                    },
                }],
            }),
        )
    })
}

fn options(fetch: crate::types::FetchFunction) -> ProviderImagesOptions {
    ProviderImagesOptions {
        images: ImagesOptions {
            request: ProviderRequestOptions {
                api_key: Some("test".to_owned()),
                fetch: Some(fetch),
                ..ProviderRequestOptions::default()
            },
            metadata: None,
        },
        extra: serde_json::Map::new(),
    }
}

#[tokio::test]
async fn returns_text_plus_images_in_final_output() {
    let mut model = image_model(
        "google/gemini-3.1-flash-image-preview",
        "Gemini 3.1 Flash Image Preview",
        &["text", "image"],
    );
    model.headers = Some(
        [("HTTP-Referer".to_owned(), "https://example.com".to_owned())]
            .into_iter()
            .collect(),
    );
    let (fetch, requests) = fake_openrouter();

    let output = generate_images(&model, &dog(), options(fetch))
        .await
        .expect("images");

    assert_eq!(output.stop_reason, ImagesStopReason::Stop);
    assert_eq!(output.response_id.as_deref(), Some("img-1"));
    assert_eq!(
        output.output[0],
        UserContentBlock::Text(TextContent::new("Here is your image."))
    );
    assert_eq!(
        output.output[1],
        UserContentBlock::Image(ImageContent {
            mime_type: "image/png".to_owned(),
            data: "ZmFrZS1wbmc=".to_owned(),
        })
    );

    let requests = recorded(&requests);
    assert_eq!(
        requests[0].url,
        "https://openrouter.ai/api/v1/chat/completions"
    );
    assert_eq!(requests[0].method, "POST");
    assert_eq!(requests[0].header("authorization"), Some("Bearer test"));
    assert_eq!(
        requests[0].header("http-referer"),
        Some("https://example.com")
    );
    let params = requests[0].json();
    assert_eq!(params["stream"], false);
    assert_eq!(params["modalities"], json!(["image", "text"]));
    assert_eq!(
        params["messages"][0]["content"][0],
        json!({ "type": "text", "text": "Generate a dog" })
    );
}

#[tokio::test]
async fn passes_through_abort_signal_and_returns_aborted_result() {
    let model = image_model("black-forest-labs/flux.2-pro", "FLUX.2 Pro", &["image"]);
    let controller = AbortController::new();
    controller.abort(None);
    let (fetch, _) = fake_openrouter();
    let mut aborted = options(fetch);
    aborted.images.request.signal = Some(controller.signal());

    let output = generate_images(&model, &dog(), aborted)
        .await
        .expect("images");

    assert_eq!(output.stop_reason, ImagesStopReason::Aborted);
    assert_eq!(output.error_message.as_deref(), Some("Request aborted"));
}

#[tokio::test]
async fn generate_images_resolves_the_final_assistant_images_result() {
    let model = image_model("black-forest-labs/flux.2-pro", "FLUX.2 Pro", &["image"]);
    let (fetch, requests) = fake_openrouter();

    let output = generate_images(&model, &dog(), options(fetch))
        .await
        .expect("images");

    assert!(output
        .output
        .iter()
        .any(|item| matches!(item, UserContentBlock::Image(_))));
    // Image-only models must not request text output.
    assert_eq!(
        recorded(&requests)[0].json()["modalities"],
        json!(["image"])
    );
}

fn live_options() -> ProviderImagesOptions {
    ProviderImagesOptions {
        images: ImagesOptions {
            request: ProviderRequestOptions {
                api_key: std::env::var("OPENROUTER_API_KEY").ok(),
                ..ProviderRequestOptions::default()
            },
            metadata: None,
        },
        extra: serde_json::Map::new(),
    }
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_images_should_generate_a_basic_image() {
    let model = get_image_model("openrouter", "google/gemini-2.5-flash-image").expect("model");
    let context = ImagesContext {
        input: vec![UserContentBlock::Text(TextContent::new(
            "Generate a simple red circle on a plain white background. No text.",
        ))],
    };
    let response = generate_images(&model, &context, live_options())
        .await
        .expect("images");
    assert_eq!(
        response.stop_reason,
        ImagesStopReason::Stop,
        "Error: {:?}",
        response.error_message
    );
    assert!(response.error_message.is_none());
    assert!(response
        .output
        .iter()
        .any(|item| matches!(item, UserContentBlock::Image(_))));
    assert!(response.timestamp > 0);
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_images_should_handle_image_input() {
    let model = get_image_model("openrouter", "google/gemini-2.5-flash-image").expect("model");
    let image = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/data/red-circle.png"
    ))
    .expect("fixture");
    let context = ImagesContext {
        input: vec![
            UserContentBlock::Text(TextContent::new(
                "Create a variation of this image with a blue background.",
            )),
            UserContentBlock::Image(ImageContent {
                data: base64::engine::general_purpose::STANDARD.encode(image),
                mime_type: "image/png".to_owned(),
            }),
        ],
    };
    let response = generate_images(&model, &context, live_options())
        .await
        .expect("images");
    assert_eq!(
        response.stop_reason,
        ImagesStopReason::Stop,
        "Error: {:?}",
        response.error_message
    );
    assert!(response
        .output
        .iter()
        .any(|item| matches!(item, UserContentBlock::Image(_))));
}
