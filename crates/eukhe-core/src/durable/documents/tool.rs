//! The wire documents tools: `read` (`read@1`), `edit` (`edit@hl.1`),
//! `grep` (`grep@1`), and `glob` (`glob@1`). Each performs its function on
//! the session's documents, the same engine and edit store as the kernel's
//! `read()`/`edit()`/`grep()`/`glob()`, so lines either shows are anchorable
//! by both. The Harness repairs the arguments by the function's declared
//! dialect before the call; the text is bounded once by [`BoundedOutput`].

use std::path::PathBuf;
use std::sync::Arc;

use base64::prelude::{Engine as _, BASE64_STANDARD};
use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{
    ToolDiagnostic, ToolExecutionApi, ToolExecutionMode, ToolExecutionResult, ToolRegistration,
    ToolReplay,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::pi_ai::{
    ImageContent, JsonValue as PiJsonValue, Modality, Model, TextContent, UserContentBlock,
};

use super::contract::Function;
use super::probe;
use super::requests::{perform, Caller, Cut, Done, Performed, ReadImage};
use super::DocumentsHost;
use crate::durable::bounded_output::BoundedOutput;
use crate::durable::HostDeps;

/// The text the model gets of `done`, bounded by `output`; the rows of a
/// read or grep that survive the bound become seen, and only those.
pub(super) fn bounded(
    documents: &eukhe_docs::Documents,
    done: &Done,
    mut output: BoundedOutput,
) -> (String, Option<ToolDiagnostic>) {
    output.push(done.rendered());
    let (text, diagnostic) = output.finish();
    let cut = match diagnostic
        .as_ref()
        .and_then(|diagnostic| diagnostic.omitted.as_ref())
    {
        Some(omitted) => Cut::of(done.rendered(), &text, omitted),
        None => Cut::Whole,
    };
    done.mark_seen(documents, &cut);
    (text, diagnostic)
}

/// The registration of `function`. `edit` runs sequentially with the kernel
/// cell that may also edit and never replays blindly: its probe looks at
/// the files a call interrupted by a crash was writing, so the call is
/// adopted, run again, or reported interrupted as they show
/// ([`probe::probe`]). The others only read and replay safely.
pub(super) fn document_tool(
    function: Function,
    host: &Arc<DocumentsHost>,
    deps: &Arc<HostDeps>,
) -> Arc<ToolRegistration> {
    let host = Arc::clone(host);
    let deps = Arc::clone(deps);
    let mut registration = ToolRegistration::new(
        function.name(),
        function.description(),
        function.parameters(),
        move |args: PiJsonValue, api: Arc<dyn ToolExecutionApi>, cx: Context| {
            let host = Arc::clone(&host);
            let deps = Arc::clone(&deps);
            async move { execute(function, host, &deps, args, api, &cx).await }
        },
    );
    registration.dialect = function.dialect();
    match function {
        Function::Edit | Function::Write => {
            registration.execution_mode = Some(ToolExecutionMode::Sequential);
            registration.replay = Some(ToolReplay::Unsafe);
            registration.probe = Some(probe::probe());
        }
        Function::Read | Function::Grep | Function::Glob => {
            registration.replay = Some(ToolReplay::Safe);
        }
    }
    define_tool(registration)
}

fn text_result(
    text: String,
    images: Vec<ImageContent>,
    is_error: bool,
    details: serde_json::Value,
) -> ToolExecutionResult {
    let mut output = vec![UserContentBlock::Text(TextContent::new(text))];
    output.extend(images.into_iter().map(UserContentBlock::Image));
    ToolExecutionResult {
        output: Some(output),
        is_error: Some(is_error),
        details: Some(JsonValue::from(details)),
        ..ToolExecutionResult::default()
    }
}

/// Relative paths resolve against the session's working directory (the
/// agent's cwd, else the session's).
async fn execute(
    function: Function,
    host: Arc<DocumentsHost>,
    deps: &HostDeps,
    args: PiJsonValue,
    api: Arc<dyn ToolExecutionApi>,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    let PiJsonValue::Object(args) = args else {
        return Err(SessionError::error(format!(
            "{} arguments must be an object",
            function.name()
        )));
    };
    let agent = api.agent(cx).await?;
    let cwd = agent
        .cwd
        .clone()
        .map_or_else(|| deps.cwd.clone(), PathBuf::from);
    let performed = perform(
        &host,
        function,
        cwd.clone(),
        &cwd,
        args,
        Caller::Tool(Arc::clone(&api)),
        cx,
    )
    .await
    .map_err(|error| SessionError::error(format!("{} worker failed: {error}", function.name())))?;
    match performed {
        Ok(Performed { done, mut images }) => {
            let output = BoundedOutput::in_session(
                deps.storage_dir.as_deref(),
                &api.task_id().to_string(),
                api.truncation(),
            );
            let (text, bounded) = bounded(&host.documents, &done, output);
            let details = serde_json::to_value(&done).map_err(SessionError::other)?;
            let (text, is_error) = match done.image() {
                None => (text, false),
                Some(image) => {
                    let model = agent
                        .model
                        .as_ref()
                        .and_then(|model| deps.models.get_model(&model.provider, &model.model_id));
                    match image_refusal(&image, model.as_ref()) {
                        None => {
                            images.push(ImageContent {
                                data: BASE64_STANDARD.encode(image.bytes),
                                mime_type: image.mime_type.to_string(),
                            });
                            (text, false)
                        }
                        Some(refusal) => (format!("{text}\n{refusal}"), true),
                    }
                }
            };
            Ok(ToolExecutionResult {
                diagnostics: bounded.map(|diagnostic| vec![diagnostic]),
                ..text_result(text, images, is_error, details)
            })
        }
        Err(rejection) => {
            let details = serde_json::to_value(&rejection).map_err(SessionError::other)?;
            Ok(text_result(rejection.message, Vec::new(), true, details))
        }
    }
}

/// The longest side, in pixels, of an image `read` attaches as it is on
/// disk (Anthropic's recommended size, omp's read limit).
const READ_IMAGE_MAX_SIDE: u64 = 1568;
/// The largest image file `read` attaches as it is on disk (omp's).
const READ_IMAGE_MAX_BYTES: u64 = 500 * 1024;

/// Why `read` does not attach `image` for `model`, or `None` when it does:
/// the model sees images, and the image is within both read limits and the
/// model's own image resize limits (`inputLimits.images.resize`). A larger
/// image is for `attach_image`, which resizes it.
fn image_refusal(image: &ReadImage<'_>, model: Option<&Model>) -> Option<String> {
    let Some(model) = model.filter(|model| model.input.contains(&Modality::Image)) else {
        return Some("Not attached: this model cannot see images.".to_string());
    };
    let resize = model
        .input_limits
        .as_ref()
        .and_then(|limits| limits.images.as_ref())
        .and_then(|images| images.resize.as_ref());
    let max_width = resize
        .and_then(|resize| resize.max_width)
        .map_or(READ_IMAGE_MAX_SIDE, |max| max.min(READ_IMAGE_MAX_SIDE));
    let max_height = resize
        .and_then(|resize| resize.max_height)
        .map_or(READ_IMAGE_MAX_SIDE, |max| max.min(READ_IMAGE_MAX_SIDE));
    // The model's byte limit is on the base64 payload: 4 characters per 3
    // bytes.
    let max_bytes = resize
        .and_then(|resize| resize.max_bytes)
        .map_or(READ_IMAGE_MAX_BYTES, |max| {
            (max / 4 * 3).min(READ_IMAGE_MAX_BYTES)
        });
    let size = u64::try_from(image.bytes.len()).unwrap_or(u64::MAX);
    if u64::from(image.width) <= max_width
        && u64::from(image.height) <= max_height
        && size <= max_bytes
    {
        return None;
    }
    let path = image
        .absolute
        .map(|path| path.display().to_string())
        .unwrap_or_default();
    Some(format!(
        "Not attached: over the read limit of {max_width}x{max_height} pixels and {} KB. \
         `print(await attach_image.run({path:?}))` in `ipython` resizes it into context.",
        max_bytes / 1024
    ))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use eukhe_types::pi_ai::{
        ModelCost, ModelImageInputLimits, ModelImageResizeOptions, ModelInputLimits,
    };

    use super::*;

    fn model(input: Vec<Modality>, resize: Option<ModelImageResizeOptions>) -> Model {
        Model {
            id: "m".to_owned(),
            name: "m".to_owned(),
            api: "faux".to_owned(),
            provider: "p".to_owned(),
            base_url: String::new(),
            input,
            input_limits: resize.map(|resize| ModelInputLimits {
                max_request_bytes: None,
                images: Some(ModelImageInputLimits {
                    resize: Some(resize),
                    max_per_message: None,
                    max_per_request: None,
                }),
            }),
            cost: ModelCost::default(),
            headers: None,
            model_type: None,
            reasoning: false,
            thinking_level_map: None,
            prompt_cache: None,
            context_window: 100_000,
            max_tokens: 4_096,
            sampling_params: None,
            sampling_params_by_thinking_level: None,
            compat: None,
            featured: None,
        }
    }

    /// `read` attaches a PNG or JPEG to a vision model within 1568 pixels a
    /// side and 500 KB, lowered by the model's own resize limits; anything
    /// else names `attach_image`, and a model without vision gets none.
    #[test]
    fn read_attaches_images_within_the_read_and_model_limits() {
        fn image(width: u32, height: u32, bytes: &[u8]) -> ReadImage<'_> {
            ReadImage {
                absolute: Some(Path::new("/w/shot.png")),
                mime_type: "image/png",
                width,
                height,
                bytes,
            }
        }
        let bytes = vec![0; 300 * 1024];
        let bytes = bytes.as_slice();
        let vision = model(vec![Modality::Text, Modality::Image], None);
        let small = model(
            vec![Modality::Text, Modality::Image],
            Some(ModelImageResizeOptions {
                max_width: Some(1000),
                max_height: Some(2000),
                // The base64 length of 200 KB.
                max_bytes: Some(273_068),
                jpeg_quality: Some(80),
            }),
        );
        let text_only = model(vec![Modality::Text], None);
        let over = |limits: &str| {
            Some(format!(
                "Not attached: over the read limit of {limits}. `print(await attach_image.run(\"/w/shot.png\"))` in `ipython` resizes it into context."
            ))
        };
        assert_eq!(
            [
                image_refusal(&image(1568, 980, bytes), Some(&vision)),
                image_refusal(&image(1569, 980, bytes), Some(&vision)),
                image_refusal(&image(1000, 980, &bytes[..200 * 1024]), Some(&small)),
                image_refusal(&image(1001, 980, &bytes[..200 * 1024]), Some(&small)),
                image_refusal(&image(1000, 980, bytes), Some(&small)),
                image_refusal(&image(10, 10, &bytes[..10]), Some(&text_only)),
                image_refusal(&image(10, 10, &bytes[..10]), None),
            ],
            [
                None,
                over("1568x1568 pixels and 500 KB"),
                None,
                over("1000x1568 pixels and 200 KB"),
                over("1000x1568 pixels and 200 KB"),
                Some("Not attached: this model cannot see images.".to_owned()),
                Some("Not attached: this model cannot see images.".to_owned()),
            ]
        );
    }
}
