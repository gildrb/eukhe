//! The code mode tool and extension (pi-durable `codemode.ts`
//! `createCodemodeTool`, `createCodemodeExtension`).

use std::sync::Arc;

use eukhe_ai::typebox::{Options, Type};
use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_types::pi_ai::{
    ConstrainedSamplingConfig, GrammarFormat, GrammarVariants, JsonValue as PiJsonValue,
    ToolConstrainedSampling,
};
use futures::future::BoxFuture;
use futures::FutureExt;

use super::call::execute;
use super::describe::{
    codemode_description, codemode_section, CodemodeModels, CodemodeNamespace,
    DEFAULT_CODEMODE_INLINE_BUDGET,
};
use super::models::{create_model_tools, CODEMODE_INTERNAL_PREFIX};
use super::output::OutputLimits;
use super::sandbox::CodemodeSandbox;
use super::source::CODEMODE_SOURCE_GRAMMAR;
use crate::harness::define::{define_extension, define_tool, section};
use crate::harness::types::{
    Extension, ToolCaller, ToolExecutionApi, ToolOutputLimits, ToolRegistration, ToolReplay,
};
use crate::session::{SessionError, SessionResult};

/// Version of everything in this module that turns stored results into
/// what a script sees: result mapping, globals, start data. Bump it when
/// that changes, so a call started before an upgrade is not replayed by
/// different code.
pub const CODEMODE_MODULE_VERSION: u32 = 1;

pub const CODEMODE_TOOL_NAME: &str = "codemode";

/// Outputs bounded by the script's own token budget; the Harness's limits
/// only stop a runaway.
pub(super) const OUTPUT_LIMITS: OutputLimits = OutputLimits {
    max_bytes: 4 * 1024 * 1024,
    max_lines: 100_000,
};

/// A host function scripts call as a top-level global: `(args, api, cx)`,
/// where `args` is what the script passed (the argument list when
/// `spread`), resolving to the value (`None`: `undefined`). Its result is
/// journaled, so a replay does not call it again.
pub type CodemodeGlobalExecute = Arc<
    dyn Fn(
            Option<JsonValue>,
            Arc<dyn ToolExecutionApi>,
            Context,
        ) -> BoxFuture<'static, SessionResult<Option<JsonValue>>>
        + Send
        + Sync,
>;

/// A host global (TS `CodemodeGlobal`): an identifier or `namespace.member`.
#[derive(Clone)]
pub struct CodemodeGlobal {
    pub name: String,
    /// The call passes its whole argument list instead of the first
    /// argument.
    pub spread: bool,
    pub execute: CodemodeGlobalExecute,
}

impl std::fmt::Debug for CodemodeGlobal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CodemodeGlobal")
            .field("name", &self.name)
            .field("spread", &self.spread)
            .finish_non_exhaustive()
    }
}

/// Options of the code mode tool (TS `CodemodeToolOptions`).
#[derive(Debug, Clone)]
pub struct CodemodeToolOptions {
    /// Runs the scripts.
    pub sandbox: CodemodeSandbox,
    /// Groups of tools by name prefix, such as MCP servers, for the
    /// `codemode` section and tool search.
    pub namespaces: Vec<CodemodeNamespace>,
    /// Estimated tokens the tool declarations in the `codemode` section may
    /// use.
    pub inline_budget: usize,
    /// Whether scripts get `models.*`: the model catalog, classifiers, and
    /// image generation.
    pub models: CodemodeModels,
    /// Host functions scripts call as globals.
    pub globals: Vec<CodemodeGlobal>,
}

impl CodemodeToolOptions {
    /// The defaults with `sandbox`: no namespaces, the default inline
    /// budget, `models.*` included, no host globals.
    #[must_use]
    pub fn new(sandbox: CodemodeSandbox) -> Self {
        Self {
            sandbox,
            namespaces: Vec::new(),
            inline_budget: DEFAULT_CODEMODE_INLINE_BUDGET,
            models: CodemodeModels::Included,
            globals: Vec::new(),
        }
    }
}

/// The code mode tool. Scripts call the conversation's callable tools as
/// `tools.<name>(args)`.
#[must_use]
pub fn create_codemode_tool(options: &Arc<CodemodeToolOptions>) -> Arc<ToolRegistration> {
    let parameters = Type::object([(
        "code",
        Type::string_with(Options::new().set("description", "Raw JavaScript source.")),
    )]);
    let shared = Arc::clone(options);
    let mut tool = ToolRegistration::new(
        CODEMODE_TOOL_NAME,
        codemode_description(options.models),
        parameters,
        move |args: PiJsonValue, api: Arc<dyn ToolExecutionApi>, cx: Context| {
            let options = Arc::clone(&shared);
            async move {
                let code = args
                    .get("code")
                    .and_then(PiJsonValue::as_str)
                    .ok_or_else(|| SessionError::type_error("codemode expects a code string"))?
                    .to_owned();
                execute(options, api, cx, &code).await
            }
        },
    );
    // Capable models write the script as raw text instead of a JSON-escaped
    // string; pi-ai applies it only for them.
    let mut variants = GrammarVariants::new();
    variants.insert(
        GrammarFormat::OpenAILark,
        CODEMODE_SOURCE_GRAMMAR.to_owned(),
    );
    tool.constrained_sampling = Some(ToolConstrainedSampling::Config(
        ConstrainedSamplingConfig::Grammar { variants },
    ));
    tool.output_limits = Some(ToolOutputLimits {
        max_bytes: Some(OUTPUT_LIMITS.max_bytes),
        max_lines: Some(OUTPUT_LIMITS.max_lines),
        retain: None,
    });
    tool.callers = Some(vec![ToolCaller::Model]);
    tool.replay = Some(ToolReplay::Safe);
    define_tool(tool)
}

/// The `codemode` extension: the code mode tool, the internal tools behind
/// `models.*` when included, and the `codemode` prompt section listing the
/// tools scripts can call.
#[must_use]
pub fn create_codemode_extension(options: CodemodeToolOptions) -> Arc<Extension> {
    let options = Arc::new(options);
    let mut tools = vec![create_codemode_tool(&options)];
    match options.models {
        CodemodeModels::Included => tools.extend(create_model_tools()),
        CodemodeModels::Excluded => {}
    }
    let shared = Arc::clone(&options);
    let render = section(
        "codemode",
        move |input, _cx| {
            let callable: Vec<Arc<ToolRegistration>> = input
                .agent
                .callable
                .iter()
                .filter(|tool| !tool.name.starts_with(CODEMODE_INTERNAL_PREFIX))
                .cloned()
                .collect();
            let text = codemode_section(&callable, &shared.namespaces, shared.inline_budget);
            async move { Ok(text) }.boxed()
        },
        None,
    );
    define_extension(Extension {
        tools,
        sections: vec![render],
        ..Extension::named("codemode")
    })
}
