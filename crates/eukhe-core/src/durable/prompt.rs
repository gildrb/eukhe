//! `eukhe.prompt` and `eukhe.closing`: eukhe's system prompt as durable
//! sections, one per segment of [`system_prompt_breakdown`], in the same
//! order, so the provider sees exactly eukhe's system prompt: durable joins
//! section texts with `"\n\n"` and drops empty ones, as the breakdown joins
//! its (never empty) segments. The order follows how often a part changes:
//! `eukhe.prompt` holds the install-stable sections ([`section_keys`]);
//! the other extensions' sections (such as `codemode`) follow; then
//! `eukhe.closing`, installed last, holds the closing `<critical>` block,
//! the project's instructions and the environment ([`CLOSING_KEYS`]), and
//! last `running-jobs`, present only while a job runs
//! ([`super::jobs::running_jobs_section`]). Nothing varies per session, so
//! a second session in a project reuses the provider's cached prompt.
//!
//! Inputs fixed for the session (resources, guidelines, role, memory,
//! daemon availability) are captured at construction; the model selector,
//! vision capability, offered tools, working directory, and date come from
//! each request's agent. The breakdown is cached per distinct request
//! input; a cache miss re-resolves the per-model additions
//! (`model-prompts.toml`) for the request's model. At open, a broken rule
//! map is reported once as a display-only `model_prompt_error` row.

use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::Models;
use eukhe_durable::harness::define::{define_extension, section};
use eukhe_durable::harness::types::{
    Extension, PromptInput, SubmissionDraft, WriteSubmissionDraft,
};
use eukhe_types::pi_ai::Modality;
use futures::FutureExt;

use super::deps::{HostDeps, OpenedSession};
use super::rlm::CustomNotice;
use crate::memory::MemoryRole;
use crate::prompts::model_prompts::{
    load_model_prompts, model_prompt_error_text, MODEL_PROMPT_ERROR_CUSTOM_TYPE,
};
use crate::prompts::system_prompt::{
    system_prompt_breakdown, today, BuildSystemPromptOptions, SourcedPrompt, SystemPromptBreakdown,
    CLOSING_SEGMENT,
};
use crate::skills::Skill;

/// The extension name.
pub const PROMPT_EXTENSION: &str = "eukhe.prompt";
/// The closing extension's name.
pub const CLOSING_EXTENSION: &str = "eukhe.closing";

/// Section keys of `eukhe.prompt` (the breakdown's segment names) in prompt
/// order: the install-stable part before the closing block.
pub const SECTION_KEYS: [&str; 12] = [
    "memory",
    "custom",
    "core",
    "usage",
    "opinionated",
    "model-prompts",
    "packages",
    "skills-inventory",
    "mcp-servers",
    "session-role",
    "additional-guidance",
    "appended-prompt",
];

/// Section keys of `eukhe.closing` from the breakdown, in prompt order: the
/// closing block, then what is stable for a project.
pub const CLOSING_KEYS: [&str; 3] = [CLOSING_SEGMENT, "project-context", "environment"];

/// The prompt inputs fixed for the session.
struct SessionPrompt {
    custom_prompt: Option<SourcedPrompt>,
    context_files: Vec<(String, String)>,
    skills: Vec<Skill>,
    guidelines: Vec<String>,
    append_system_prompt: Vec<SourcedPrompt>,
    allow_recursion: Option<bool>,
    rlm_depth: u32,
    parent_agent: Option<String>,
    /// No child host: `rlm.spawn` errors.
    daemonless: bool,
    generic_mcp_servers: Vec<String>,
    memory: Option<MemoryRole>,
    session_cwd: String,
    models: Models,
    /// Where `model-prompts.toml` and its files live.
    agent_dir: PathBuf,
}

/// The inputs a request contributes.
#[derive(Clone, Debug, PartialEq, Eq)]
struct RequestPrompt {
    model: Option<String>,
    vision_capable: Option<bool>,
    tools: Vec<String>,
    cwd: String,
    today: String,
}

struct PromptBuilder {
    session: SessionPrompt,
    cache: Mutex<Option<(RequestPrompt, Arc<SystemPromptBreakdown>)>>,
}

impl PromptBuilder {
    fn request(&self, input: &PromptInput) -> RequestPrompt {
        let agent = &input.agent;
        let model = agent.model.as_ref();
        RequestPrompt {
            model: model.map(|model| format!("{}/{}", model.provider, model.model_id)),
            vision_capable: model.and_then(|model| {
                self.session
                    .models
                    .get_model(&model.provider, &model.model_id)
                    .map(|found| found.input.contains(&Modality::Image))
            }),
            tools: agent.tools.iter().map(|tool| tool.name.clone()).collect(),
            cwd: agent
                .cwd
                .clone()
                .unwrap_or_else(|| self.session.session_cwd.clone()),
            today: today(),
        }
    }

    fn breakdown(&self, request: RequestPrompt) -> Arc<SystemPromptBreakdown> {
        let mut cache = self.cache.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some((key, breakdown)) = cache.as_ref() {
            if *key == request {
                return Arc::clone(breakdown);
            }
        }
        let model_prompts = load_model_prompts(request.model.as_deref(), &self.session.agent_dir);
        if !model_prompts.errors.is_empty() {
            tracing::warn!(
                errors = ?model_prompts.errors,
                "per-model system prompt additions not applied"
            );
        }
        let breakdown = Arc::new(system_prompt_breakdown(
            &self.options(&request, model_prompts.extras.as_deref()),
        ));
        *cache = Some((request, Arc::clone(&breakdown)));
        breakdown
    }

    fn options<'a>(
        &'a self,
        request: &'a RequestPrompt,
        model_prompt_extras: Option<&'a str>,
    ) -> BuildSystemPromptOptions<'a> {
        let session = &self.session;
        BuildSystemPromptOptions {
            custom_prompt: session.custom_prompt.clone(),
            model_prompt_extras,
            vision_capable: request.vision_capable,
            selected_tools: Some(request.tools.iter().map(String::as_str).collect()),
            prompt_guidelines: Some(session.guidelines.clone()),
            append_system_prompt: session.append_system_prompt.clone(),
            cwd: request.cwd.clone(),
            context_files: session.context_files.clone(),
            skills: session.skills.clone(),
            allow_recursion: session.allow_recursion,
            rlm_depth: Some(session.rlm_depth),
            rlm_parent_agent: session.parent_agent.as_deref(),
            daemonless: session.daemonless,
            generic_mcp_servers: session.generic_mcp_servers.clone(),
            memory: session.memory,
        }
    }

    fn segment(&self, input: &PromptInput, key: &str) -> Option<String> {
        let breakdown = self.breakdown(self.request(input));
        breakdown
            .segments
            .iter()
            .find(|segment| segment.name == key)
            .map(|segment| segment.text.clone())
            .filter(|text| !text.is_empty())
    }
}

/// The session's two prompt extensions sharing one breakdown: `eukhe.prompt`
/// ([`SECTION_KEYS`]), which the registry installs first, and
/// `eukhe.closing` ([`CLOSING_KEYS`], then `running-jobs`), which it
/// installs last, after every other extension's sections. A user prompt
/// that replaces the layered defaults drops the closing block: its section
/// is then empty.
#[must_use]
pub fn extensions(deps: &Arc<HostDeps>) -> [Arc<Extension>; 2] {
    let builder = Arc::new(PromptBuilder {
        session: SessionPrompt {
            custom_prompt: deps.resources.system_prompt.clone(),
            context_files: deps
                .resources
                .agents_files
                .iter()
                .map(|file| (file.path.display().to_string(), file.content.clone()))
                .collect(),
            skills: deps.resources.skills.clone(),
            guidelines: deps.prompt.guidelines.clone(),
            append_system_prompt: deps.resources.append_system_prompt.clone(),
            allow_recursion: deps.prompt.allow_recursion,
            rlm_depth: deps.role.rlm_depth,
            parent_agent: deps
                .role
                .parent
                .as_ref()
                .and_then(|parent| parent.agent_name.clone()),
            daemonless: deps.children.is_none(),
            generic_mcp_servers: deps.generic_mcp_servers.clone(),
            memory: deps.memory.as_ref().map(|_| deps.role.memory_role()),
            session_cwd: deps.cwd.display().to_string(),
            models: deps.models.clone(),
            agent_dir: deps.agent_dir.clone(),
        },
        cache: Mutex::new(None),
    });
    report_model_prompt_errors(deps);
    let sections = |keys: &[&'static str]| -> Vec<_> {
        keys.iter()
            .map(|&key| {
                let builder = Arc::clone(&builder);
                section(
                    key,
                    move |input: &PromptInput, _cx| {
                        futures::future::ready(Ok(builder.segment(input, key))).boxed()
                    },
                    Some(false),
                )
            })
            .collect()
    };
    let prompt = define_extension(Extension {
        name: PROMPT_EXTENSION.to_owned(),
        sections: sections(&SECTION_KEYS),
        ..Extension::default()
    });
    let mut closing = sections(&CLOSING_KEYS);
    // Last: it comes and goes with the jobs, after the stable sections.
    closing.push(super::jobs::running_jobs_section(deps));
    let closing = define_extension(Extension {
        name: CLOSING_EXTENSION.to_owned(),
        sections: closing,
        ..Extension::default()
    });
    [prompt, closing]
}

/// Report a broken model-prompts rule map once per open: a display-only
/// `model_prompt_error` row on the root conversation (problems disable the
/// additions whatever the model, so the selector does not matter). The row
/// is submitted in the background, as the kernel boot notices are: a
/// submission resumes scheduling, which a service start must not do.
fn report_model_prompt_errors(deps: &Arc<HostDeps>) {
    let errors = load_model_prompts(None, &deps.agent_dir).errors;
    if errors.is_empty() {
        return;
    }
    let notice = CustomNotice::new(
        MODEL_PROMPT_ERROR_CUSTOM_TYPE,
        model_prompt_error_text(&errors),
        true,
        None,
    );
    deps.add_service(Box::new(move |opened: OpenedSession| {
        async move {
            tokio::spawn(async move {
                let cx = eukhe_chord::context::BACKGROUND_CONTEXT.clone();
                let submitted = match notice.draft() {
                    Ok(entry) => opened
                        .root
                        .submit(
                            SubmissionDraft::Write(WriteSubmissionDraft {
                                request_id: None,
                                entry,
                            }),
                            &cx,
                        )
                        .await
                        .map(drop)
                        .map_err(anyhow::Error::from),
                    Err(error) => Err(anyhow::Error::from(error)),
                };
                if let Err(error) = submitted {
                    tracing::warn!(%error, "model prompt error notice not delivered");
                }
            });
            Ok(None)
        }
        .boxed()
    }));
}

#[cfg(test)]
mod budget_tests;
