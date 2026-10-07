//! `eukhe.prompt`: eukhe's system prompt as durable sections. Each segment
//! of [`system_prompt_breakdown`] is one untagged section, in the same
//! order, so the provider sees exactly the old engine's prompt: durable
//! joins section texts with `"\n\n"` and drops empty ones, as the breakdown
//! joins its (never empty) segments.
//!
//! Inputs fixed for the session (resources, guidelines, role, memory, log
//! path) are captured at construction; the model selector, vision
//! capability, offered tools, working directory, and date come from each
//! request's agent. The breakdown is cached per distinct request input.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_durable::harness::define::{define_extension, section};
use eukhe_durable::harness::types::{Extension, PromptInput};
use eukhe_pi_ai::models::Models;
use eukhe_types::pi_ai::Modality;
use futures::FutureExt;

use super::deps::HostDeps;
use crate::memory::MemoryRole;
use crate::prompts::system_prompt::{
    system_prompt_breakdown, today, BuildSystemPromptOptions, SystemPromptBreakdown,
};
use crate::skills::Skill;

/// The extension name.
pub const PROMPT_EXTENSION: &str = "eukhe.prompt";

/// Section keys (the breakdown's segment names) in prompt order. The project
/// context closes the prompt of a chat-memory session and follows the
/// packages otherwise.
#[must_use]
pub fn section_keys(memory: Option<MemoryRole>) -> Vec<&'static str> {
    let mut keys = vec![
        "memory",
        "custom",
        "core",
        "usage",
        "opinionated",
        "per-model",
        "packages",
    ];
    if memory.is_none() {
        keys.push("project-context");
    }
    keys.extend([
        "skills-inventory",
        "mcp-servers",
        "environment",
        "session-role",
        "additional-guidance",
        "appended-prompt",
    ]);
    if memory.is_some() {
        keys.push("project-context");
    }
    keys
}

/// The prompt inputs fixed for the session.
struct SessionPrompt {
    custom_prompt: Option<String>,
    context_files: Vec<(String, String)>,
    skills: Vec<Skill>,
    guidelines: Vec<String>,
    append_system_prompt: Option<String>,
    allow_recursion: Option<bool>,
    rlm_depth: u32,
    parent_agent: Option<String>,
    generic_mcp_servers: Vec<String>,
    memory: Option<MemoryRole>,
    messages_path: Option<String>,
    session_cwd: String,
    models: Models,
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
        let breakdown = Arc::new(system_prompt_breakdown(&self.options(&request)));
        *cache = Some((request, Arc::clone(&breakdown)));
        breakdown
    }

    fn options<'a>(&'a self, request: &'a RequestPrompt) -> BuildSystemPromptOptions<'a> {
        let session = &self.session;
        BuildSystemPromptOptions {
            custom_prompt: session.custom_prompt.clone(),
            model: request.model.as_deref(),
            vision_capable: request.vision_capable,
            selected_tools: Some(request.tools.iter().map(String::as_str).collect()),
            prompt_guidelines: Some(session.guidelines.clone()),
            append_system_prompt: session.append_system_prompt.clone(),
            cwd: request.cwd.clone(),
            messages_path: session.messages_path.clone(),
            context_files: session.context_files.clone(),
            skills: session.skills.clone(),
            allow_recursion: session.allow_recursion,
            rlm_depth: Some(session.rlm_depth),
            rlm_parent_agent: session.parent_agent.as_deref(),
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

/// The `eukhe.prompt` extension of a session.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let memory = deps.memory.as_ref().map(|_| deps.role.memory_role());
    let messages_path = match &deps.memory {
        Some(memory) => Some(memory.dir().display().to_string()),
        None => deps
            .prompt
            .conversation_log_path
            .as_ref()
            .or(deps.storage_dir.as_ref())
            .map(|path| path.display().to_string()),
    };
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
            append_system_prompt: deps.prompt.append_system_prompt.clone(),
            allow_recursion: deps.prompt.allow_recursion,
            rlm_depth: deps.role.rlm_depth,
            parent_agent: deps
                .role
                .parent
                .as_ref()
                .and_then(|parent| parent.agent_name.clone()),
            generic_mcp_servers: deps.generic_mcp_servers.clone(),
            memory,
            messages_path,
            session_cwd: deps.cwd.display().to_string(),
            models: deps.models.clone(),
        },
        cache: Mutex::new(None),
    });
    let sections = section_keys(memory)
        .into_iter()
        .map(|key| {
            let builder = Arc::clone(&builder);
            section(
                key,
                move |input: &PromptInput, _cx| {
                    futures::future::ready(Ok(builder.segment(input, key))).boxed()
                },
                Some(false),
            )
        })
        .collect();
    define_extension(Extension {
        name: PROMPT_EXTENSION.to_owned(),
        sections,
        ..Extension::default()
    })
}
