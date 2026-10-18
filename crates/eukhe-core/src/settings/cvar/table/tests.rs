use serde::de::DeserializeOwned;
use serde_json::Value;

use super::*;
use crate::settings::types::{
    AutoRefineSettings, AutonomousLimitSetting, AutonomousSettings, BranchSummarySettings,
    CompactionSettings, DirectorSettings, FactorySettings, FallbackChainsSettings, GatewaySettings,
    ImageSettings, MarkdownSettings, MemorySettings, MermaidRenderingMode, ModelRolesSettings,
    ProviderRetrySettings, ProviderWaitSettings, ProvidersSettings, QueueModeSetting,
    RetryFailoverSettings, RetrySettings, Settings, ShellSettings, SignalGatewaySettings,
    SshSettings, StreamPaceSettings, SttSettings, TerminalSettings, ThinkingBudgetsSettings,
    ThinkingLevelSetting, TitleSettings, TransportSetting, TtsSettings, WarningSettings,
};

/// Every field set; no `..`, so a new settings field does not compile
/// until it is filled here (and then declared in the table).
fn populated() -> Settings {
    let limit = || Some(AutonomousLimitSetting::Number(1.0));
    Settings {
        onboarding_shown: Some(true),
        onboarding_completed: Some(true),
        default_provider: Some("p".into()),
        default_model: Some("m".into()),
        subagent_default_model: Some("m".into()),
        recent_models: Some(vec![]),
        auxiliary_model: Some("m".into()),
        default_thinking_level: Some(ThinkingLevelSetting::High),
        default_service_tier: Some("flex".into()),
        rlm_max_depth: Some(1),
        provider_max_in_flight: Some(std::collections::BTreeMap::new()),
        provider_max_queued: Some(1),
        subagent_max_concurrency: Some(1),
        subagent_stall_ms: Some(1),
        tool_blocking_budget_ms: Some(1),
        max_tool_rounds: Some(1),
        idle_eviction_minutes: Some(Value::from(1)),
        session_archive_max_age_days: Some(Value::from(1)),
        session_archive_max_sessions: Some(Value::from(1)),
        transport: Some(TransportSetting::Sse),
        steering_mode: Some(QueueModeSetting::All),
        follow_up_mode: Some(QueueModeSetting::All),
        theme: Some("t".into()),
        compaction: Some(CompactionSettings {
            enabled: Some(true),
            reserve_tokens: Some(1),
            keep_recent_tokens: Some(1),
            agent_callable: Some(true),
            provider_token_count: Some(true),
        }),
        memory: Some(MemorySettings {
            model: Some("m".into()),
            thinking: Some(ThinkingLevelSetting::Low),
            settle_timeout_ms: Some(1),
        }),
        auto_refine: Some(AutoRefineSettings {
            enabled: Some(true),
            turn_interval: Some(1),
            compact: Some(true),
            cooldown_ms: Some(1),
        }),
        factory: Some(FactorySettings {
            enabled: Some(true),
        }),
        branch_summary: Some(BranchSummarySettings {
            reserve_tokens: Some(1),
            skip_prompt: Some(true),
        }),
        retry: Some(RetrySettings {
            enabled: Some(true),
            max_retries: Some(1),
            base_delay_ms: Some(1),
            failover: Some(RetryFailoverSettings {
                enabled: Some(true),
                max_retries: Some(1),
                base_delay_ms: Some(1),
                max_delay_ms: Some(1),
            }),
            provider: Some(ProviderRetrySettings {
                timeout_ms: Some(1),
                max_retry_delay_ms: Some(1),
                stream_idle_timeout_ms: Some(1),
                stream_repeat_limit: Some(1),
                wait_for_usage: Some(ProviderWaitSettings {
                    enabled: Some(true),
                    base_delay_ms: Some(1),
                    max_delay_ms: Some(1),
                    max_attempts: Some(1),
                    max_wait_ms: Some(1),
                    pause_until_reset: Some(true),
                    max_pause_ms: Some(1),
                    max_parks: Some(1),
                }),
            }),
            fallback_chains: Some(FallbackChainsSettings {
                tiny: Some(vec![]),
                judge: Some(vec![]),
                translate: Some(vec![]),
                speech: Some(vec![]),
                dictation: Some(vec![]),
            }),
        }),
        provider_backup_model: Some("m".into()),
        image_model: Some("m".into()),
        autonomous: Some(AutonomousSettings {
            max_continuations: limit(),
            max_turns: limit(),
            max_tokens: limit(),
            timeout_ms: limit(),
        }),
        directors: Some(DirectorSettings {
            stack_cap: Some(1),
            max_steps: Some(1),
        }),
        shell_path: Some("s".into()),
        quiet_startup: Some(true),
        shell_command_prefix: Some("s".into()),
        npm_command: Some(vec![]),
        mcp_servers: Some(serde_json::Map::new()),
        mcp_catalog_sources: Some(vec![]),
        packages: Some(vec![]),
        skills: Some(vec![]),
        prompts: Some(vec![]),
        themes: Some(vec![]),
        enable_skill_commands: Some(true),
        enable_builtin_skills: Some(true),
        terminal: Some(TerminalSettings {
            show_images: Some(true),
            clear_on_shrink: Some(true),
            show_terminal_progress: Some(true),
            show_speed: Some(true),
            fullscreen: Some(true),
            stream_pace: Some(StreamPaceSettings {
                min_chars: Some(1),
                lag: Some(1),
            }),
        }),
        images: Some(ImageSettings {
            auto_resize: Some(true),
            block_images: Some(true),
        }),
        enabled_models: Some(vec![]),
        allowed_models: Some(vec![]),
        tree_filter_mode: Some("all".into()),
        chat_detail: Some("all".into()),
        thinking_budgets: Some(ThinkingBudgetsSettings {
            minimal: Some(1),
            low: Some(1),
            medium: Some(1),
            high: Some(1),
        }),
        editor_padding_x: Some(1),
        autocomplete_max_visible: Some(1),
        show_hardware_cursor: Some(true),
        markdown: Some(MarkdownSettings {
            code_block_indent: Some(" ".into()),
            mermaid: Some(MermaidRenderingMode::Off),
        }),
        warnings: Some(WarningSettings {
            anthropic_extra_usage: Some(true),
        }),
        session_dir: Some("d".into()),
        request_timing: Some(true),
        trusted_projects: Some(vec![]),
        gateway: Some(GatewaySettings {
            signal: Some(SignalGatewaySettings {
                account: Some("a".into()),
                allow: Some(vec![]),
                cli_path: Some("c".into()),
                cwd: Some("d".into()),
            }),
        }),
        kernel_transport: Some(Value::from(1)),
        shell: Some(ShellSettings {
            auto_effects: Some(vec![]),
        }),
        ssh: Some(SshSettings {
            hosts: Some(vec![]),
        }),
        model_roles: Some(ModelRolesSettings {
            tiny: Some("m".into()),
            judge: Some("m".into()),
            translate: Some("m".into()),
            speech: Some("m".into()),
            dictation: Some("m".into()),
        }),
        providers: Some(ProvidersSettings {
            device: Some("cpu".into()),
            dtype: Some("q4".into()),
            runtime_library: Some("l".into()),
        }),
        titles: Some(TitleSettings {
            generate: Some(true),
        }),
        tts: Some(TtsSettings {
            local_voice: Some("af_heart".into()),
        }),
        stt: Some(SttSettings {
            enabled: Some(true),
        }),
        extra: serde_json::Map::new(),
    }
}

/// The dotted paths of the leaves of `value`: a scalar, an array, or an
/// empty object (a map setting) ends a path.
fn leaves(prefix: &str, value: &Value, out: &mut Vec<String>) {
    match value {
        Value::Object(fields) if !fields.is_empty() => {
            for (key, field) in fields {
                let path = if prefix.is_empty() {
                    key.clone()
                } else {
                    format!("{prefix}.{key}")
                };
                leaves(&path, field, out);
            }
        }
        Value::Null
        | Value::Bool(_)
        | Value::Number(_)
        | Value::String(_)
        | Value::Array(_)
        | Value::Object(_) => out.push(prefix.to_string()),
    }
}

#[test]
fn every_settings_leaf_is_declared_once() {
    let document = serde_json::to_value(populated()).expect("settings serialize");
    let mut found = Vec::new();
    leaves("", &document, &mut found);
    found.sort();
    let mut declared: Vec<String> = DECLS.iter().map(|decl| decl.id.to_string()).collect();
    declared.sort();
    assert_eq!(declared, found);
}

/// Every option of `decl` reads as a value of `T` (the getters parse the
/// cvar's text into the settings enum).
fn options_parse<T: DeserializeOwned>(decl: &Decl) -> Vec<(&'static str, bool)> {
    let CvarType::Choice(options) = decl.ty else {
        return Vec::new();
    };
    options
        .iter()
        .filter(|option| !option.is_empty())
        .map(|option| {
            (
                *option,
                serde_json::from_value::<T>(Value::String((*option).to_string())).is_ok(),
            )
        })
        .collect()
}

#[test]
fn every_choice_option_is_a_value_of_its_enum() {
    let checked = [
        options_parse::<QueueModeSetting>(&STEERING_MODE),
        options_parse::<QueueModeSetting>(&FOLLOW_UP_MODE),
        options_parse::<TransportSetting>(&TRANSPORT),
        options_parse::<ThinkingLevelSetting>(&MEMORY_THINKING),
        options_parse::<ThinkingLevelSetting>(&DEFAULT_THINKING_LEVEL),
        options_parse::<eukhe_types::ai::ServiceTier>(&DEFAULT_SERVICE_TIER),
        options_parse::<MermaidRenderingMode>(&MARKDOWN_MERMAID),
    ];
    let failed: Vec<&str> = checked
        .iter()
        .flatten()
        .filter(|(_, parses)| !parses)
        .map(|(option, _)| *option)
        .collect();
    assert_eq!(failed, Vec::<&str>::new());
    assert!(checked.iter().all(|options| !options.is_empty()));
}
