//! The first-run onboarding concern (moved with its concern): the
//! startup-model probe over the findInitialModel chain, the settings
//! sink behind the eukhe-tui onboarding trait, and the startup task
//! assembly the interactive launch mounts.

use super::{PathBuf, Result, RunOptions};

/// The startup-model resolution inputs (TS `findInitialModel`'s chain),
/// captured at task construction: the onboarding flow re-resolves the
/// model state at its own boundaries -- the branch (TS
/// `isOnboardingModelReady` at flow start) and the completion gate (TS
/// re-reads `getOnboardingState` before `markOnboardingShown`) -- because
/// the flow's own sign-in can change the answer.
#[derive(Clone)]
pub(super) struct StartupModelProbe {
    pub(super) cwd: PathBuf,
    pub(super) agent_dir: PathBuf,
    pub(super) cli_provider: Option<String>,
    pub(super) cli_model: Option<String>,
    /// The `--models` scope pattern list, resolved against the fresh
    /// catalog on every probe.
    pub(super) models: Option<Vec<String>>,
    pub(super) is_continuing: bool,
    /// An explicit `--api-key` counts as configured auth (it rides the
    /// resolved model's provider as a runtime key).
    pub(super) api_key: Option<String>,
}

impl StartupModelProbe {
    /// The resolution (TS `findInitialModel` + `isOnboardingModelReady`):
    /// the startup model, and whether it carries configured auth.
    fn resolve(&self) -> (Option<eukhe_types::ai::Model>, bool) {
        let settings = eukhe_core::settings::SettingsManager::create(&self.cwd, &self.agent_dir);
        let auth = eukhe_core::auth::AuthStorage::create(&self.agent_dir);
        let registry =
            eukhe_core::models::ModelRegistry::create(auth, self.agent_dir.join("models.json"));
        let all: Vec<eukhe_types::ai::Model> = registry.get_all().cloned().collect();
        let available: Vec<eukhe_types::ai::Model> =
            registry.get_available().into_iter().cloned().collect();
        let scoped = self
            .models
            .as_deref()
            .map(|patterns| {
                eukhe_core::models::resolve_model_scope_from_models(patterns, &available)
            })
            .unwrap_or_default();
        let startup_model =
            eukhe_core::models::find_initial_model(&eukhe_core::models::InitialModelOptions {
                cli_provider: self.cli_provider.as_deref(),
                cli_model: self.cli_model.as_deref(),
                scoped_models: &scoped,
                is_continuing: self.is_continuing,
                default_provider: settings.get_default_provider(),
                default_model_id: settings.get_default_model(),
                all_models: &all,
                available_models: &available,
            });
        let ready = match &startup_model {
            Some(model) => registry.has_configured_auth(model) || self.api_key.is_some(),
            None => false,
        };
        (startup_model, ready)
    }
}

/// Persistence for the first-run onboarding completion: the global
/// settings file (TS `markOnboardingShown` + flush).
pub(super) struct SettingsOnboardingSink {
    pub(super) cwd: PathBuf,
    pub(super) agent_dir: PathBuf,
}

impl eukhe_tui::interactive::OnboardingSink for SettingsOnboardingSink {
    fn onboarding_shown(&self) -> bool {
        eukhe_core::settings::SettingsManager::create(&self.cwd, &self.agent_dir)
            .get_onboarding_shown()
    }

    fn mark_onboarding_complete(&self) -> Result<()> {
        let mut settings =
            eukhe_core::settings::SettingsManager::create(&self.cwd, &self.agent_dir);
        settings.set_onboarding_shown(true)
    }
}

/// TS `shouldRunOnboarding`: first launch is defined by the settings flag
/// alone -- credentials found on disk (a Prime CLI token, an API key in
/// the environment) never skip the flow, they only make the sign-in step
/// instant. The task carries the startup model state (the resolved model
/// is TS `getCurrentModel` at flow time; the readiness probe decides the
/// branch and gates the completion marker), and the provider auth surface
/// the full flow signs in through. The startup model follows the TS
/// `findInitialModel` chain -- explicit flags, the `--models` scope, the
/// saved settings default, the featured default, the first available
/// model.
pub(super) fn onboarding_task(
    options: &RunOptions,
    provider_auth: Option<eukhe_tui::provider_auth::ProviderAuthCommandsHandle>,
) -> Option<eukhe_tui::interactive::OnboardingTask> {
    let config = &options.config;
    let settings = eukhe_core::settings::SettingsManager::create(&config.cwd, &config.agent_dir);
    if settings.get_onboarding_shown() {
        return None;
    }
    let probe = StartupModelProbe {
        cwd: config.cwd.clone(),
        agent_dir: config.agent_dir.clone(),
        cli_provider: config.provider.clone(),
        cli_model: config.model.clone(),
        models: config.models.clone(),
        // A fork launch resolves the startup model as a continuation
        // (#2806): the copy holds the source's rows.
        is_continuing: options.session.resume.is_some()
            || options.session.continue_recent
            || options.session.fork.is_some(),
        api_key: config.api_key.clone(),
    };
    let (current_model, _) = probe.resolve();
    let task = eukhe_tui::interactive::OnboardingTask {
        sink: std::sync::Arc::new(SettingsOnboardingSink {
            cwd: config.cwd.clone(),
            agent_dir: config.agent_dir.clone(),
        }),
        model_ready: std::sync::Arc::new(move || probe.resolve().1),
        current_model,
        provider_auth,
    };
    Some(task)
}
