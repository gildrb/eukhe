//! First-run onboarding surface (TS `PrimeOnboardingSplashComponent` +
//! `OnboardingChoiceComponent`): the welcome line and the flow panels
//! the full first-run flow mounts inside the block (the login dialog,
//! the team question, the connect-more providers picker).
//! [`OnboardingChoice`] is the reusable question panel (options with
//! optional detail subtitles, a row-width override, a seeded cursor); the
//! completion flag persists through [`crate::interactive::OnboardingSink`].
//!
//! A home with no usable model runs the full flow (TS
//! `runOnboardingFlow`'s not-ready branch) -- the welcome screen's
//! description and login action, then the flow panels in
//! [`crate::onboarding_flow`], one at a time.

use crate::keybindings::KeybindingsManager;
use crate::keys::KeyId;
use crate::onboarding_choice::{OnboardingChoice, OnboardingChoiceOption, OnboardingChoiceOptions};
use crate::onboarding_flow::{welcome_action_row, welcome_rows, OnboardingPanel};
use crate::style::{Modifier, Style};
use crate::theme::{Theme, ThemeColor};
use crate::{Line, Span};

/// The onboarding team question's prompt (TS `showPrimeTeamSelector`'s
/// onboarding arm mounts `OnboardingChoiceComponent` with this prompt).
pub const TEAM_QUESTION_PROMPT: &str = "Which account should Eukhe use?";
/// The onboarding team question's first row (TS the `Personal account`
/// option, index 0 -- the personal answer).
pub const PERSONAL_ACCOUNT_LABEL: &str = "Personal account";

/// The onboarding team question's rows (TS the options: the personal
/// account first, then one row per team with its slug as the dim
/// `@detail` identifier).
pub(crate) fn team_question_options(
    teams: &[crate::auth_panel::PrimeTeamOption],
) -> Vec<OnboardingChoiceOption> {
    let mut options = vec![OnboardingChoiceOption {
        label: PERSONAL_ACCOUNT_LABEL.to_string(),
        detail: None,
    }];
    options.extend(teams.iter().map(|team| {
        OnboardingChoiceOption {
            // The team fields are provider-supplied: the same control
            // character hygiene every daemon-supplied row carries (the
            // session team picker scrubs them the same way).
            label: crate::menu_panel::scrub_controls(&team.name),
            detail: team
                .slug
                .clone()
                .map(|slug| crate::menu_panel::scrub_controls(&slug)),
        }
    }));
    options
}

/// The onboarding team question's copy (TS the config: the prompt alone --
/// no description, no note).
pub(crate) fn team_question_config() -> OnboardingChoiceOptions {
    OnboardingChoiceOptions {
        prompt: Some(TEAM_QUESTION_PROMPT.to_string()),
        description: None,
        note: None,
        row_width: None,
    }
}

/// The outcome of one onboarding key press.
pub enum OnboardingDecision {
    /// Exit keys while onboarding owns the pane: quit the app.
    Exit,
    /// Enter on the welcome screen's login action (TS the splash's
    /// `onSelect`): the full flow starts.
    Begin,
    /// The connect-more-providers picker's answer (TS `onSelect` /
    /// `onContinue` / `onCancel`).
    Pick(crate::onboarding_flow::ProviderPick),
}

/// The onboarding pane state: the started flag (TS `flowStarted` -- the
/// welcome text and action never return once a flow owns the block),
/// and the mounted flow panel.
#[derive(Debug)]
pub struct OnboardingScreen {
    flow_started: bool,
    /// The mounted flow panel (TS `setPanel`'s top: the flow never nests
    /// its panels, so one slot covers the sequence).
    panel: Option<OnboardingPanel>,
}

impl OnboardingScreen {
    /// The full flow's splash (TS the plain `showOnboardingSplash`): the
    /// welcome text and the single login action, until Enter starts the
    /// flow.
    #[must_use]
    pub fn welcome() -> Self {
        Self {
            flow_started: false,
            panel: None,
        }
    }

    /// TS `setPanel`: mount one flow panel -- the flow has started from
    /// here on, and the welcome text never comes back.
    pub fn mount_panel(&mut self, panel: OnboardingPanel) {
        self.flow_started = true;
        self.panel = Some(panel);
    }

    /// Handle one key id (TS splash + mounted panel `handleInput`). `None`
    /// keeps the pane waiting. `osc_sink` carries a copy's OSC 52 fallback
    /// (the login dialog's URL copy).
    pub(crate) fn handle_key(
        &mut self,
        key: &KeyId,
        kb: &KeybindingsManager,
        osc_sink: &mut crate::clipboard::OscSink,
    ) -> Option<OnboardingDecision> {
        // Onboarding owns the pane before the editor exists, so its panels
        // answer the exit keys themselves (TS `isOnboardingExitKey`).
        if kb.matches(key, "app.clear") || kb.matches(key, "app.exit") {
            return Some(OnboardingDecision::Exit);
        }
        if let Some(panel) = self.panel.as_mut() {
            return panel.handle_key(key, kb, osc_sink);
        }
        // The welcome screen binds one key: Enter starts the flow (TS:
        // cancel is deliberately unbound -- signing in is the only way
        // forward).
        if !self.flow_started && kb.matches(key, "tui.select.confirm") {
            return Some(OnboardingDecision::Begin);
        }
        None
    }

    /// One paste payload (TS the mounted input's paste): the login dialog's
    /// field or the picker's search.
    pub fn handle_paste(&mut self, text: &str) {
        if let Some(panel) = self.panel.as_mut() {
            panel.handle_paste(text);
        }
    }

    /// Fold one auth-panel request into the mounted login dialog (the
    /// onboarding phase's channel arm -- the same folding the run loop's
    /// `apply_auth_panel_request` does for the session view): the render
    /// requests mount into the panel, and a request with no mounted
    /// dialog cancels its flow (the dropped oneshot reply, the same
    /// contract a closed terminal input had). The settled requests never
    /// arrive here: the onboarding flows settle through their own spawned
    /// futures, so past-the-dialog requests are a no-op.
    pub fn apply_auth_request(&mut self, request: crate::auth_panel::AuthPanelRequest) {
        use crate::auth_panel::AuthPanelRequest;
        match request {
            // TS `runPrimeInferenceLogin`'s guarded arm: "onboarding
            // narrates itself; step chatter stays in the chat flows" --
            // the callback's step lines never render on this surface,
            // while a direct `showProgress` line (the browser-sign-in
            // fallback) does.
            AuthPanelRequest::Progress { message, chatter } => {
                let Some(OnboardingPanel::Auth { panel, .. }) = self.panel.as_mut() else {
                    return;
                };
                if !chatter {
                    panel.push_progress(&message);
                }
            }
            // TS `showWaiting`: the dialog's own method carries no
            // onboarding guard -- the polling device flow's waiting line
            // renders on this surface too.
            AuthPanelRequest::Waiting { message } => {
                let Some(OnboardingPanel::Auth { panel, .. }) = self.panel.as_mut() else {
                    return;
                };
                panel.push_waiting(&message);
            }
            AuthPanelRequest::AuthUrl { url, instructions } => {
                let Some(OnboardingPanel::Auth { panel, .. }) = self.panel.as_mut() else {
                    return;
                };
                panel.show_auth_url(url, instructions);
            }
            AuthPanelRequest::Notice { message } => {
                let Some(OnboardingPanel::Auth { panel, .. }) = self.panel.as_mut() else {
                    return;
                };
                panel.show_notice(&message);
            }
            AuthPanelRequest::PastePrompt {
                prompt,
                tone,
                style,
                allow_empty,
                reply,
            } => {
                let Some(OnboardingPanel::Auth { panel, .. }) = self.panel.as_mut() else {
                    return;
                };
                panel.mount_paste(&prompt, tone, style, allow_empty, reply);
            }
            // TS `showPrimeTeamSelector`'s onboarding arm: the team
            // selection is a question in the onboarding selection
            // language (`OnboardingChoiceComponent`, no heading -- the
            // brand line returns), not the `/login` surface's team
            // picker.
            AuthPanelRequest::SelectTeam {
                teams,
                current,
                reply,
            } => {
                let seed = teams
                    .iter()
                    .position(|team| Some(team.team_id.as_str()) == current.as_deref())
                    .map_or(0, |position| position + 1);
                self.mount_panel(OnboardingPanel::TeamQuestion {
                    choice: OnboardingChoice::new(
                        team_question_options(&teams),
                        Some(seed),
                        team_question_config(),
                    ),
                    teams,
                    reply: Some(reply),
                });
            }
            AuthPanelRequest::ProviderSettled { .. } | AuthPanelRequest::McpSettled { .. } => {}
        }
    }

    /// The full pane frame (TS `PrimeOnboardingSplashComponent.render`).
    /// The keybindings manager feeds the mounted panel's hint row.
    pub(crate) fn render(
        &mut self,
        theme: &Theme,
        width: usize,
        height: usize,
        kb: &crate::keybindings::KeybindingsManager,
    ) -> Vec<Line> {
        let width = width.max(1);
        let mut lines: Vec<Line> = vec![Vec::new()];
        lines.push(self.heading_line(theme));
        // The welcome text and action render only before the flow starts;
        // once a panel owns the block, its rows mount directly under the
        // heading (TS: the panel brings its own leading padding, and it
        // indents its own content by one column -- panelLeft =
        // contentLeft - 1; contentLeft = PADDING_X = 1).
        match self.panel.as_mut() {
            None if !self.flow_started => {
                lines.extend(welcome_rows(theme, width));
                lines.push(welcome_action_row(theme, width));
            }
            // A started flow with no mounted panel keeps one blank row in
            // the gap (TS `if (!this.getActivePanel())`).
            None => lines.push(Vec::new()),
            Some(panel) => {
                let room = height.saturating_sub(lines.len());
                lines.extend(panel.render(theme, width, room, kb));
            }
        }
        while lines.len() < height {
            lines.push(Vec::new());
        }
        lines.truncate(height);
        lines
    }

    /// The block's heading (TS `renderHeadingLine`): the mounted panel
    /// that names itself replaces the brand line.
    fn heading_line(&self, theme: &Theme) -> Line {
        let heading = self.panel.as_ref().and_then(|panel| panel.heading());
        if let Some(heading) = heading {
            let mut row: Line = vec![Span::styled(" ".to_string(), Style::default())];
            row.push(Span::styled(
                heading.to_string(),
                theme
                    .fg_style(ThemeColor::Text)
                    .add_modifier(Modifier::BOLD),
            ));
            return row;
        }
        Self::brand_line(theme)
    }

    /// "Welcome to **eukhe**" (TS `renderBrandLine`), one column in from
    /// the pane edge.
    fn brand_line(theme: &Theme) -> Line {
        let text = theme.fg_style(ThemeColor::Text);
        let mut row: Line = vec![Span::styled(" ".to_string(), Style::default())];
        row.push(Span::styled("Welcome to ".to_string(), text));
        row.push(Span::styled(
            "eukhe".to_string(),
            text.add_modifier(Modifier::BOLD),
        ));
        row
    }
}

/// Greedy word wrap at `width` columns.
pub(crate) fn wrap_words(text: &str, width: usize) -> Vec<String> {
    let mut rows = Vec::new();
    let mut row = String::new();
    for word in text.split(' ') {
        if row.is_empty() {
            row = word.to_string();
        } else if row.chars().count() + 1 + word.chars().count() <= width {
            row.push(' ');
            row.push_str(word);
        } else {
            rows.push(std::mem::take(&mut row));
            row = word.to_string();
        }
        while row.chars().count() > width {
            let cut: String = row.chars().take(width).collect();
            rows.push(cut);
            row = row.chars().skip(width).collect();
        }
    }
    if !row.is_empty() {
        rows.push(row);
    }
    if rows.is_empty() {
        rows.push(String::new());
    }
    rows
}

#[cfg(test)]
mod tests {
    fn kb() -> crate::keybindings::KeybindingsManager {
        crate::keybindings::KeybindingsManager::new()
    }

    use super::*;
    use crate::theme::{ColorMode, Theme};

    /// TS `runPrimeInferenceLogin`'s guarded arm: the `onProgress`
    /// callback's step chatter never renders on the onboarding block
    /// ("onboarding narrates itself"), while the browser-fallback's
    /// direct line does.
    #[test]
    fn the_onboarding_fold_drops_step_chatter_keeps_direct_lines() {
        let mut screen = OnboardingScreen::welcome();
        screen.mount_panel(crate::onboarding_flow::OnboardingPanel::Auth {
            panel: std::boxed::Box::new(crate::auth_panel::AuthPanel::onboarding(
                "Login to Prime Inference",
            )),
            heading: Some(crate::onboarding_flow::EUKHE_LOGIN_HEADING.to_string()),
        });
        screen.apply_auth_request(crate::auth_panel::AuthPanelRequest::Progress {
            message: "Generating the browser challenge...".to_string(),
            chatter: true,
        });
        let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
        let rows = screen.render(&theme, 80, 24, &kb());
        let text = rows
            .iter()
            .map(|line| {
                line.iter()
                    .map(|span| span.content.clone())
                    .collect::<String>()
            })
            .collect::<Vec<_>>();
        assert!(
            !text
                .iter()
                .any(|row| row.contains("Generating the browser challenge")),
            "the step chatter stays out of the onboarding block: {text:?}"
        );
        assert!(
            !text
                .iter()
                .any(|row| row.contains("Preparing authentication")),
            "no progress block opened: {text:?}"
        );
        screen.apply_auth_request(crate::auth_panel::AuthPanelRequest::Progress {
            message: "Browser sign-in unavailable (mock).".to_string(),
            chatter: false,
        });
        let rows = screen.render(&theme, 80, 24, &kb());
        let text = rows
            .iter()
            .map(|line| {
                line.iter()
                    .map(|span| span.content.clone())
                    .collect::<String>()
            })
            .collect::<Vec<_>>();
        assert!(
            text.iter()
                .any(|row| row.contains("Browser sign-in unavailable (mock).")),
            "the direct fallback line renders: {text:?}"
        );
    }

    /// TS `showWaiting` (the Copilot device flow's status): the dialog's
    /// own method carries no onboarding guard, so the waiting line
    /// renders on this surface too -- below the browser URL block (the
    /// `onProgress` chatter the fold drops never reaches the panel).
    #[test]
    fn the_onboarding_fold_renders_the_device_flow_waiting_line() {
        let mut screen = OnboardingScreen::welcome();
        screen.mount_panel(crate::onboarding_flow::OnboardingPanel::Auth {
            panel: std::boxed::Box::new(crate::auth_panel::AuthPanel::onboarding(
                "Login to GitHub Copilot",
            )),
            heading: Some(crate::onboarding_flow::EUKHE_LOGIN_HEADING.to_string()),
        });
        screen.apply_auth_request(crate::auth_panel::AuthPanelRequest::AuthUrl {
            url: "https://fixture.example/device".to_string(),
            instructions: None,
        });
        screen.apply_auth_request(crate::auth_panel::AuthPanelRequest::Waiting {
            message: "Waiting for browser authentication...".to_string(),
        });
        let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
        let rows = screen.render(&theme, 80, 24, &kb());
        let text = rows
            .iter()
            .map(|line| {
                line.iter()
                    .map(|span| span.content.clone())
                    .collect::<String>()
            })
            .collect::<Vec<_>>();
        let url = text
            .iter()
            .position(|row| row.contains("fixture.example/device"))
            .expect("the url row");
        let waiting = text
            .iter()
            .position(|row| row.contains("Waiting for browser authentication"))
            .expect("the waiting row");
        assert!(
            waiting > url,
            "the waiting line rides below the URL block: {text:?}"
        );
    }

    /// TS `showPrimeTeamSelector`'s onboarding arm: the `SelectTeam`
    /// request mounts the onboarding choice question (the brand line
    /// returns -- no heading) with the personal account first and the
    /// teams' slugs as their dim identifiers, seeded on the stored
    /// selection; Enter answers the request's oneshot.
    #[test]
    fn the_team_selection_mounts_the_onboarding_choice_question() {
        use crate::auth_panel::{AuthPanelRequest, PrimeTeamOption, PrimeTeamPick};
        let mut screen = OnboardingScreen::welcome();
        screen.mount_panel(crate::onboarding_flow::OnboardingPanel::Auth {
            panel: std::boxed::Box::new(crate::auth_panel::AuthPanel::onboarding(
                "Login to Prime Inference",
            )),
            heading: Some(crate::onboarding_flow::EUKHE_LOGIN_HEADING.to_string()),
        });
        let (reply, answer) = tokio::sync::oneshot::channel();
        screen.apply_auth_request(AuthPanelRequest::SelectTeam {
            teams: vec![
                PrimeTeamOption {
                    team_id: "team-acme".to_string(),
                    name: "Acme Corp".to_string(),
                    slug: Some("acme".to_string()),
                    role: Some("Owner".to_string()),
                    created_at: None,
                },
                PrimeTeamOption {
                    team_id: "team-beta".to_string(),
                    name: "Beta Team".to_string(),
                    slug: None,
                    role: None,
                    created_at: None,
                },
            ],
            current: Some("team-beta".to_string()),
            reply,
        });
        let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
        let rows = screen.render(&theme, 80, 24, &kb());
        let text = rows
            .iter()
            .map(|line| {
                line.iter()
                    .map(|span| span.content.clone())
                    .collect::<String>()
            })
            .collect::<Vec<_>>();
        // The heading reverted to the brand line (TS: the choice mounts
        // without a heading).
        assert!(
            text.iter().any(|row| row.contains("Welcome to ")),
            "the brand line returns over the team question: {text:?}"
        );
        assert!(
            !text
                .iter()
                .any(|row| row.contains(crate::onboarding_flow::EUKHE_LOGIN_HEADING)),
            "no login heading rides the question: {text:?}"
        );
        // The question frame: the prompt, the personal account first, the
        // teams with their slug identifiers, the stored team seeded.
        assert!(
            text.iter().any(|row| row.contains(TEAM_QUESTION_PROMPT)),
            "the TS prompt: {text:?}"
        );
        let seed = text
            .iter()
            .find(|row| row.contains("> Beta Team"))
            .expect("the stored team is seeded");
        assert!(
            seed.starts_with(" > Beta Team"),
            "the seeded row renders in the selection language: {seed:?}"
        );
        assert!(
            text.iter().any(|row| row.contains("  Personal account")),
            "the personal row rides first: {text:?}"
        );
        assert!(
            text.iter().any(|row| row.contains("@acme")),
            "the team slug renders as the dim identifier: {text:?}"
        );
        // Enter answers the seeded row (Beta) through the oneshot.
        let kb = crate::keybindings::KeybindingsManager::new();
        let mut sink = crate::clipboard::OscSink::Buffer(Vec::new());
        screen.handle_key(&crate::keys::KeyId::from("enter"), &kb, &mut sink);
        match answer.blocking_recv().expect("the pick answered") {
            PrimeTeamPick::Team(team) => assert_eq!(team.team_id, "team-beta"),
            other => panic!("the seeded team answered, got {other:?}"),
        }
    }
}
