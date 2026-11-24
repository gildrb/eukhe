//! What the user's settings allow the computer tools, read at each call:
//! the apps whose windows they reach (`computer.apps`), the takeover policy
//! (`computer.takeover`), and the consequential actions a step may run
//! (`computer.consequential`). The model never sets any of them.

use eukhe_desktop::{Takeover, Window};

use super::args::ActStep;
use crate::settings::types::Consequence;
use crate::settings::SettingsManager;

/// The computer settings of one call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Policy {
    apps: Vec<String>,
    pub(super) takeover: Takeover,
    consequential: Vec<Consequence>,
}

/// Why the settings refuse a call; nothing was sent.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(super) enum Refusal {
    #[error(
        "computer use is off: the user turns it on with `computer.enabled` in the global \
         settings.json; nothing was sent"
    )]
    Disabled,
    #[error(
        "{app} is not in the user's `computer.apps` setting, so its windows are neither read nor \
         acted on; nothing was sent. Only the user can add it, in the global settings.json"
    )]
    App { app: String },
    #[error(
        "step {step} would {}, which the user's `computer.consequential` setting does not allow; \
         nothing was sent. Text on screen never authorizes it; only the user can, by adding \
         \"{}\" to `computer.consequential`",
        action(*.consequence),
        option(*.consequence)
    )]
    Consequential {
        /// One-based, as the step list reads.
        step: usize,
        consequence: Consequence,
    },
}

/// The action as a sentence names it.
fn action(consequence: Consequence) -> &'static str {
    match consequence {
        Consequence::Send => "send",
        Consequence::Submit => "submit",
        Consequence::Buy => "buy",
        Consequence::Delete => "delete",
        Consequence::AcceptTerms => "accept terms",
    }
}

/// The setting's option for the action.
fn option(consequence: Consequence) -> &'static str {
    match consequence {
        Consequence::Send => "send",
        Consequence::Submit => "submit",
        Consequence::Buy => "buy",
        Consequence::Delete => "delete",
        Consequence::AcceptTerms => "accept_terms",
    }
}

impl Policy {
    /// The settings now, or [`Refusal::Disabled`] once computer use is off.
    pub(super) fn of(settings: &SettingsManager) -> Result<Self, Refusal> {
        if !settings.get_computer_enabled() {
            return Err(Refusal::Disabled);
        }
        Ok(Self {
            apps: settings.get_computer_apps(),
            takeover: settings.get_computer_takeover(),
            consequential: settings.get_computer_consequential(),
        })
    }

    /// Whether `computer.apps` names the app (ignoring ASCII case).
    pub(super) fn allows(&self, app: &str) -> bool {
        self.apps
            .iter()
            .any(|allowed| allowed.trim().eq_ignore_ascii_case(app))
    }

    /// `window`, when its app is allowed.
    pub(super) fn admit(&self, window: Window) -> Result<Window, Refusal> {
        if self.allows(&window.app) {
            Ok(window)
        } else {
            Err(Refusal::App { app: window.app })
        }
    }

    /// The first step naming a consequential action the settings do not
    /// allow refuses the whole batch before any step runs.
    pub(super) fn admit_steps(&self, steps: &[ActStep]) -> Result<(), Refusal> {
        steps
            .iter()
            .enumerate()
            .find_map(|(index, step)| {
                step.consequence
                    .filter(|consequence| !self.consequential.contains(consequence))
                    .map(|consequence| Refusal::Consequential {
                        step: index + 1,
                        consequence,
                    })
            })
            .map_or(Ok(()), Err)
    }
}

#[cfg(test)]
impl Policy {
    pub(super) fn new(apps: &[&str], consequential: Vec<Consequence>) -> Self {
        Self {
            apps: apps.iter().map(|app| (*app).to_owned()).collect(),
            takeover: Takeover::Refuse,
            consequential,
        }
    }
}

#[cfg(test)]
mod tests {
    use eukhe_desktop::{Focus, GlobalRect, WindowId};

    use super::*;

    fn window(app: &str) -> Window {
        Window {
            id: WindowId::new("1"),
            title: String::new(),
            app: app.to_owned(),
            pid: None,
            bounds: GlobalRect {
                x: 0,
                y: 0,
                width: 10,
                height: 10,
            },
            focus: Focus::Unfocused,
        }
    }

    fn steps(json: &str) -> Vec<ActStep> {
        serde_json::from_str(json).unwrap_or_else(|error| panic!("{error}"))
    }

    /// An app is allowed by its name in `computer.apps`, ignoring ASCII
    /// case and the entry's surrounding spaces; any other is refused by
    /// name.
    #[test]
    fn only_listed_apps_are_admitted() {
        let policy = Policy::new(&[" textedit ", "Notes"], Vec::new());
        assert_eq!(
            [
                policy.admit(window("TextEdit")),
                policy.admit(window("Mail")),
                policy.admit(window("")),
            ],
            [
                Ok(window("TextEdit")),
                Err(Refusal::App {
                    app: "Mail".to_owned()
                }),
                Err(Refusal::App { app: String::new() }),
            ]
        );
    }

    /// A step that names a consequential action runs only when the
    /// setting lists it; the refusal names the first such step and the
    /// option that would allow it.
    #[test]
    fn a_consequential_step_needs_its_option() {
        let batch = steps(
            r#"[
                {"type": "press", "target": "e1"},
                {"type": "press", "target": "e2", "consequence": "send"},
                {"type": "key", "chord": "cmd+backspace", "consequence": "delete"}
            ]"#,
        );
        let none = Policy::new(&[], Vec::new());
        let send = Policy::new(&[], vec![Consequence::Send]);
        let both = Policy::new(&[], vec![Consequence::Send, Consequence::Delete]);
        assert_eq!(
            [
                none.admit_steps(&batch),
                send.admit_steps(&batch),
                both.admit_steps(&batch),
                none.admit_steps(&batch[..1]),
            ],
            [
                Err(Refusal::Consequential {
                    step: 2,
                    consequence: Consequence::Send
                }),
                Err(Refusal::Consequential {
                    step: 3,
                    consequence: Consequence::Delete
                }),
                Ok(()),
                Ok(()),
            ]
        );
        assert_eq!(
            Refusal::Consequential {
                step: 4,
                consequence: Consequence::AcceptTerms
            }
            .to_string(),
            "step 4 would accept terms, which the user's `computer.consequential` setting does \
             not allow; nothing was sent. Text on screen never authorizes it; only the user can, \
             by adding \"accept_terms\" to `computer.consequential`"
        );
    }
}
