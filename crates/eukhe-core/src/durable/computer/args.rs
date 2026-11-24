//! The computer tools' arguments, parsed once into the desktop's types:
//! the window a call names, what an observation takes, and the steps of
//! an act with the consequential action each names.

use eukhe_desktop::{FindQuery, Step, TreeOptions, WindowFilter, WindowId, WindowSelector};
use serde::Deserialize;

use crate::settings::types::Consequence;

/// A call's arguments that do not parse.
#[derive(Debug, thiserror::Error)]
pub(super) enum ArgError {
    #[error("invalid arguments: {0}")]
    Json(#[from] serde_json::Error),
    #[error("invalid arguments: `window` takes `id`, or `app` and `title`, not both")]
    IdWithFilter,
}

/// `window`: an id from `computer_windows`, or a filter that must match
/// exactly one window.
#[derive(Debug, Deserialize)]
struct WindowArg {
    #[serde(default)]
    id: Option<WindowId>,
    #[serde(default)]
    app: Option<String>,
    #[serde(default)]
    title: Option<String>,
}

impl TryFrom<WindowArg> for WindowSelector {
    type Error = ArgError;

    fn try_from(arg: WindowArg) -> Result<Self, ArgError> {
        match arg {
            WindowArg {
                id: Some(id),
                app: None,
                title: None,
            } => Ok(Self::Id(id)),
            WindowArg {
                id: Some(_),
                app: Some(_),
                ..
            }
            | WindowArg {
                id: Some(_),
                title: Some(_),
                ..
            } => Err(ArgError::IdWithFilter),
            WindowArg {
                id: None,
                app,
                title,
            } => Ok(Self::Filter(WindowFilter { app, title })),
        }
    }
}

const fn yes() -> bool {
    true
}

#[derive(Debug, Deserialize)]
struct ObserveArgs {
    window: WindowArg,
    #[serde(default = "yes")]
    screenshot: bool,
    #[serde(default = "yes")]
    tree: bool,
    #[serde(default)]
    max_depth: Option<u32>,
    #[serde(default)]
    find: Option<FindQuery>,
}

/// Whether an observation takes a screenshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Shot {
    Take,
    Skip,
}

/// What an observation reads of the window's elements.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum View {
    Tree(TreeOptions),
    /// Only the matching elements, instead of the tree.
    Find(FindQuery),
    Nothing,
}

/// One `computer_observe` call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Observe {
    pub(super) window: WindowSelector,
    pub(super) shot: Shot,
    pub(super) view: View,
}

/// The tree an observation reads by default: every interesting element,
/// down to `max_depth`.
pub(super) fn tree(max_depth: Option<u32>) -> TreeOptions {
    TreeOptions {
        max_depth,
        ..TreeOptions::default()
    }
}

impl Observe {
    pub(super) fn parse(args: serde_json::Value) -> Result<Self, ArgError> {
        let ObserveArgs {
            window,
            screenshot,
            tree: read_tree,
            max_depth,
            find,
        } = serde_json::from_value(args)?;
        let view = match (find, read_tree) {
            (Some(query), _) => View::Find(query),
            (None, true) => View::Tree(tree(max_depth)),
            (None, false) => View::Nothing,
        };
        Ok(Self {
            window: window.try_into()?,
            shot: if screenshot { Shot::Take } else { Shot::Skip },
            view,
        })
    }
}

/// One step of an act, with the consequential action it names, if any.
#[derive(Debug, Clone, PartialEq, Deserialize)]
pub(super) struct ActStep {
    #[serde(default)]
    pub(super) consequence: Option<Consequence>,
    #[serde(flatten)]
    pub(super) step: Step,
}

#[derive(Debug, Deserialize)]
struct ActArgs {
    window: WindowArg,
    steps: Vec<ActStep>,
    #[serde(default = "yes")]
    observe_after: bool,
}

/// Whether an act observes its window after its steps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum After {
    Observe,
    Skip,
}

/// One `computer_act` call.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Act {
    pub(super) window: WindowSelector,
    pub(super) steps: Vec<ActStep>,
    pub(super) after: After,
}

impl Act {
    pub(super) fn parse(args: serde_json::Value) -> Result<Self, ArgError> {
        let ActArgs {
            window,
            steps,
            observe_after,
        } = serde_json::from_value(args)?;
        Ok(Self {
            window: window.try_into()?,
            steps,
            after: if observe_after {
                After::Observe
            } else {
                After::Skip
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use eukhe_desktop::ElementRef;
    use serde_json::json;

    use super::*;

    fn target(reference: &str) -> ElementRef {
        reference
            .parse()
            .unwrap_or_else(|error| panic!("{reference}: {error:?}"))
    }

    /// `window` names an id or a filter; both at once is refused.
    #[test]
    fn a_window_is_an_id_or_a_filter() {
        let parse = |window: serde_json::Value| {
            Observe::parse(json!({ "window": window })).map(|observe| observe.window)
        };
        assert_eq!(
            parse(json!({ "id": "42" })).ok(),
            Some(WindowSelector::Id(WindowId::new("42")))
        );
        assert_eq!(
            parse(json!({ "app": "TextEdit" })).ok(),
            Some(WindowSelector::Filter(WindowFilter {
                app: Some("TextEdit".to_owned()),
                title: None
            }))
        );
        assert!(matches!(
            parse(json!({ "id": "42", "title": "Notes" })),
            Err(ArgError::IdWithFilter)
        ));
    }

    /// An observation takes a screenshot and the tree unless told not to;
    /// `find` replaces the tree.
    #[test]
    fn an_observation_defaults_to_screenshot_and_tree() {
        let parse = |args: serde_json::Value| {
            Observe::parse(args).map(|observe| (observe.shot, observe.view))
        };
        let window = json!({ "id": "1" });
        let query = FindQuery {
            role: Some("button".to_owned()),
            ..FindQuery::default()
        };
        assert_eq!(
            [
                parse(json!({ "window": window })).ok(),
                parse(json!({ "window": window, "screenshot": false, "max_depth": 3 })).ok(),
                parse(json!({ "window": window, "tree": false })).ok(),
                parse(json!({ "window": window, "find": { "role": "button" } })).ok(),
            ],
            [
                Some((Shot::Take, View::Tree(tree(None)))),
                Some((Shot::Skip, View::Tree(tree(Some(3))))),
                Some((Shot::Take, View::Nothing)),
                Some((Shot::Take, View::Find(query))),
            ]
        );
    }

    /// Each step decodes as the desktop's step beside the consequential
    /// action it names; the intent `i` the harness adds is ignored.
    #[test]
    fn act_steps_carry_their_consequence() {
        let act = Act::parse(json!({
            "i": "Sending the draft",
            "window": { "app": "Mail" },
            "steps": [
                { "type": "set_value", "target": "e3", "value": "hi" },
                { "type": "press", "target": "e9", "consequence": "send" }
            ],
            "observe_after": false
        }));
        assert_eq!(
            act.ok(),
            Some(Act {
                window: WindowSelector::Filter(WindowFilter {
                    app: Some("Mail".to_owned()),
                    title: None
                }),
                steps: vec![
                    ActStep {
                        consequence: None,
                        step: Step::SetValue {
                            target: target("e3"),
                            value: "hi".to_owned()
                        }
                    },
                    ActStep {
                        consequence: Some(Consequence::Send),
                        step: Step::Press {
                            target: target("e9")
                        }
                    },
                ],
                after: After::Skip,
            })
        );
        assert!(Act::parse(json!({
            "window": { "id": "1" },
            "steps": [{ "type": "press", "target": "e1", "consequence": "wire_money" }]
        }))
        .is_err());
    }
}
