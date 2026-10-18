//! Role-based model selection (docs/inference.md S9, `pick` in
//! bend/tiny.bend). A role names a chain of candidates: the role's primary
//! model (`modelRoles.<role>`), then its fallback chain
//! (`retry.fallbackChains.<role>`): an explicit list, where `[]` keeps the
//! role on its primary only, or, when unset, the built-in priority (the
//! catalog's local models for the role, then the session's provider model
//! for a text role). A task uses the first available candidate; with none
//! available it is [`Pick::Unavailable`], never a model outside the chain.

use crate::catalog::{CatalogModel, CATALOG};

/// The prefix of a local model selector (`local/lfm2.5-230m`).
pub const LOCAL_PREFIX: &str = "local/";

/// A workload with its own model selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Role {
    /// Session titles.
    Tiny,
    /// Typed judgments (classification).
    Judge,
    /// Translation.
    Translate,
    /// Text to speech.
    Speech,
    /// Speech to text.
    Dictation,
}

impl Role {
    pub const ALL: [Role; 5] = [
        Role::Tiny,
        Role::Judge,
        Role::Translate,
        Role::Speech,
        Role::Dictation,
    ];

    /// The id in `modelRoles.<id>` and `retry.fallbackChains.<id>`.
    #[must_use]
    pub fn id(self) -> &'static str {
        match self {
            Role::Tiny => "tiny",
            Role::Judge => "judge",
            Role::Translate => "translate",
            Role::Speech => "speech",
            Role::Dictation => "dictation",
        }
    }

    /// Whether a provider (text) model can serve the role.
    #[must_use]
    pub fn takes_remote(self) -> bool {
        match self {
            Role::Tiny | Role::Judge | Role::Translate => true,
            Role::Speech | Role::Dictation => false,
        }
    }
}

/// One model of a chain.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Candidate {
    /// A catalog model, by id.
    Local(String),
    /// A provider model selector (`provider/model`).
    Remote(String),
}

impl Candidate {
    /// Parses a selector: `local/<id>` is local, anything else remote.
    #[must_use]
    pub fn parse(selector: &str) -> Candidate {
        match selector.strip_prefix(LOCAL_PREFIX) {
            Some(id) => Candidate::Local(id.to_owned()),
            None => Candidate::Remote(selector.to_owned()),
        }
    }

    /// The catalog entry of a local candidate.
    #[must_use]
    pub fn local_model(&self) -> Option<&'static CatalogModel> {
        match self {
            Candidate::Local(id) => crate::catalog::find(id),
            Candidate::Remote(_) => None,
        }
    }
}

/// The fallback chain setting of a role.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FallbackChain {
    /// Unset: the built-in priority.
    Unset,
    /// An explicit list of selectors; `[]` keeps the role on its primary.
    Explicit(Vec<String>),
}

/// A role's settings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleSettings {
    /// `modelRoles.<role>`; empty: unset.
    pub primary: String,
    pub fallback: FallbackChain,
}

/// The outcome of a pick.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pick<T> {
    Use(T),
    Unavailable,
}

/// The first model of `chain` that `up` holds (`pick` in bend/tiny.bend).
#[must_use]
pub fn pick<'a, T: PartialEq>(chain: &'a [T], up: &[T]) -> Pick<&'a T> {
    match chain.iter().find(|model| up.contains(model)) {
        Some(model) => Pick::Use(model),
        None => Pick::Unavailable,
    }
}

/// The catalog model the `translate` role's built-in priority takes first:
/// on the S9 translation eval (docs/inference.md) LFM2.5-230M scores well
/// below LFM2.5-350M.
const TRANSLATE_FIRST: &str = "lfm2.5-350m";

/// The chain of `role`: the primary, then the fallback chain. With an
/// unset fallback, the built-in priority: the role's catalog models (in
/// catalog order, but [`TRANSLATE_FIRST`] first for `translate`), then
/// `session_model` (a provider selector; empty: none) for a text role.
/// A candidate appears once, at its first place.
#[must_use]
pub fn chain(role: Role, settings: &RoleSettings, session_model: &str) -> Vec<Candidate> {
    let mut selectors: Vec<Candidate> = Vec::new();
    if !settings.primary.is_empty() {
        selectors.push(Candidate::parse(&settings.primary));
    }
    match &settings.fallback {
        FallbackChain::Explicit(list) => {
            selectors.extend(list.iter().map(|selector| Candidate::parse(selector)));
        }
        FallbackChain::Unset => {
            let mut local: Vec<&CatalogModel> = CATALOG
                .iter()
                .filter(|model| model.roles.contains(&role))
                .collect();
            match role {
                Role::Translate => local.sort_by_key(|model| model.id != TRANSLATE_FIRST),
                Role::Tiny | Role::Judge | Role::Speech | Role::Dictation => {}
            }
            selectors.extend(
                local
                    .into_iter()
                    .map(|model| Candidate::Local(model.id.to_owned())),
            );
            if role.takes_remote() && !session_model.is_empty() {
                selectors.push(Candidate::Remote(session_model.to_owned()));
            }
        }
    }
    let mut chain: Vec<Candidate> = Vec::with_capacity(selectors.len());
    for candidate in selectors {
        if !chain.contains(&candidate) {
            chain.push(candidate);
        }
    }
    chain
}
