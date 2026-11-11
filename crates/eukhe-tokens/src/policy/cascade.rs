//! The slice of omp's compat cascade (`packages/catalog/src/compat/cascade.ts`)
//! the catalog axes here read: rules are conjunctions over `(class,
//! provider, api, family, revision, models)`, and per axis the matching rule
//! with the greatest `(model-selector exactness, constrained-dimension
//! count, priority)` wins. Upstream constraints and `token` model selectors
//! are not ported: no rule on these axes uses them.

use super::ModelRef;
use super::revision::{RevisionTerm, revision_satisfies};
use super::taxonomy::{ModelIdentity, UNKNOWN_CLASS, classify_model, glob_match};

/// One `models` selector of a rule.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ModelSelector {
    /// The whole target id, case-sensitive.
    Exact(&'static str),
    /// A `*` glob over the lowercased target id.
    Glob(&'static str),
}

/// A compiled cascade rule's selector; `None` leaves a dimension open.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Selector {
    pub(crate) class: Option<&'static str>,
    pub(crate) providers: Option<&'static [&'static str]>,
    pub(crate) apis: Option<&'static [&'static str]>,
    pub(crate) family: Option<&'static str>,
    pub(crate) revision: Option<&'static [RevisionTerm]>,
    pub(crate) models: Option<&'static [ModelSelector]>,
    pub(crate) priority: i32,
}

impl Selector {
    /// A rule matching every target, to be narrowed with struct update syntax.
    pub(crate) const ANY: Self = Self {
        class: None,
        providers: None,
        apis: None,
        family: None,
        revision: None,
        models: None,
        priority: 0,
    };

    fn dimensions(&self) -> usize {
        [
            self.class.is_some(),
            self.providers.is_some(),
            self.apis.is_some(),
            self.family.is_some(),
            self.revision.is_some(),
            self.models.is_some(),
        ]
        .into_iter()
        .filter(|&constrained| constrained)
        .count()
    }

    /// `(exactness, dimensions, priority)` when the rule matches `target`.
    fn rank(&self, target: &Target<'_>) -> Option<(u8, usize, i32)> {
        if self
            .class
            .is_some_and(|class| class != target.identity.class)
            || self
                .providers
                .is_some_and(|providers| !providers.contains(&target.provider))
            || self.apis.is_some_and(|apis| !apis.contains(&target.api))
            || self
                .family
                .is_some_and(|family| Some(family) != target.identity.family)
        {
            return None;
        }
        if let Some(terms) = self.revision {
            let revision = target.identity.revision?;
            if !revision_satisfies(revision, terms) {
                return None;
            }
        }
        let exactness = match self.models {
            None => 0,
            Some(selectors) => selectors
                .iter()
                .filter_map(|selector| match *selector {
                    ModelSelector::Exact(id) => (id == target.model).then_some(2),
                    ModelSelector::Glob(glob) => glob_match(glob, &target.model_lower).then_some(1),
                })
                .max()?,
        };
        Some((exactness, self.dimensions(), self.priority))
    }
}

/// The structured target a cascade resolves: a model id classified on its
/// host, carried by a wire API.
pub(crate) struct Target<'a> {
    provider: &'a str,
    api: &'a str,
    model: &'a str,
    model_lower: String,
    identity: ModelIdentity,
}

impl<'a> Target<'a> {
    /// omp's image-tokenization and thinking-replay targets: the id's
    /// lenient identity on its host, or an unclassified target when the id
    /// is empty.
    pub(crate) fn new(model: ModelRef<'a>) -> Self {
        let identity = if model.id.is_empty() {
            ModelIdentity {
                class: UNKNOWN_CLASS,
                family: None,
                revision: None,
            }
        } else {
            classify_model(model.provider, model.id)
        };
        Self {
            provider: model.provider,
            api: model.api,
            model: model.id,
            model_lower: model.id.to_lowercase(),
            identity,
        }
    }
}

/// The winning value of one axis among `rules`. omp throws on an equal-rank
/// contest; the checked-in rules never produce one, and the first declared
/// rule would hold here.
pub(crate) fn resolve_axis<'r, T>(
    rules: &'r [(Selector, T)],
    target: &Target<'_>,
) -> Option<&'r T> {
    let mut winner: Option<((u8, usize, i32), &'r T)> = None;
    for (selector, value) in rules {
        let Some(rank) = selector.rank(target) else {
            continue;
        };
        if winner.is_none_or(|(held, _)| held < rank) {
            winner = Some((rank, value));
        }
    }
    winner.map(|(_, value)| value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bedrock_and_gateway_ids_keep_their_lineage() {
        let target = Target::new(ModelRef {
            id: "us.anthropic.claude-opus-4-7-v1:0",
            provider: "amazon-bedrock",
            api: "bedrock-converse-stream",
        });
        assert_eq!(target.identity.class, "anthropic");
        assert_eq!(target.identity.family, Some("opus"));
        assert_eq!(target.identity.revision, Some([4, 7, 0]));
    }
}
