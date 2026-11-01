//! Where the model of every model role comes from (`bend/model_roles.bend`,
//! entry `bend/ffi_model_roles.bend`; `laws/model_roles.bend`): a role's
//! own setting when it is set; else the all-roles setting
//! (`modelRoles.all`) when it is set and the role takes a chat model
//! (every role but speech and dictation); else the role's default. The
//! table answers every role once, in `ModelRole::ALL` order.
//!
//! The selectors on the wire are opaque ids: a role's own setting is its
//! index in `ModelRole::ALL` plus 1, the all-roles setting is 0, so the
//! reply names which setting each role takes.

use eukhe_types::model_roles::ModelRole;

use crate::wire::{Reader, WireError, Writer};
use crate::{call, Entry, Error};

/// The selector id of the all-roles setting (a role's own id is its index
/// in `ModelRole::ALL` plus 1).
const ALL_SELECTOR: u64 = 0;

/// Where a role's model comes from (`bend/model_roles.bend` `Src`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoleSource {
    /// The role's own setting.
    Own,
    /// The all-roles setting (`modelRoles.all`).
    All,
    /// The role's default (its chain, the session model, ...).
    Default,
}

/// The source of every role, in `ModelRole::ALL` order, from the compiled
/// core. `own(role)`: the role's own setting is set; `all`:
/// `modelRoles.all` is set.
///
/// # Errors
///
/// A core failure, or a reply out of shape ([`WireError::Malformed`]):
/// rows other than `ModelRole::ALL` in order, an own row naming another
/// role's setting, an all-roles row naming another selector than the
/// all-roles one.
pub fn role_sources(
    own: impl Fn(ModelRole) -> bool,
    all: bool,
) -> Result<Vec<(ModelRole, RoleSource)>, Error> {
    let mut request = Writer::new();
    for (id, role) in (1u64..).zip(ModelRole::ALL) {
        if own(role) {
            request.some().nat(id);
        } else {
            request.none();
        }
    }
    if all {
        request.some().nat(ALL_SELECTOR);
    } else {
        request.none();
    }
    let reply = call(Entry::ModelRoles, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    if reader.count()? != ModelRole::ALL.len() {
        return Err(malformed("one row per model role").into());
    }
    let mut rows = Vec::with_capacity(ModelRole::ALL.len());
    for (tag, role) in (0u32..).zip(ModelRole::ALL) {
        if reader.tag()? != tag {
            return Err(malformed("the model roles in ModelRole::ALL order").into());
        }
        let source = match reader.tag_of(3, "a model role source")? {
            0 => {
                if reader.nat()? != u64::from(tag) + 1 {
                    return Err(malformed("the role's own selector").into());
                }
                RoleSource::Own
            }
            1 => {
                if reader.nat()? != ALL_SELECTOR {
                    return Err(malformed("the all-roles selector").into());
                }
                RoleSource::All
            }
            // `tag_of` answers a tag below 3: this is 2.
            _ => RoleSource::Default,
        };
        rows.push((role, source));
    }
    reader.end()?;
    Ok(rows)
}

fn malformed(expected: &'static str) -> WireError {
    WireError::Malformed { at: 0, expected }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The table pairs every role, in order, with `source(role)`.
    fn table(source: impl Fn(ModelRole) -> RoleSource) -> Vec<(ModelRole, RoleSource)> {
        ModelRole::ALL
            .into_iter()
            .map(|role| (role, source(role)))
            .collect()
    }

    /// The sources come from the compiled core: nothing set is every
    /// default; the all-roles setting alone reaches every role but speech
    /// and dictation; every own setting wins over it; a chat own setting
    /// beside the all-roles setting keeps the chat on its own model.
    #[test]
    fn the_core_decides_every_role_source() {
        let local = |role: ModelRole| matches!(role, ModelRole::Speech | ModelRole::Dictation);
        assert_eq!(
            [
                role_sources(|_| false, /*all*/ false).unwrap(),
                role_sources(|_| false, /*all*/ true).unwrap(),
                role_sources(|_| true, /*all*/ true).unwrap(),
                role_sources(|role| role == ModelRole::Chat, /*all*/ true).unwrap(),
            ],
            [
                table(|_| RoleSource::Default),
                table(|role| if local(role) {
                    RoleSource::Default
                } else {
                    RoleSource::All
                }),
                table(|_| RoleSource::Own),
                table(|role| match role {
                    ModelRole::Chat => RoleSource::Own,
                    ModelRole::Speech | ModelRole::Dictation => RoleSource::Default,
                    ModelRole::Memory
                    | ModelRole::Auxiliary
                    | ModelRole::Image
                    | ModelRole::Subagent
                    | ModelRole::Gateway
                    | ModelRole::Query
                    | ModelRole::Titles
                    | ModelRole::Judge
                    | ModelRole::Translate => RoleSource::All,
                }),
            ]
        );
    }
}
