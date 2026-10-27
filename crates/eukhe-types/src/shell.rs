//! The shell's approval vocabulary (S7): the effects of one
//! step of a `bash` script (a set), the auto set, the question the host
//! asks the attached client about a step that is not within the auto set,
//! the client's answer, and how the question ended.

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::path_policy::PathClass;

/// One effect a step may have. A command the classification table does
/// not know is [`ShellEffect::Exec`]. Every effect may sit in an
/// [`AutoSet`]; the user's `shell.autoEffects` decides (a secret access
/// gates like any other).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ShellEffect {
    /// Reads files or shell state.
    Read,
    /// Changes files.
    Write,
    /// Runs a program the table does not know, or one a repository or a
    /// file can choose.
    Exec,
    /// Talks to the network.
    Net,
    /// Writes outside the workspace.
    Outside,
    /// Writes eukhe's own configuration or credentials, or a place that
    /// makes a later step run a program (bend/tools.bend: never auto).
    Protected,
    /// Reads or writes a secret (ssh keys, credential stores).
    Secret,
}

impl ShellEffect {
    /// Every effect, in code order (bend/tools.bend `Eff.code`: 0 to 6).
    pub const ALL: [Self; 7] = [
        Self::Read,
        Self::Write,
        Self::Exec,
        Self::Net,
        Self::Outside,
        Self::Protected,
        Self::Secret,
    ];

    /// The effect's wire name.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Read => "read",
            Self::Write => "write",
            Self::Exec => "exec",
            Self::Net => "net",
            Self::Outside => "outside",
            Self::Protected => "protected",
            Self::Secret => "secret",
        }
    }

    /// The effect's code (bend/tools.bend `Eff.code`).
    #[must_use]
    pub fn code(self) -> u8 {
        match self {
            Self::Read => 0,
            Self::Write => 1,
            Self::Exec => 2,
            Self::Net => 3,
            Self::Outside => 4,
            Self::Protected => 5,
            Self::Secret => 6,
        }
    }

    /// Whether the user's auto set may hold the effect: every effect
    /// (bend/tools.bend `grantable`).
    #[must_use]
    pub fn grantable(self) -> bool {
        match self {
            Self::Read
            | Self::Write
            | Self::Exec
            | Self::Net
            | Self::Outside
            | Self::Protected
            | Self::Secret => true,
        }
    }
}

/// A set of [`ShellEffect`]s: every effect of one step. On the wire, the
/// list of the effects' names in code order.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct ShellEffects(u8);

impl ShellEffects {
    /// The empty set.
    pub const NONE: Self = Self(0);

    /// The set of `effects`.
    #[must_use]
    pub fn of(effects: &[ShellEffect]) -> Self {
        effects
            .iter()
            .fold(Self::NONE, |set, &effect| set.with(effect))
    }

    /// This set with `effect` added.
    #[must_use]
    pub fn with(self, effect: ShellEffect) -> Self {
        Self(self.0 | 1 << effect.code())
    }

    /// Add `effect`.
    pub fn insert(&mut self, effect: ShellEffect) {
        *self = self.with(effect);
    }

    /// The effects of both sets.
    #[must_use]
    pub fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    #[must_use]
    pub fn contains(self, effect: ShellEffect) -> bool {
        self.0 & 1 << effect.code() != 0
    }

    /// The effects, in code order.
    pub fn iter(self) -> impl Iterator<Item = ShellEffect> {
        ShellEffect::ALL
            .into_iter()
            .filter(move |&effect| self.contains(effect))
    }

    /// The effects' names joined by `+`, in code order (`net+write`).
    #[must_use]
    pub fn names(self) -> String {
        self.iter()
            .map(ShellEffect::as_str)
            .collect::<Vec<_>>()
            .join("+")
    }

    /// The effects of a write to a path of class `class`.
    #[must_use]
    pub fn write_to(class: PathClass) -> Self {
        match class {
            PathClass::Inside => Self::of(&[ShellEffect::Write]),
            PathClass::Outside => Self::of(&[ShellEffect::Write, ShellEffect::Outside]),
            PathClass::Protected => Self::of(&[ShellEffect::Write, ShellEffect::Protected]),
            PathClass::Secret => Self::of(&[ShellEffect::Write, ShellEffect::Secret]),
        }
    }

    /// The effects of a read of a path of class `class`.
    #[must_use]
    pub fn read_of(class: PathClass) -> Self {
        match class {
            PathClass::Secret => Self::of(&[ShellEffect::Read, ShellEffect::Secret]),
            PathClass::Inside | PathClass::Outside | PathClass::Protected => {
                Self::of(&[ShellEffect::Read])
            }
        }
    }
}

impl Serialize for ShellEffects {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self.iter())
    }
}

impl<'de> Deserialize<'de> for ShellEffects {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Self::of(&Vec::<ShellEffect>::deserialize(deserializer)?))
    }
}

/// The effects whose steps run without asking: the grantable effects the
/// user allows (`shell.autoEffects`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AutoSet(ShellEffects);

impl AutoSet {
    /// The auto set of the grantable effects of `effects`; the others are
    /// dropped.
    pub fn new(effects: impl IntoIterator<Item = ShellEffect>) -> Self {
        Self(
            effects
                .into_iter()
                .filter(|effect| effect.grantable())
                .fold(ShellEffects::NONE, ShellEffects::with),
        )
    }

    /// Whether a step with `effects` runs without asking: every effect is
    /// in the auto set (bend/tools.bend `within`).
    #[must_use]
    pub fn allows(self, effects: ShellEffects) -> bool {
        effects.0 & !(self.0).0 == 0
    }
}

/// The host asks the attached client whether one step may run (the
/// `shell_approval` frame).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ShellApprovalRequest {
    /// Unique within the session; the answer names it.
    pub request_id: String,
    /// The step's place in the script, from 0, in the order steps run.
    pub step: u64,
    /// The step exactly as it will run, after expansion, with every
    /// control and bidi character escaped.
    pub command: String,
    /// Every effect of the step.
    pub effects: ShellEffects,
}

/// The client's answer to one [`ShellApprovalRequest`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ShellVerdict {
    Approve,
    Deny,
}

/// How one [`ShellApprovalRequest`] ended: the answer of the session's
/// approval sink.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ShellAnswer {
    /// A client approved the step, or the session runs only from the
    /// phone gateway and the step is not guarded: it runs.
    Approve,
    /// A client denied the step.
    Deny,
    /// No session up the chain had a client that answered: a denial.
    Unanswered,
    /// The session runs only from the phone gateway, and the step writes a
    /// protected path ([`ShellEffect::Protected`]) that the narrowed auto
    /// set does not run: refused at once.
    GatewayRefused,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn effects_round_trip_as_names_in_code_order() {
        let set = ShellEffects::of(&[ShellEffect::Secret, ShellEffect::Net, ShellEffect::Write]);
        let json = serde_json::to_value(set).unwrap();
        assert_eq!(json, serde_json::json!(["write", "net", "secret"]));
        assert_eq!(serde_json::from_value::<ShellEffects>(json).unwrap(), set);
    }

    #[test]
    fn the_auto_set_allows_a_secret_like_any_effect() {
        let auto = AutoSet::new(ShellEffect::ALL);
        let allowed: Vec<bool> = ShellEffect::ALL
            .into_iter()
            .map(|effect| auto.allows(ShellEffects::of(&[ShellEffect::Read, effect])))
            .collect();
        assert_eq!(allowed, [true, true, true, true, true, true, true]);
    }
}
