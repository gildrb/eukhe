//! The model roles the `/model` hub sets: one per setting that names a
//! model. A role's [`id`](ModelRole::id) is its `/model <role>` subcommand.

/// One model role.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ModelRole {
    /// The session's chat model and the default for new sessions.
    Chat,
    /// The memory compactor (`memory.model`).
    Memory,
    /// Compaction and summaries (`auxiliaryModel`).
    Auxiliary,
    /// Turns that carry images (`imageModel`).
    Image,
    /// Subagents without an explicit model (`subagentDefaultModel`).
    Subagent,
    /// The phone gateway (`gateway.signal.model`).
    Gateway,
    /// Session titles (`modelRoles.tiny`).
    Titles,
    /// The judge (`modelRoles.judge`).
    Judge,
    /// Translation (`modelRoles.translate`).
    Translate,
    /// Speech synthesis (`modelRoles.speech`).
    Speech,
    /// Dictation (`modelRoles.dictation`).
    Dictation,
}

/// The models a role group accepts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ModelRoleGroup {
    /// Remote or local chat models.
    Chat,
    /// Local catalog models of the role.
    Local,
}

impl ModelRole {
    /// Every role, in hub order.
    pub const ALL: [Self; 11] = [
        Self::Chat,
        Self::Memory,
        Self::Auxiliary,
        Self::Image,
        Self::Subagent,
        Self::Gateway,
        Self::Titles,
        Self::Judge,
        Self::Translate,
        Self::Speech,
        Self::Dictation,
    ];

    /// The role's id: its `/model` subcommand.
    #[must_use]
    pub const fn id(self) -> &'static str {
        match self {
            Self::Chat => "chat",
            Self::Memory => "memory",
            Self::Auxiliary => "auxiliary",
            Self::Image => "image",
            Self::Subagent => "subagent",
            Self::Gateway => "gateway",
            Self::Titles => "titles",
            Self::Judge => "judge",
            Self::Translate => "translate",
            Self::Speech => "speech",
            Self::Dictation => "dictation",
        }
    }

    /// The role's label in the hub.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Chat => "Chat (this session, default)",
            Self::Memory => "Memory compactor",
            Self::Auxiliary => "Compaction and summaries",
            Self::Image => "Image turns",
            Self::Subagent => "Subagents",
            Self::Gateway => "Phone gateway",
            Self::Titles => "Titles",
            Self::Judge => "Judge",
            Self::Translate => "Translation",
            Self::Speech => "Speech",
            Self::Dictation => "Dictation",
        }
    }

    /// The models the role accepts.
    #[must_use]
    pub const fn group(self) -> ModelRoleGroup {
        match self {
            Self::Chat
            | Self::Memory
            | Self::Auxiliary
            | Self::Image
            | Self::Subagent
            | Self::Gateway => ModelRoleGroup::Chat,
            Self::Titles | Self::Judge | Self::Translate | Self::Speech | Self::Dictation => {
                ModelRoleGroup::Local
            }
        }
    }

    /// The role with `id`, if any.
    #[must_use]
    pub fn from_id(id: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|role| role.id() == id)
    }
}

#[cfg(test)]
mod tests {
    use super::ModelRole;

    #[test]
    fn ids_round_trip_and_are_unique() {
        for role in ModelRole::ALL {
            assert_eq!(ModelRole::from_id(role.id()), Some(role));
        }
        assert_eq!(ModelRole::from_id("tiny"), None);
    }
}
