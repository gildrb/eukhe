//! A node's place in the agent tree: the runtime metadata a tree node's
//! session carries from its spawn (`treeRole`, `treeScope`, `treePath`,
//! `treeAllowance`, `treeDeadline`), and the node's status its roster row
//! shows.

use serde::{Deserialize, Serialize};

/// A node's role in its tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TreeRole {
    /// The tree's root: the whole scope.
    Root,
    /// A split's left child.
    Left,
    /// A split's right child.
    Right,
    /// A read-only leaf: no write scope.
    Help,
    /// A harness-run internal node of a workflow's tree.
    Integrator,
}

/// A node's place, as its spawn's runtime metadata names it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TreePlace {
    #[serde(rename = "treeRole")]
    pub role: TreeRole,
    /// Paths relative to the workspace root (`""` = everything).
    #[serde(rename = "treeScope")]
    pub scope: Vec<String>,
    /// Left/right steps from the root (`""` = the root, `"L"`, `"LR"`); a
    /// help leaf: its node's path.
    #[serde(rename = "treePath")]
    pub path: String,
    /// The nodes the node may hold, itself included.
    #[serde(rename = "treeAllowance")]
    pub allowance: u64,
    /// The node's deadline (Unix ms); `None`: unlimited.
    #[serde(
        rename = "treeDeadline",
        default,
        skip_serializing_if = "Option::is_none"
    )]
    pub deadline: Option<u64>,
}

/// Where a node stands: running, or how its last run ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TreeStatus {
    Running,
    /// The last run answered.
    Finished,
    /// The last run ended on an error.
    Failed,
    /// The last run was aborted (a tree cancel, a deadline, an abort).
    Cancelled,
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    /// A spawn's runtime metadata reads as the node's place; the other
    /// metadata keys stay out of it.
    #[test]
    fn spawn_metadata_reads_as_the_place() {
        let metadata = json!({
            "kind": "subagent",
            "rlmChildId": "sub-1",
            "treeRole": "left",
            "treeScope": ["crates/eukhe-tui", "docs"],
            "treePath": "L",
            "treeAllowance": 7,
        });
        assert_eq!(
            serde_json::from_value::<TreePlace>(metadata).expect("a place"),
            TreePlace {
                role: TreeRole::Left,
                scope: vec!["crates/eukhe-tui".to_string(), "docs".to_string()],
                path: "L".to_string(),
                allowance: 7,
                deadline: None,
            }
        );
    }
}
