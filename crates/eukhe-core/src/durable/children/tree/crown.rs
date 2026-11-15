//! The local crown as stored: a serde mirror of the compiled core's types
//! (`eukhe_bend::rules::agent_tree`), converted whole each way.

use eukhe_bend::rules::agent_tree::{Crown, Dir, Help, Info, Lim, Node, Status};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind", content = "value")]
pub(crate) enum LimDoc {
    Unlimited,
    Value(u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) enum StatusDoc {
    Running,
    Finished,
    Failed,
    Cancelled,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) enum DirDoc {
    Left,
    Right,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct InfoDoc {
    status: StatusDoc,
    scope: Vec<bool>,
    limit: LimDoc,
    spent: u64,
    deadline: LimDoc,
    patch: Vec<Option<u64>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub(crate) enum NodeDoc {
    Leaf {
        info: InfoDoc,
    },
    Split {
        info: InfoDoc,
        own: Vec<bool>,
        left: Box<NodeDoc>,
        right: Box<NodeDoc>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct HelpDoc {
    at: Vec<DirDoc>,
    status: StatusDoc,
    limit: LimDoc,
    spent: u64,
    deadline: LimDoc,
}

/// A crown as the tree document stores it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct CrownDoc {
    tree: NodeDoc,
    helps: Vec<HelpDoc>,
}

impl From<Lim> for LimDoc {
    fn from(lim: Lim) -> Self {
        match lim {
            Lim::Unlimited => Self::Unlimited,
            Lim::Value(value) => Self::Value(value),
        }
    }
}

impl From<LimDoc> for Lim {
    fn from(lim: LimDoc) -> Self {
        match lim {
            LimDoc::Unlimited => Self::Unlimited,
            LimDoc::Value(value) => Self::Value(value),
        }
    }
}

impl From<Status> for StatusDoc {
    fn from(status: Status) -> Self {
        match status {
            Status::Running => Self::Running,
            Status::Finished => Self::Finished,
            Status::Failed => Self::Failed,
            Status::Cancelled => Self::Cancelled,
        }
    }
}

impl From<StatusDoc> for Status {
    fn from(status: StatusDoc) -> Self {
        match status {
            StatusDoc::Running => Self::Running,
            StatusDoc::Finished => Self::Finished,
            StatusDoc::Failed => Self::Failed,
            StatusDoc::Cancelled => Self::Cancelled,
        }
    }
}

impl From<Dir> for DirDoc {
    fn from(dir: Dir) -> Self {
        match dir {
            Dir::Left => Self::Left,
            Dir::Right => Self::Right,
        }
    }
}

impl From<DirDoc> for Dir {
    fn from(dir: DirDoc) -> Self {
        match dir {
            DirDoc::Left => Self::Left,
            DirDoc::Right => Self::Right,
        }
    }
}

impl From<&Info> for InfoDoc {
    fn from(info: &Info) -> Self {
        Self {
            status: info.status.into(),
            scope: info.scope.clone(),
            limit: info.limit.into(),
            spent: info.spent,
            deadline: info.deadline.into(),
            patch: info.patch.clone(),
        }
    }
}

impl From<&InfoDoc> for Info {
    fn from(info: &InfoDoc) -> Self {
        Self {
            status: info.status.into(),
            scope: info.scope.clone(),
            limit: info.limit.into(),
            spent: info.spent,
            deadline: info.deadline.into(),
            patch: info.patch.clone(),
        }
    }
}

impl From<&Node> for NodeDoc {
    fn from(node: &Node) -> Self {
        match node {
            Node::Leaf(info) => Self::Leaf { info: info.into() },
            Node::Split {
                info,
                own,
                left,
                right,
            } => Self::Split {
                info: info.into(),
                own: own.clone(),
                left: Box::new(left.as_ref().into()),
                right: Box::new(right.as_ref().into()),
            },
        }
    }
}

impl From<&NodeDoc> for Node {
    fn from(node: &NodeDoc) -> Self {
        match node {
            NodeDoc::Leaf { info } => Self::Leaf(info.into()),
            NodeDoc::Split {
                info,
                own,
                left,
                right,
            } => Self::Split {
                info: info.into(),
                own: own.clone(),
                left: Box::new(left.as_ref().into()),
                right: Box::new(right.as_ref().into()),
            },
        }
    }
}

impl From<&Help> for HelpDoc {
    fn from(help: &Help) -> Self {
        Self {
            at: help.at.iter().copied().map(DirDoc::from).collect(),
            status: help.status.into(),
            limit: help.limit.into(),
            spent: help.spent,
            deadline: help.deadline.into(),
        }
    }
}

impl From<&HelpDoc> for Help {
    fn from(help: &HelpDoc) -> Self {
        Self {
            at: help.at.iter().copied().map(Dir::from).collect(),
            status: help.status.into(),
            limit: help.limit.into(),
            spent: help.spent,
            deadline: help.deadline.into(),
        }
    }
}

impl From<&Crown> for CrownDoc {
    fn from(crown: &Crown) -> Self {
        Self {
            tree: (&crown.tree).into(),
            helps: crown.helps.iter().map(HelpDoc::from).collect(),
        }
    }
}

impl From<&CrownDoc> for Crown {
    fn from(crown: &CrownDoc) -> Self {
        Self {
            tree: (&crown.tree).into(),
            helps: crown.helps.iter().map(Help::from).collect(),
        }
    }
}
