//! The merge of one path (`bend/sandbox.bend`, `merge1`): the parent's
//! content, the base's (the workspace when the child started) and the
//! child's; `None` is no file.

/// The merged content of one path, and whether it is a conflict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct One<T> {
    pub(super) body: Option<T>,
    pub(super) clash: bool,
}

/// - The child did not change the path: the parent's content stays.
/// - Only the child changed it: the child's content.
/// - Both changed it to the same content: that content.
/// - Both changed it differently: the parent's content stays, and the
///   path is a conflict.
pub(super) fn merge1<T: PartialEq + Clone>(
    parent: Option<&T>,
    base: Option<&T>,
    child: Option<&T>,
) -> One<T> {
    let child_changed = child != base;
    let parent_changed = parent != base;
    let same = parent == child;
    match (child_changed, parent_changed, same) {
        (false, _, _) | (true, true, true) => One {
            body: parent.cloned(),
            clash: false,
        },
        (true, false, _) => One {
            body: child.cloned(),
            clash: false,
        },
        (true, true, false) => One {
            body: parent.cloned(),
            clash: true,
        },
    }
}
