//! A fixed accessibility tree for tests.

use std::collections::{HashMap, HashSet};
use std::hash::{DefaultHasher, Hash, Hasher};

use super::{
    Availability, AxProps, AxRead, Completeness, Identity, Liveness, Role, Selection, Settable,
    Unread, WalkBounds,
};
use crate::error::{Error, Refusal};
use crate::types::{Focus, Window};

/// An element read whole, identified by its role and title.
pub(crate) fn props(role: Role, title: &str) -> AxProps {
    let mut hasher = DefaultHasher::new();
    (&role, title).hash(&mut hasher);
    AxProps {
        role,
        native_role: String::new(),
        title: (!title.is_empty()).then(|| title.to_owned()),
        value: None,
        description: None,
        role_name: None,
        availability: Availability::Enabled,
        focus: Focus::Unfocused,
        selection: Selection::Unselected,
        bounds: None,
        actions: Vec::new(),
        child_count: 0,
        identity: Some(Identity(hasher.finish())),
        fields: Completeness::Whole,
        label_read: Completeness::Whole,
        unread_children: Unread::Count(0),
    }
}

/// Elements by handle, each with its props and children.
#[derive(Default)]
pub(crate) struct FakeTree {
    pub(crate) root: u64,
    pub(crate) nodes: HashMap<u64, (AxProps, Vec<u64>)>,
    pub(crate) gone: HashSet<u64>,
}

impl FakeTree {
    pub(crate) fn add(&mut self, handle: u64, props: AxProps, children: &[u64]) {
        self.nodes.insert(handle, (props, children.to_vec()));
    }
}

impl AxRead for FakeTree {
    type Handle = u64;

    fn window_root(&mut self, _: &Window) -> Result<u64, Error> {
        Ok(self.root)
    }

    fn walk_node(
        &mut self,
        handle: &u64,
        _: WalkBounds,
        _: u32,
    ) -> Result<(AxProps, Vec<u64>), Error> {
        if self.gone.contains(handle) {
            return Err(Error::Refused(Refusal::Vanished));
        }
        self.nodes
            .get(handle)
            .cloned()
            .ok_or(Error::Refused(Refusal::Vanished))
    }

    fn props(&mut self, handle: &u64) -> Result<AxProps, Error> {
        self.walk_node(handle, WalkBounds::Read, 0)
            .map(|(props, _)| props)
    }

    fn liveness(&mut self, handle: &u64) -> Liveness {
        if self.gone.contains(handle) {
            Liveness::Gone
        } else {
            Liveness::Alive
        }
    }

    fn focused_within(&mut self, _: &u64) -> Option<u64> {
        None
    }

    fn value_settable(&mut self, _: &u64) -> Settable {
        Settable::Unknown
    }
}
