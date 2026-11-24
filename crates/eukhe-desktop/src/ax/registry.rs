//! The ref registry (port of `AxRegistry` in omp
//! `crates/natives/src/desktop/ax.rs`).
//!
//! An element keeps its ref across reads of its window while its role and
//! label stay the same; a ref missing from two observations of its window in
//! a row expires. An element read again with another role or label, or whose
//! element from the last read is gone, gets a new ref.

use std::collections::HashMap;
use std::hash::Hash;

use super::tree::SnapshotLimits;
use super::{AxProps, Completeness, ElementRef, Fingerprint, Identity, Liveness, Role};
use crate::error::{StaleCause, StaleRef};
use crate::types::WindowId;

/// Most refs the registry keeps; past it the oldest observation of the
/// window with the most refs goes first.
const CAP: usize = 5_000;

/// A walk that read every element of the window element `root` still there,
/// within these limits.
#[derive(Clone)]
pub(crate) struct WholeWalk<H> {
    pub(super) root: H,
    pub(super) limits: SnapshotLimits,
}

/// What one read says about whether an element's identity is unique in its
/// window.
pub(crate) enum Uniqueness<'a, H> {
    /// No other element of this walk of the whole window shares it.
    Proven(&'a WholeWalk<H>),
    /// Another element of the walk shares it.
    Shared,
    /// A read that cannot tell: an earlier proof stands while the identity
    /// is unchanged.
    Unknown,
}

impl<H> Clone for Uniqueness<'_, H> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<H> Copy for Uniqueness<'_, H> {}

/// Why a ref's identity can name its element's one copy.
#[derive(Clone)]
struct Proof<H> {
    identity: Identity,
    walk: WholeWalk<H>,
}

/// Where a ref's element sits in a table row no other row of a whole walk
/// matched element for element, so the ref can follow the row once the app
/// rebuilds it from new elements.
#[derive(Clone)]
pub(super) struct RowProof<H> {
    /// The row's print ([`super::stale::row_print`]).
    pub(super) print: u64,
    /// Child indices from the row down to the element.
    pub(super) path: Vec<usize>,
    pub(super) identity: Identity,
    pub(super) walk: WholeWalk<H>,
}

struct Registered<H> {
    handle: H,
    window: WindowId,
    /// The window's observation that last registered it.
    generation: Generation,
    /// Role and label at registration.
    fingerprint: Fingerprint,
    proof: Option<Proof<H>>,
    row: Option<RowProof<H>>,
    /// The fingerprint an action through this ref checks; none when the
    /// label was not read whole, nor for a window, which names its document.
    held: Option<Fingerprint>,
}

/// The count of a window's observations; refs a newer one did not renew
/// expire by it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Generation(u64);

impl Generation {
    /// Whether a ref last renewed in `self` expires once `current` ends:
    /// neither it nor the observation before it renewed the ref.
    fn expires_by(self, current: Self) -> bool {
        self.0.saturating_add(1) < current.0
    }
}

/// What a read of a window is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReadKind {
    /// An observation: starts a generation that expires refs.
    Snapshot,
    /// A search or single read: renews refs in the current generation.
    Query,
}

pub(crate) struct Registry<H> {
    next: u64,
    generations: HashMap<WindowId, Generation>,
    entries: HashMap<u64, Registered<H>>,
    /// The ref of each element registered under each window.
    refs: HashMap<WindowId, HashMap<H, u64>>,
}

impl<H> Default for Registry<H> {
    fn default() -> Self {
        Self {
            next: 1,
            generations: HashMap::new(),
            entries: HashMap::new(),
            refs: HashMap::new(),
        }
    }
}

impl<H: Clone + Eq + Hash> Registry<H> {
    /// Starts a read of `window`, returning its generation.
    pub(crate) fn begin_read(&mut self, window: &WindowId, kind: ReadKind) -> Generation {
        let generation = self.generations.entry(window.clone()).or_default();
        *generation = Generation(match kind {
            ReadKind::Snapshot => generation.0.saturating_add(1),
            ReadKind::Query => generation.0.max(1),
        });
        *generation
    }

    /// Ends `window`'s observation `generation` once it registered its
    /// elements: refs neither it nor the previous observation registered
    /// expire, so an element missing from one observation keeps its ref.
    pub(crate) fn end_snapshot(&mut self, window: &WindowId, generation: Generation) {
        self.evict(|entry| entry.window == *window && entry.generation.expires_by(generation));
    }

    /// The element's ref under `window`, minted the first time it is seen
    /// there and renewed for `generation`. `liveness` tells whether the
    /// element a known ref was read from still exists.
    pub(crate) fn register(
        &mut self,
        mut liveness: impl FnMut(&H) -> Liveness,
        window: &WindowId,
        generation: Generation,
        handle: H,
        props: &AxProps,
        uniqueness: Uniqueness<'_, H>,
    ) -> ElementRef {
        let fingerprint = props.fingerprint();
        let known = self
            .refs
            .get(window)
            .and_then(|refs| refs.get(&handle))
            .copied();
        let renewed = known.filter(|id| {
            self.entries.get(id).is_some_and(|entry| {
                entry.fingerprint == fingerprint && liveness(&entry.handle) == Liveness::Alive
            })
        });
        let id = renewed.unwrap_or_else(|| {
            let id = self.next;
            self.next = self.next.saturating_add(1);
            self.refs
                .entry(window.clone())
                .or_default()
                .insert(handle.clone(), id);
            id
        });
        let kept = |identity| props.identity == Some(identity);
        let (earlier_proof, row) =
            renewed
                .and_then(|id| self.entries.remove(&id))
                .map_or((None, None), |entry| {
                    (
                        entry.proof.filter(|proof| kept(proof.identity)),
                        entry.row.filter(|row| kept(row.identity)),
                    )
                });
        let proof = match uniqueness {
            Uniqueness::Proven(walk) => props.identity.map(|identity| Proof {
                identity,
                walk: walk.clone(),
            }),
            Uniqueness::Shared => None,
            Uniqueness::Unknown => earlier_proof,
        };
        let held = (props.label_read == Completeness::Whole && props.role != Role::Window)
            .then_some(fingerprint);
        self.entries.insert(
            id,
            Registered {
                handle,
                window: window.clone(),
                generation,
                fingerprint,
                proof,
                row,
                held,
            },
        );
        self.enforce_cap();
        ElementRef(id)
    }

    fn entry(&self, reference: ElementRef) -> Result<&Registered<H>, StaleRef> {
        self.entries.get(&reference.0).ok_or(StaleRef {
            reference,
            cause: StaleCause::Expired,
        })
    }

    /// The element `reference` names and the window it was read in.
    pub(crate) fn resolve(&self, reference: ElementRef) -> Result<(&H, &WindowId), StaleRef> {
        self.entry(reference)
            .map(|entry| (&entry.handle, &entry.window))
    }

    /// The role and label an action through `reference` checks.
    pub(crate) fn held(&self, reference: ElementRef) -> Option<Fingerprint> {
        self.entry(reference).ok()?.held
    }

    /// Whether `reference` was read in a row no other row of a whole walk
    /// matched, so it can follow the row's rebuilt copy.
    pub(crate) fn has_row(&self, reference: ElementRef) -> bool {
        self.row(reference).is_some()
    }

    /// The role and label `reference` was read with.
    pub(super) fn fingerprint(&self, reference: ElementRef) -> Result<Fingerprint, StaleRef> {
        self.entry(reference).map(|entry| entry.fingerprint)
    }

    /// The proof `reference`'s identity names its element's one copy.
    pub(super) fn proof(&self, reference: ElementRef) -> Option<(Identity, &WholeWalk<H>)> {
        let proof = self.entry(reference).ok()?.proof.as_ref()?;
        Some((proof.identity, &proof.walk))
    }

    pub(super) fn row(&self, reference: ElementRef) -> Option<&RowProof<H>> {
        self.entry(reference).ok()?.row.as_ref()
    }

    /// Records where `reference` sits in its row, decided by a whole walk.
    pub(super) fn set_row(&mut self, reference: ElementRef, row: Option<RowProof<H>>) {
        if let Some(entry) = self.entries.get_mut(&reference.0) {
            entry.row = row;
        }
    }

    /// Points `reference` at `handle`, the element in its place in a rebuilt
    /// copy of its row. Another ref that already names `handle` keeps it.
    pub(super) fn repoint(&mut self, reference: ElementRef, handle: H, row: RowProof<H>) {
        let Some(entry) = self.entries.get_mut(&reference.0) else {
            return;
        };
        let old = std::mem::replace(&mut entry.handle, handle.clone());
        entry.row = Some(row);
        let Some(refs) = self.refs.get_mut(&entry.window) else {
            return;
        };
        if refs.get(&old) == Some(&reference.0) {
            refs.remove(&old);
        }
        refs.entry(handle).or_insert(reference.0);
    }

    /// Whether `reference` still resolves: registering at the cap can evict
    /// the ref just minted.
    pub(super) fn live(&self, reference: ElementRef) -> bool {
        self.entries.contains_key(&reference.0)
    }

    /// Drops expired refs. An identity a newer ref took over keeps pointing
    /// at that one.
    fn evict(&mut self, mut expired: impl FnMut(&Registered<H>) -> bool) {
        let refs = &mut self.refs;
        self.entries.retain(|id, entry| {
            if !expired(entry) {
                return true;
            }
            if let Some(window_refs) = refs.get_mut(&entry.window) {
                if window_refs.get(&entry.handle) == Some(id) {
                    window_refs.remove(&entry.handle);
                }
            }
            false
        });
    }

    fn enforce_cap(&mut self) {
        while self.entries.len() > CAP {
            let mut sizes: HashMap<&WindowId, usize> = HashMap::new();
            for entry in self.entries.values() {
                *sizes.entry(&entry.window).or_default() += 1;
            }
            let Some(window) = sizes
                .into_iter()
                .max_by_key(|(_, count)| *count)
                .map(|(window, _)| window.clone())
            else {
                return;
            };
            let Some(oldest) = self
                .entries
                .values()
                .filter(|entry| entry.window == window)
                .map(|entry| entry.generation)
                .min()
            else {
                return;
            };
            self.evict(|entry| entry.window == window && entry.generation == oldest);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ax::fake::props;

    #[allow(
        clippy::trivially_copy_pass_by_ref,
        reason = "the registry passes handles by reference"
    )]
    fn alive(_: &u64) -> Liveness {
        Liveness::Alive
    }

    /// One observation of `window` reading `elements` (handle, role, title).
    fn observe(
        registry: &mut Registry<u64>,
        window: &WindowId,
        elements: &[(u64, Role, &str)],
    ) -> Vec<ElementRef> {
        let generation = registry.begin_read(window, ReadKind::Snapshot);
        let refs = elements
            .iter()
            .map(|(handle, role, title)| {
                registry.register(
                    alive,
                    window,
                    generation,
                    *handle,
                    &props(role.clone(), title),
                    Uniqueness::Unknown,
                )
            })
            .collect();
        registry.end_snapshot(window, generation);
        refs
    }

    fn expired(reference: ElementRef) -> Result<(), StaleRef> {
        Err(StaleRef {
            reference,
            cause: StaleCause::Expired,
        })
    }

    fn resolves(registry: &Registry<u64>, reference: ElementRef) -> Result<(), StaleRef> {
        registry.resolve(reference).map(|_| ())
    }

    #[test]
    fn a_ref_survives_one_missed_observation_and_expires_after_two() {
        let window = WindowId::new("1");
        let mut registry = Registry::default();
        let [save, quit] = observe(
            &mut registry,
            &window,
            &[(1, Role::Button, "Save"), (2, Role::Button, "Quit")],
        )[..] else {
            panic!("two refs");
        };
        assert_eq!(
            observe(&mut registry, &window, &[(1, Role::Button, "Save")]),
            [save]
        );
        assert_eq!(resolves(&registry, quit), Ok(()));
        observe(&mut registry, &window, &[(1, Role::Button, "Save")]);
        assert_eq!(resolves(&registry, save), Ok(()));
        assert_eq!(resolves(&registry, quit), expired(quit));
    }

    #[test]
    fn a_new_role_or_label_mints_a_new_ref_and_the_old_one_expires() {
        let window = WindowId::new("1");
        let mut registry = Registry::default();
        let first = observe(&mut registry, &window, &[(1, Role::TextField, "City")]);
        let second = observe(&mut registry, &window, &[(1, Role::TextField, "Street")]);
        assert_ne!(first, second);
        assert_eq!(resolves(&registry, first[0]), Ok(()));
        let third = observe(&mut registry, &window, &[(1, Role::TextField, "Street")]);
        assert_eq!(third, second);
        assert_eq!(resolves(&registry, first[0]), expired(first[0]));
    }

    #[test]
    fn a_gone_element_is_never_renewed_onto_its_successor() {
        let window = WindowId::new("1");
        let mut registry = Registry::default();
        let first = observe(&mut registry, &window, &[(7, Role::Button, "OK")]);
        let generation = registry.begin_read(&window, ReadKind::Snapshot);
        let again = registry.register(
            |_| Liveness::Gone,
            &window,
            generation,
            7,
            &props(Role::Button, "OK"),
            Uniqueness::Unknown,
        );
        assert_ne!(again, first[0]);
    }

    #[test]
    fn refs_are_kept_per_window() {
        let (one, two) = (WindowId::new("1"), WindowId::new("2"));
        let mut registry = Registry::default();
        let a = observe(&mut registry, &one, &[(1, Role::Button, "OK")]);
        observe(&mut registry, &two, &[(2, Role::Button, "OK")]);
        observe(&mut registry, &two, &[(2, Role::Button, "OK")]);
        assert_eq!(resolves(&registry, a[0]), Ok(()));
        assert_eq!(
            registry
                .resolve(a[0])
                .map(|(handle, window)| (*handle, window.clone())),
            Ok((1, one))
        );
    }
}
