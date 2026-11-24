//! Naming where a stale ref's element went: following a rebuilt table row,
//! and the one element left with the ref's identity or role and label (port
//! of `follow_row`, `refind_in` and `find_read_as` in omp
//! `crates/natives/src/desktop/ax.rs`).

use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};

use super::registry::{ReadKind, RowProof, Uniqueness, WholeWalk};
use super::tree::{walk, Marks, Walk, WalkNode};
use super::{AxRead, Completeness, ElementRef, Registry, Role, WalkBounds};
use crate::control::Token;
use crate::error::Error;
use crate::types::Window;

/// A row's elements, each as its depth below the row and its identity, in
/// walk order, hashed: two rows match when they hold the same elements in
/// the same places. `None` when an element of the row has no identity.
fn row_print<H>(row: &WalkNode<H>) -> Option<u64> {
    fn add<H>(node: &WalkNode<H>, depth: u32, hasher: &mut DefaultHasher) -> Option<()> {
        depth.hash(hasher);
        node.props.identity?.hash(hasher);
        node.children
            .iter()
            .try_for_each(|child| add(child, depth + 1, hasher))
    }
    let mut hasher = DefaultHasher::new();
    add(row, 0, &mut hasher)?;
    Some(hasher.finish())
}

/// Every row of `tree`, outer before inner, with its [`row_print`].
fn rows_of<H>(tree: &WalkNode<H>) -> Vec<(&WalkNode<H>, Option<u64>)> {
    let mut rows = Vec::new();
    let mut stack = vec![tree];
    while let Some(node) = stack.pop() {
        if node.props.role == Role::Row {
            rows.push((node, row_print(node)));
        }
        stack.extend(node.children.iter().rev());
    }
    rows
}

/// Where each element of a row of `tree` that no other row matches sits in
/// it. An element of a row inside a row is placed in the inner one.
pub(super) fn row_places<H: Clone + Eq + Hash>(
    tree: &WalkNode<H>,
    walk: &WholeWalk<H>,
) -> HashMap<H, RowProof<H>> {
    fn place<H: Clone + Eq + Hash>(
        node: &WalkNode<H>,
        path: &mut Vec<usize>,
        print: u64,
        walk: &WholeWalk<H>,
        places: &mut HashMap<H, RowProof<H>>,
    ) {
        if let Some(identity) = node.props.identity {
            places.insert(
                node.handle.clone(),
                RowProof {
                    print,
                    path: path.clone(),
                    identity,
                    walk: walk.clone(),
                },
            );
        }
        for (index, child) in node.children.iter().enumerate() {
            path.push(index);
            place(child, path, print, walk, places);
            path.pop();
        }
    }
    let rows = rows_of(tree);
    let mut counts: HashMap<u64, u32> = HashMap::new();
    for print in rows.iter().filter_map(|(_, print)| *print) {
        *counts.entry(print).or_default() += 1;
    }
    let mut places = HashMap::new();
    for (row, print) in rows {
        if let Some(print) = print.filter(|print| counts.get(print) == Some(&1)) {
            place(row, &mut Vec::new(), print, walk, &mut places);
        }
    }
    places
}

/// A read of the whole window, from the root a ref's walk was taken from.
pub(crate) struct WindowRead<H> {
    root: H,
    tree: Option<WalkNode<H>>,
    walk: WholeWalk<H>,
}

/// Reads the whole of `window`, as far as `bounds` did and at least as far
/// as `find` does. `None` when the window id now names another window, or
/// this walk could not read the whole window.
fn read_whole<A: AxRead>(
    ax: &mut A,
    window: &Window,
    bounds: &WholeWalk<A::Handle>,
    token: &Token,
) -> Result<Option<WindowRead<A::Handle>>, Error> {
    let root = ax.window_root(window)?;
    if root != bounds.root {
        return Ok(None);
    }
    let (tree, state) = walk(
        ax,
        root.clone(),
        Walk::new(
            token,
            bounds.limits.at_least_find(),
            WalkBounds::Skip,
            Marks::Skip,
        ),
    )?;
    // A copy in a part the walk could not read would make a match ambiguous.
    Ok(state
        .whole(&root)
        .map(|walk| WindowRead { root, tree, walk }))
}

/// Points `reference` at the element in its place in the one row of
/// `window` that reads, element for element, as the ref's row did, once the
/// app rebuilt that row from new elements. `Ok(None)` once the ref followed
/// its row, or when there was no whole read; otherwise the read is returned
/// for [`refind_in`].
pub(crate) fn follow_row<A: AxRead>(
    ax: &mut A,
    registry: &mut Registry<A::Handle>,
    window: &Window,
    reference: ElementRef,
    token: &Token,
) -> Result<Option<WindowRead<A::Handle>>, Error> {
    let Some(row) = registry.row(reference).cloned() else {
        return Ok(None);
    };
    let Some(read) = read_whole(ax, window, &row.walk, token)? else {
        return Ok(None);
    };
    let Some(tree) = &read.tree else {
        return Ok(Some(read));
    };
    let rows = rows_of(tree);
    let mut same = rows.iter().filter(|(_, print)| *print == Some(row.print));
    let (Some((copy, _)), None) = (same.next(), same.next()) else {
        return Ok(Some(read));
    };
    let Some(element) = row
        .path
        .iter()
        .try_fold(*copy, |node, &index| node.children.get(index))
        .filter(|element| element.props.identity == Some(row.identity))
    else {
        return Ok(Some(read));
    };
    let handle = element.handle.clone();
    registry.repoint(
        reference,
        handle,
        RowProof {
            walk: read.walk,
            ..row
        },
    );
    Ok(None)
}

/// The one element of `window` with the identity `reference` was read with,
/// registered under the ref's window, for a `StaleRef` to name once the app
/// destroyed the ref's element. The ref keeps naming the destroyed element:
/// equal fields do not prove the match is the same control. Searches `read`
/// when it comes from the root the identity was proved in.
pub(crate) fn refind_in<A: AxRead>(
    ax: &mut A,
    registry: &mut Registry<A::Handle>,
    window: &Window,
    reference: ElementRef,
    read: Option<WindowRead<A::Handle>>,
    token: &Token,
) -> Result<Option<ElementRef>, Error> {
    let Some((identity, proof_walk)) = registry
        .proof(reference)
        .map(|(identity, walk)| (identity, walk.clone()))
    else {
        return Ok(None);
    };
    let in_row = registry.row(reference).is_some();
    let read = match read.filter(|read| read.root == proof_walk.root) {
        Some(read) => read,
        None => match read_whole(ax, window, &proof_walk, token)? {
            Some(read) => read,
            None => return Ok(None),
        },
    };
    let WindowRead { tree, walk, .. } = read;
    let mut rows = match &tree {
        Some(tree) if in_row => row_places(tree, &walk),
        Some(_) | None => HashMap::new(),
    };
    let mut matches = Vec::new();
    let mut stack: Vec<_> = tree.into_iter().collect();
    while let Some(node) = stack.pop() {
        stack.extend(node.children);
        if node.props.identity == Some(identity) {
            matches.push((node.handle, node.props));
        }
    }
    let Ok([(handle, props)]) = <[_; 1]>::try_from(matches) else {
        return Ok(None);
    };
    let row = rows.remove(&handle);
    let generation = registry.begin_read(&window.id, ReadKind::Query);
    let found = registry.register(
        |handle| ax.liveness(handle),
        &window.id,
        generation,
        handle,
        &props,
        Uniqueness::Proven(&walk),
    );
    registry.set_row(found, row);
    Ok(registry.live(found).then_some(found))
}

/// The one element of `window`, other than the one `reference` names, that
/// reads with the role and label the ref was read with: where the control
/// went once the app handed the ref's element to another control. Needs no
/// proof, so the error says it is what this read found.
pub(crate) fn find_read_as<A: AxRead>(
    ax: &mut A,
    registry: &mut Registry<A::Handle>,
    window: &Window,
    reference: ElementRef,
    token: &Token,
) -> Result<Option<ElementRef>, Error> {
    let read_as = registry.fingerprint(reference).map_err(Error::from)?;
    let handle = registry
        .resolve(reference)
        .map(|(handle, _)| handle.clone())
        .map_err(Error::from)?;
    let root = ax.window_root(window)?;
    let (tree, _) = walk(
        ax,
        root,
        Walk::new(
            token,
            super::SnapshotLimits::FIND,
            WalkBounds::Skip,
            Marks::Skip,
        ),
    )?;
    let mut matches = Vec::new();
    let mut stack: Vec<_> = tree.into_iter().collect();
    while let Some(node) = stack.pop() {
        stack.extend(node.children);
        if node.handle != handle
            && node.props.label_read == Completeness::Whole
            && node.props.fingerprint() == read_as
        {
            matches.push((node.handle, node.props));
        }
    }
    let Ok([(found, props)]) = <[_; 1]>::try_from(matches) else {
        return Ok(None);
    };
    let generation = registry.begin_read(&window.id, ReadKind::Query);
    let found = registry.register(
        |handle| ax.liveness(handle),
        &window.id,
        generation,
        found,
        &props,
        Uniqueness::Unknown,
    );
    Ok(registry.live(found).then_some(found))
}
