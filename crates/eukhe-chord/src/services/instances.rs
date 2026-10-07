//! Keyed instance lifetime and the cancellable tasks observing those
//! instances (port of `services/instances.ts`).

use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use indexmap::IndexMap;

use crate::callback::{Disposer, Outcome};
use crate::context::{with_cancel, CancelContext, Context, BACKGROUND_CONTEXT};
use crate::error::{ChordError, ErrorReporter};
use crate::task::spawn_detached;

use super::handle::SlotTarget;

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// One live keyed instance incarnation.
pub(crate) trait InstanceDirectoryEntry: Send + Sync {
    fn key(&self) -> &str;
    fn generation(&self) -> u64;
    /// The service handed to observers.
    fn service(&self) -> SlotTarget;
    fn deactivate(&self);
}

/// Observes one keyed instance: `(service, context)`. The context is
/// cancelled when the instance retires or the observation stops.
pub(crate) type InstanceObserver = Arc<dyn Fn(SlotTarget, Context) -> Outcome + Send + Sync>;

struct Observer<E> {
    handler: InstanceObserver,
    tasks: Vec<(Arc<E>, CancelContext)>,
    closed: bool,
}

struct DirectoryState<E> {
    entries: IndexMap<String, Arc<E>>,
    observers: Vec<Arc<Mutex<Observer<E>>>>,
    ready: bool,
    disposed: bool,
}

/// Owns keyed instance lifetime and the cancellable tasks observing those
/// instances.
pub(crate) struct InstanceDirectory<E: InstanceDirectoryEntry + 'static> {
    state: Arc<Mutex<DirectoryState<E>>>,
    report: ErrorReporter,
}

impl<E: InstanceDirectoryEntry + 'static> Clone for InstanceDirectory<E> {
    fn clone(&self) -> Self {
        Self {
            state: Arc::clone(&self.state),
            report: Arc::clone(&self.report),
        }
    }
}

/// Whether observers start on insertion right away.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Readiness {
    Ready,
    Pending,
}

/// An observer start prepared under the lock and run after releasing it.
struct Start {
    handler: InstanceObserver,
    service: SlotTarget,
    context: Context,
}

impl<E: InstanceDirectoryEntry + 'static> InstanceDirectory<E> {
    pub(crate) fn new(readiness: Readiness, report: ErrorReporter) -> Self {
        Self {
            state: Arc::new(Mutex::new(DirectoryState {
                entries: IndexMap::new(),
                observers: Vec::new(),
                ready: matches!(readiness, Readiness::Ready),
                disposed: false,
            })),
            report,
        }
    }

    pub(crate) fn observer_count(&self) -> usize {
        lock(&self.state).observers.len()
    }

    pub(crate) fn values(&self) -> Vec<Arc<E>> {
        lock(&self.state).entries.values().cloned().collect()
    }

    pub(crate) fn get(&self, key: &str) -> Option<Arc<E>> {
        lock(&self.state).entries.get(key).cloned()
    }

    pub(crate) fn insert(&self, entry: &Arc<E>) -> Result<(), ChordError> {
        let starts = {
            let mut state = lock(&self.state);
            assert_active(&state)?;
            if state.entries.contains_key(entry.key()) {
                return Err(ChordError::error(format!(
                    "Keyed service already has a live instance with key {}",
                    entry.key()
                )));
            }
            state
                .entries
                .insert(entry.key().to_owned(), Arc::clone(entry));
            if state.ready {
                start_all(&state, entry)
            } else {
                Vec::new()
            }
        };
        self.run(starts);
        Ok(())
    }

    pub(crate) fn replace(&self, entry: &Arc<E>) -> Result<(), ChordError> {
        let (removed, starts) = {
            let mut state = lock(&self.state);
            assert_active(&state)?;
            let mut removed = None;
            if let Some(previous) = state.entries.get(entry.key()).cloned() {
                if previous.generation() == entry.generation() {
                    return Err(ChordError::error(
                        "Keyed service repeated a live generation",
                    ));
                }
                removed = remove_locked(&mut state, &previous);
            }
            state
                .entries
                .insert(entry.key().to_owned(), Arc::clone(entry));
            let starts = if state.ready {
                start_all(&state, entry)
            } else {
                Vec::new()
            };
            (removed, starts)
        };
        if let Some(removed) = removed {
            removed.finish();
        }
        self.run(starts);
        Ok(())
    }

    pub(crate) fn remove(&self, entry: &Arc<E>) {
        let removed = remove_locked(&mut lock(&self.state), entry);
        if let Some(removed) = removed {
            removed.finish();
        }
    }

    pub(crate) fn ready(&self) -> Result<(), ChordError> {
        let starts = {
            let mut state = lock(&self.state);
            assert_active(&state)?;
            if state.ready {
                return Ok(());
            }
            state.ready = true;
            let entries: Vec<Arc<E>> = state.entries.values().cloned().collect();
            entries
                .iter()
                .flat_map(|entry| start_all(&state, entry))
                .collect()
        };
        self.run(starts);
        Ok(())
    }

    pub(crate) fn reset(&self) {
        let removed: Vec<Removed<E>> = {
            let mut state = lock(&self.state);
            if state.disposed {
                return;
            }
            state.ready = false;
            let entries: Vec<Arc<E>> = state.entries.values().cloned().collect();
            entries
                .iter()
                .filter_map(|entry| remove_locked(&mut state, entry))
                .collect()
        };
        for removed in removed {
            removed.finish();
        }
    }

    pub(crate) fn observe(&self, handler: InstanceObserver) -> Result<Disposer, ChordError> {
        let observer = Arc::new(Mutex::new(Observer {
            handler,
            tasks: Vec::new(),
            closed: false,
        }));
        let starts = {
            let mut state = lock(&self.state);
            assert_active(&state)?;
            state.observers.push(Arc::clone(&observer));
            if state.ready {
                let entries: Vec<Arc<E>> = state.entries.values().cloned().collect();
                entries
                    .iter()
                    .filter_map(|entry| start(&observer, entry))
                    .collect()
            } else {
                Vec::new()
            }
        };
        self.run(starts);
        let directory = Arc::downgrade(&self.state);
        Ok(Disposer::new(move || {
            let tasks = {
                let mut observer_state = lock(&observer);
                if observer_state.closed {
                    return;
                }
                observer_state.closed = true;
                std::mem::take(&mut observer_state.tasks)
            };
            for (_, cancel) in tasks {
                cancel.cancel(None);
            }
            if let Some(directory) = directory.upgrade() {
                lock(&directory)
                    .observers
                    .retain(|candidate| !Arc::ptr_eq(candidate, &observer));
            }
        }))
    }

    pub(crate) fn dispose(&self) {
        let (observers, entries) = {
            let mut state = lock(&self.state);
            if state.disposed {
                return;
            }
            state.disposed = true;
            let observers = std::mem::take(&mut state.observers);
            let entries: Vec<Arc<E>> = state.entries.drain(..).map(|(_, entry)| entry).collect();
            (observers, entries)
        };
        for observer in observers {
            let tasks = {
                let mut observer = lock(&observer);
                observer.closed = true;
                std::mem::take(&mut observer.tasks)
            };
            for (_, cancel) in tasks {
                cancel.cancel(None);
            }
        }
        for entry in entries {
            entry.deactivate();
        }
    }

    fn run(&self, starts: Vec<Start>) {
        for Start {
            handler,
            service,
            context,
        } in starts
        {
            let outcome = handler(service, context.clone());
            let report = Arc::clone(&self.report);
            match outcome {
                Outcome::Done => {}
                Outcome::Failed(error) => {
                    if !context.aborted() {
                        report(error);
                    }
                }
                Outcome::Pending(future) => spawn_detached(async move {
                    if let Err(error) = future.await {
                        if !context.aborted() {
                            report(error);
                        }
                    }
                }),
            }
        }
    }
}

/// An entry removed under the lock; deactivation and cancellation run
/// after releasing it.
struct Removed<E> {
    entry: Arc<E>,
    cancels: Vec<CancelContext>,
}

impl<E: InstanceDirectoryEntry> Removed<E> {
    fn finish(self) {
        self.entry.deactivate();
        for cancel in self.cancels {
            cancel.cancel(None);
        }
    }
}

fn remove_locked<E: InstanceDirectoryEntry>(
    state: &mut DirectoryState<E>,
    entry: &Arc<E>,
) -> Option<Removed<E>> {
    let current = state.entries.get(entry.key())?;
    if !Arc::ptr_eq(current, entry) {
        return None;
    }
    state.entries.shift_remove(entry.key());
    let mut cancels = Vec::new();
    for observer in &state.observers {
        let mut observer = lock(observer);
        if let Some(position) = observer
            .tasks
            .iter()
            .position(|(task, _)| Arc::ptr_eq(task, entry))
        {
            cancels.push(observer.tasks.remove(position).1);
        }
    }
    Some(Removed {
        entry: Arc::clone(entry),
        cancels,
    })
}

fn start_all<E: InstanceDirectoryEntry>(state: &DirectoryState<E>, entry: &Arc<E>) -> Vec<Start> {
    state
        .observers
        .iter()
        .filter_map(|observer| start(observer, entry))
        .collect()
}

fn start<E: InstanceDirectoryEntry>(
    observer: &Arc<Mutex<Observer<E>>>,
    entry: &Arc<E>,
) -> Option<Start> {
    let mut observer = lock(observer);
    if observer.closed
        || observer
            .tasks
            .iter()
            .any(|(task, _)| Arc::ptr_eq(task, entry))
    {
        return None;
    }
    let (context, cancel) = with_cancel(&BACKGROUND_CONTEXT);
    observer.tasks.push((Arc::clone(entry), cancel));
    Some(Start {
        handler: Arc::clone(&observer.handler),
        service: entry.service(),
        context,
    })
}

fn assert_active<E>(state: &DirectoryState<E>) -> Result<(), ChordError> {
    if state.disposed {
        return Err(ChordError::error("Keyed service directory is disposed"));
    }
    Ok(())
}
