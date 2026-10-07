//! Linux native watches: one non-blocking inotify instance per watcher, read
//! on the tokio reactor, with libuv's mapping of events to file names.
//!
//! libuv (`src/unix/linux.c`) adds every `fs.watch` path with
//! `IN_ATTRIB | IN_CREATE | IN_MODIFY | IN_DELETE | IN_DELETE_SELF |
//! IN_MOVE_SELF | IN_MOVED_FROM | IN_MOVED_TO`, shares one watch descriptor
//! between paths naming the same inode, and reports every event of a known
//! descriptor with the entry name, or with the basename of the descriptor's
//! first path when the event names none (events on the watched inode itself,
//! including `IN_IGNORED` once the kernel dropped the watch). It never reports
//! an error status for inotify handles, so Node's watcher `'error'` event
//! cannot happen here: a watched directory that disappears produces an event
//! (and a rescan) like any other.

use std::collections::HashMap;
use std::io;
use std::os::fd::{AsFd, AsRawFd, RawFd};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use nix::sys::inotify::{AddWatchFlags, InitFlags, Inotify, WatchDescriptor};
use tokio::io::unix::AsyncFd;
use tokio::task::JoinHandle;

use super::paths::basename;
use super::{HandleId, Listener, Notice, Sink};

/// The mask libuv's `uv_fs_event_start` watches with.
fn watch_mask() -> AddWatchFlags {
    AddWatchFlags::IN_ATTRIB
        | AddWatchFlags::IN_CREATE
        | AddWatchFlags::IN_MODIFY
        | AddWatchFlags::IN_DELETE
        | AddWatchFlags::IN_DELETE_SELF
        | AddWatchFlags::IN_MOVE_SELF
        | AddWatchFlags::IN_MOVED_FROM
        | AddWatchFlags::IN_MOVED_TO
}

/// The inotify descriptor, registrable with the tokio reactor.
struct InotifyFd(Inotify);

impl AsRawFd for InotifyFd {
    fn as_raw_fd(&self) -> RawFd {
        self.0.as_fd().as_raw_fd()
    }
}

/// libuv's `watcher_list`: the path the descriptor was first added for and
/// every handle sharing it.
struct WatchList {
    path: String,
    handles: Vec<(HandleId, Listener)>,
}

#[derive(Default)]
struct Registry {
    lists: HashMap<WatchDescriptor, WatchList>,
    handles: HashMap<HandleId, WatchDescriptor>,
    next_handle: HandleId,
}

struct Instance {
    fd: AsyncFd<InotifyFd>,
    registry: Mutex<Registry>,
}

impl Instance {
    fn registry(&self) -> MutexGuard<'_, Registry> {
        self.registry.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// The native watches of one watcher. The inotify instance and its reader
/// task start with the first watch, like libuv's per-loop instance.
pub(super) struct Backend {
    sink: Sink,
    instance: Option<Arc<Instance>>,
    reader: Option<JoinHandle<()>>,
}

impl Backend {
    pub(super) fn new(sink: Sink) -> Self {
        Self {
            sink,
            instance: None,
            reader: None,
        }
    }

    fn instance(&mut self) -> io::Result<Arc<Instance>> {
        if let Some(instance) = &self.instance {
            return Ok(Arc::clone(instance));
        }
        let inotify = Inotify::init(InitFlags::IN_NONBLOCK | InitFlags::IN_CLOEXEC)?;
        let instance = Arc::new(Instance {
            fd: AsyncFd::new(InotifyFd(inotify))?,
            registry: Mutex::new(Registry::default()),
        });
        self.reader = Some(tokio::spawn(read_events(
            Arc::clone(&instance),
            Arc::clone(&self.sink),
        )));
        self.instance = Some(Arc::clone(&instance));
        Ok(instance)
    }

    /// Watch `path` (following symbolic links), reporting to `listener`;
    /// fails with the OS error `fs.watch` throws.
    pub(super) fn add(&mut self, path: &str, listener: Listener) -> io::Result<HandleId> {
        let instance = self.instance()?;
        let descriptor = instance.fd.get_ref().0.add_watch(path, watch_mask())?;
        let mut registry = instance.registry();
        registry.next_handle += 1;
        let handle = registry.next_handle;
        registry
            .lists
            .entry(descriptor)
            .or_insert_with(|| WatchList {
                path: path.to_owned(),
                handles: Vec::new(),
            })
            .handles
            .push((handle, listener));
        registry.handles.insert(handle, descriptor);
        Ok(handle)
    }

    /// Stop one handle; the descriptor goes when its last handle does. No
    /// event is read for the handle afterwards.
    pub(super) fn remove(&mut self, handle: HandleId) {
        let Some(instance) = &self.instance else {
            return;
        };
        let mut registry = instance.registry();
        let Some(descriptor) = registry.handles.remove(&handle) else {
            return;
        };
        let Some(list) = registry.lists.get_mut(&descriptor) else {
            return;
        };
        list.handles.retain(|(id, _)| *id != handle);
        if list.handles.is_empty() {
            registry.lists.remove(&descriptor);
            // Like libuv, the result is ignored: the kernel already dropped the watch of a
            // deleted inode (EINVAL), which leaves nothing to remove.
            instance.fd.get_ref().0.rm_watch(descriptor).ok();
        }
    }

    /// Stop every handle and close the inotify descriptor.
    pub(super) fn close(&mut self) {
        if let Some(reader) = self.reader.take() {
            reader.abort();
        }
        self.instance = None;
    }
}

impl Drop for Backend {
    fn drop(&mut self) {
        self.close();
    }
}

/// Read events as they arrive and pass them to the sink with libuv's names.
async fn read_events(instance: Arc<Instance>, sink: Sink) {
    loop {
        let Ok(mut ready) = instance.fd.readable().await else {
            sink(vec![Notice::Broken]);
            return;
        };
        let events = match ready.try_io(|fd| fd.get_ref().0.read_events().map_err(io::Error::from))
        {
            Ok(Ok(events)) => events,
            // Drained (EAGAIN): readiness was cleared; wait for more.
            Err(_would_block) => continue,
            Ok(Err(_error)) => {
                sink(vec![Notice::Broken]);
                return;
            }
        };
        let notices = {
            let registry = instance.registry();
            let mut notices = Vec::new();
            for event in events {
                if event.mask.contains(AddWatchFlags::IN_Q_OVERFLOW) {
                    notices.push(Notice::Overflow);
                    continue;
                }
                // A stale event: no handles left on the descriptor.
                let Some(list) = registry.lists.get(&event.wd) else {
                    continue;
                };
                let filename = match &event.name {
                    Some(name) => name.to_string_lossy().into_owned(),
                    None => basename(&list.path).to_owned(),
                };
                for (_, listener) in &list.handles {
                    notices.push(Notice::Event {
                        listener: listener.clone(),
                        filename: Some(filename.clone()),
                    });
                }
            }
            notices
        };
        if !notices.is_empty() {
            sink(notices);
        }
    }
}
