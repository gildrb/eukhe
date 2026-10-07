//! macOS native watches: `EVFILT_VNODE` registrations on one kqueue per
//! watcher, read on the tokio reactor.
//!
//! Node watches directories on macOS with `FSEvents`, recursively and with entry
//! names. kqueue watches one vnode per descriptor, cannot watch a tree, and a
//! directory's registration does not report changes to its files' contents,
//! so the watcher installs per-directory watches here too and also watches
//! the files inside watched directories (see `Listener::File`). kqueue
//! reports no entry names: a directory event is Node's `filename ===
//! undefined` case (a rescan). Registration is synchronous, so the `FSEvents`
//! settle rescan of TS (`FSEVENTS_SETTLE_MS`) has nothing to catch and is not
//! ported. A registration that fails (out of descriptors, for example) fails
//! `add`, which switches the watcher to polling like a failed `fs.watch`.

use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io;
use std::os::fd::{AsFd, AsRawFd, RawFd};
use std::os::unix::fs::OpenOptionsExt;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use nix::errno::Errno;
use nix::libc::timespec;
use nix::sys::event::{EventFilter, EventFlag, FilterFlag, KEvent, Kqueue};
use tokio::io::unix::AsyncFd;
use tokio::task::JoinHandle;

use super::{HandleId, Listener, Notice, Sink};

/// `O_EVTONLY` of `<sys/fcntl.h>`: a descriptor for event notifications only,
/// which does not keep its volume from being unmounted.
const O_EVTONLY: i32 = 0x0000_8000;

/// Events read per `kevent` call.
const EVENT_BATCH: usize = 64;

const NO_WAIT: timespec = timespec {
    tv_sec: 0,
    tv_nsec: 0,
};

fn vnode_flags() -> FilterFlag {
    FilterFlag::NOTE_DELETE
        | FilterFlag::NOTE_WRITE
        | FilterFlag::NOTE_EXTEND
        | FilterFlag::NOTE_ATTRIB
        | FilterFlag::NOTE_LINK
        | FilterFlag::NOTE_RENAME
        | FilterFlag::NOTE_REVOKE
}

/// The kqueue descriptor, registrable with the tokio reactor.
struct KqueueFd(Kqueue);

impl AsRawFd for KqueueFd {
    fn as_raw_fd(&self) -> RawFd {
        self.0.as_fd().as_raw_fd()
    }
}

/// One watched vnode: dropping `_file` closes the descriptor, which removes
/// its registration.
struct Watch {
    handle: HandleId,
    _file: File,
    listener: Listener,
}

#[derive(Default)]
struct Registry {
    /// Keyed by the watched descriptor, the registration's `ident`.
    watches: HashMap<usize, Watch>,
    next_handle: HandleId,
}

struct Instance {
    fd: AsyncFd<KqueueFd>,
    registry: Mutex<Registry>,
}

impl Instance {
    fn registry(&self) -> MutexGuard<'_, Registry> {
        self.registry.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// The native watches of one watcher. The kqueue and its reader task start
/// with the first watch.
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
        let instance = Arc::new(Instance {
            fd: AsyncFd::new(KqueueFd(Kqueue::new()?))?,
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
    /// fails with the OS error of `open` or `kevent`.
    pub(super) fn add(&mut self, path: &str, listener: Listener) -> io::Result<HandleId> {
        let instance = self.instance()?;
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(O_EVTONLY)
            .open(path)?;
        let ident = usize::try_from(file.as_raw_fd()).map_err(|_| io::Error::from(Errno::EBADF))?;
        let registration = KEvent::new(
            ident,
            EventFilter::EVFILT_VNODE,
            EventFlag::EV_ADD | EventFlag::EV_ENABLE | EventFlag::EV_CLEAR,
            vnode_flags(),
            0,
            0,
        );
        instance
            .fd
            .get_ref()
            .0
            .kevent(&[registration], &mut [], Some(NO_WAIT))?;
        let mut registry = instance.registry();
        registry.next_handle += 1;
        let handle = registry.next_handle;
        registry.watches.insert(
            ident,
            Watch {
                handle,
                _file: file,
                listener,
            },
        );
        Ok(handle)
    }

    /// Stop one handle: closing its descriptor drops the registration. No
    /// event is read for the handle afterwards.
    pub(super) fn remove(&mut self, handle: HandleId) {
        let Some(instance) = &self.instance else {
            return;
        };
        instance
            .registry()
            .watches
            .retain(|_, watch| watch.handle != handle);
    }

    /// Stop every handle and close the kqueue.
    pub(super) fn close(&mut self) {
        if let Some(reader) = self.reader.take() {
            reader.abort();
        }
        if let Some(instance) = self.instance.take() {
            instance.registry().watches.clear();
        }
    }
}

impl Drop for Backend {
    fn drop(&mut self) {
        self.close();
    }
}

/// Read events as they arrive and pass them to the sink, without names.
async fn read_events(instance: Arc<Instance>, sink: Sink) {
    let empty = KEvent::new(
        0,
        EventFilter::EVFILT_VNODE,
        EventFlag::empty(),
        FilterFlag::empty(),
        0,
        0,
    );
    let mut events = vec![empty; EVENT_BATCH];
    loop {
        let Ok(mut ready) = instance.fd.readable().await else {
            sink(vec![Notice::Broken]);
            return;
        };
        let count = match ready.try_io(|fd| {
            match fd.get_ref().0.kevent(&[], &mut events, Some(NO_WAIT)) {
                // Nothing pending: clear readiness and wait for more.
                Ok(0) => Err(io::Error::from(io::ErrorKind::WouldBlock)),
                Ok(count) => Ok(count),
                Err(errno) => Err(io::Error::from(errno)),
            }
        }) {
            Ok(Ok(count)) => count,
            Err(_would_block) => continue,
            Ok(Err(_error)) => {
                sink(vec![Notice::Broken]);
                return;
            }
        };
        let notices: Vec<Notice> = {
            let registry = instance.registry();
            events[..count]
                .iter()
                .filter_map(|event| registry.watches.get(&event.ident()))
                .map(|watch| Notice::Event {
                    listener: watch.listener.clone(),
                    filename: None,
                })
                .collect()
        };
        if !notices.is_empty() {
            sink(notices);
        }
    }
}
