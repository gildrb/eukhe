//! Application-owned registry of extensions (`harness/registry.ts`).

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use super::agent::INSTRUCTIONS_KEY;
use super::types::{BuiltinTasks, Extension, InstalledSection, InstalledTool, RegistryReader};
use crate::session::{SessionError, SessionResult, Unsubscribe};
use crate::tasks::AnyTask;

/// TS `/^[a-z][a-z0-9_-]*$/`.
const SECTION_KEY_PATTERN: &str = "/^[a-z][a-z0-9_-]*$/";

fn is_section_key(key: &str) -> bool {
    let mut bytes = key.bytes();
    bytes.next().is_some_and(|first| first.is_ascii_lowercase())
        && bytes.all(|byte| {
            byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'_' || byte == b'-'
        })
}

struct RegistryState {
    extensions: Vec<Arc<Extension>>,
    by_name: HashMap<String, Arc<Extension>>,
    /// Built-ins first, then extension tasks in install order.
    tasks: Vec<AnyTask>,
    task_index: HashMap<String, usize>,
    builtins: BuiltinTasks,
}

/// Immutable view of one published registry state (TS `RegistrySnapshot`).
/// Clones share the state; snapshots stay as they were after later
/// publications.
#[derive(Clone)]
pub struct RegistrySnapshot {
    state: Arc<RegistryState>,
}

impl RegistrySnapshot {
    /// The state holding only the built-in tasks (TS `Map.set` per
    /// built-in: a repeated name replaces the value in its first position).
    fn builtins_only(builtins: BuiltinTasks) -> RegistryState {
        let mut tasks: Vec<AnyTask> = Vec::new();
        let mut task_index = HashMap::new();
        for task in builtins.to_vec() {
            if let Some(&index) = task_index.get(task.name()) {
                tasks[index] = task;
            } else {
                task_index.insert(task.name().to_owned(), tasks.len());
                tasks.push(task);
            }
        }
        RegistryState {
            extensions: Vec::new(),
            by_name: HashMap::new(),
            tasks,
            task_index,
            builtins,
        }
    }

    /// Build and validate the state of `extensions`.
    fn new(extensions: Vec<Arc<Extension>>, builtins: BuiltinTasks) -> SessionResult<Self> {
        let mut state = Self::builtins_only(builtins);
        for extension in &extensions {
            for task in &extension.tasks {
                let name = task.name();
                if state.task_index.contains_key(name) {
                    return Err(SessionError::error(format!(
                        "Task {name} of extension {} is already installed",
                        extension.name
                    )));
                }
                state.task_index.insert(name.to_owned(), state.tasks.len());
                state.tasks.push(task.clone());
            }
        }
        state.by_name = extensions
            .iter()
            .map(|extension| (extension.name.clone(), Arc::clone(extension)))
            .collect();
        state.extensions = extensions;
        Ok(Self {
            state: Arc::new(state),
        })
    }

    /// Installed extensions, in install order.
    #[must_use]
    pub fn installed(&self) -> &[Arc<Extension>] {
        &self.state.extensions
    }

    /// The installed extension named `name`.
    #[must_use]
    pub fn extension(&self, name: &str) -> Option<&Arc<Extension>> {
        self.state.by_name.get(name)
    }

    /// Every installed tool with its extension, in install order. Names may
    /// repeat across extensions.
    #[must_use]
    pub fn tools(&self) -> Vec<InstalledTool> {
        self.state
            .extensions
            .iter()
            .flat_map(|extension| {
                extension.tools.iter().map(|tool| InstalledTool {
                    extension: Arc::clone(extension),
                    tool: Arc::clone(tool),
                })
            })
            .collect()
    }

    /// Every installed section with its extension, in install order.
    #[must_use]
    pub fn sections(&self) -> Vec<InstalledSection> {
        self.state
            .extensions
            .iter()
            .flat_map(|extension| {
                extension.sections.iter().map(|section| InstalledSection {
                    extension: Arc::clone(extension),
                    section: Arc::clone(section),
                })
            })
            .collect()
    }

    /// Built-in and installed task definitions.
    #[must_use]
    pub fn tasks(&self) -> Vec<AnyTask> {
        self.state.tasks.clone()
    }

    /// The task definition named `name`.
    #[must_use]
    pub fn task(&self, name: &str) -> Option<&AnyTask> {
        self.state
            .task_index
            .get(name)
            .map(|&index| &self.state.tasks[index])
    }

    /// The built-in task definitions.
    pub(crate) fn builtins(&self) -> &BuiltinTasks {
        &self.state.builtins
    }

    /// Whether both are the same published state.
    #[must_use]
    pub fn ptr_eq(a: &Self, b: &Self) -> bool {
        Arc::ptr_eq(&a.state, &b.state)
    }
}

impl fmt::Debug for RegistrySnapshot {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("RegistrySnapshot")
            .field(
                "installed",
                &self
                    .state
                    .extensions
                    .iter()
                    .map(|extension| extension.name.as_str())
                    .collect::<Vec<_>>(),
            )
            .field(
                "tasks",
                &self
                    .state
                    .tasks
                    .iter()
                    .map(AnyTask::name)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

type Listener = Arc<dyn Fn() + Send + Sync>;

struct RegistryInner {
    current: Mutex<RegistrySnapshot>,
    listeners: Mutex<Vec<(u64, Listener)>>,
    next_listener: Mutex<u64>,
}

/// Application-owned registry of extensions (TS `Registry`). Clones share
/// the registry.
#[derive(Clone)]
pub struct Registry {
    inner: Arc<RegistryInner>,
}

impl fmt::Debug for Registry {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Registry")
            .field("current", &*self.current())
            .finish_non_exhaustive()
    }
}

/// Create an application-owned registry holding only the built-in tasks.
#[must_use]
pub fn create_registry() -> Registry {
    let initial = RegistrySnapshot {
        state: Arc::new(RegistrySnapshot::builtins_only(BuiltinTasks::new())),
    };
    Registry {
        inner: Arc::new(RegistryInner {
            current: Mutex::new(initial),
            listeners: Mutex::new(Vec::new()),
            next_listener: Mutex::new(0),
        }),
    }
}

impl Registry {
    fn current(&self) -> MutexGuard<'_, RegistrySnapshot> {
        self.inner
            .current
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// Install `extension`, or replace the installed extension with its name
    /// in place. Publishes at once.
    ///
    /// # Errors
    ///
    /// The extension has two tools with one name, two sections with one key,
    /// an invalid or reserved section key, or a task whose name is already
    /// installed; nothing is published then.
    pub fn install(&self, extension: Arc<Extension>) -> SessionResult<()> {
        validate_extension(&extension)?;
        let next = {
            let current = self.current();
            let installed = current.installed();
            let index = installed
                .iter()
                .position(|existing| existing.name == extension.name);
            let mut next = installed.to_vec();
            match index {
                Some(index) => next[index] = extension,
                None => next.push(extension),
            }
            (next, current.builtins().clone())
        };
        self.publish(next.0, next.1)
    }

    /// Remove the installed extension with `extension.name`, whichever object
    /// it is. A later install appends.
    pub fn uninstall(&self, extension: &Extension) {
        let next = {
            let current = self.current();
            let installed = current.installed();
            if !installed
                .iter()
                .any(|existing| existing.name == extension.name)
            {
                return;
            }
            let next: Vec<_> = installed
                .iter()
                .filter(|existing| existing.name != extension.name)
                .cloned()
                .collect();
            (next, current.builtins().clone())
        };
        // Removing an extension cannot introduce a task name collision.
        if let Err(error) = self.publish(next.0, next.1) {
            unreachable!("uninstall cannot make the registry invalid: {error}");
        }
    }

    /// Build and validate the next state, which fails on a task name
    /// collision, then publish it synchronously.
    fn publish(
        &self,
        extensions: Vec<Arc<Extension>>,
        builtins: BuiltinTasks,
    ) -> SessionResult<()> {
        let next = RegistrySnapshot::new(extensions, builtins)?;
        *self.current() = next;
        let listeners: Vec<Listener> = self
            .inner
            .listeners
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .iter()
            .map(|(_, listener)| Arc::clone(listener))
            .collect();
        for listener in listeners {
            listener();
        }
        Ok(())
    }
}

impl RegistryReader for Registry {
    fn snapshot(&self) -> RegistrySnapshot {
        self.current().clone()
    }

    fn subscribe(&self, listener: Arc<dyn Fn() + Send + Sync>) -> Unsubscribe {
        let id = {
            let mut next = self
                .inner
                .next_listener
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            *next += 1;
            *next
        };
        self.inner
            .listeners
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push((id, listener));
        let inner = Arc::downgrade(&self.inner);
        Unsubscribe::new(move || {
            let Some(inner) = inner.upgrade() else {
                return false;
            };
            let mut listeners = inner
                .listeners
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            let before = listeners.len();
            listeners.retain(|(each, _)| *each != id);
            listeners.len() != before
        })
    }
}

/// Unique tool names and section keys within one extension; valid,
/// unreserved section keys.
fn validate_extension(extension: &Extension) -> SessionResult<()> {
    let mut tools = HashSet::new();
    for tool in &extension.tools {
        if !tools.insert(tool.name.as_str()) {
            return Err(SessionError::error(format!(
                "Extension {} has two tools named {}",
                extension.name, tool.name
            )));
        }
    }
    let mut sections = HashSet::new();
    for section in &extension.sections {
        let key = section.key.as_str();
        if !is_section_key(key) {
            return Err(SessionError::type_error(format!(
                "Section key {} must match {SECTION_KEY_PATTERN}",
                json_string(key)
            )));
        }
        if key == INSTRUCTIONS_KEY {
            return Err(SessionError::error(format!(
                "Section key {key} is reserved for the agent's instructions"
            )));
        }
        if !sections.insert(key) {
            return Err(SessionError::error(format!(
                "Extension {} has two sections with key {key}",
                extension.name
            )));
        }
    }
    Ok(())
}

/// TS `JSON.stringify(key)` of a string.
fn json_string(key: &str) -> String {
    eukhe_chord::json::JsonValue::from(key).to_string()
}
