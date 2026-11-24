//! The session worker: serves one job at a time with the backend, ref
//! registry and frames it owns (port of the `Worker` of omp
//! `crates/natives/src/desktop/mod.rs`).

use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Instant;

use super::{
    ActReport, Job, KeyTarget, Observation, ObserveOptions, PointTarget, SessionOptions, Step,
};
use crate::applications::{self, OpenRequest, Opened};
use crate::ax::tree::{FindQuery, FoundNode};
use crate::ax::{self, AxRead, Completeness, ElementRef, Liveness, Registry, WindowRead};
use crate::backend::{Delivery, PointerEvent, Typing};
use crate::control::intervention::{InputWatch, Listener};
use crate::control::{CancelSource, InputLease, Token};
use crate::error::{
    Detail, Done, Effect, ElementError, Error, Feature, Quoted, Refusal, StaleCause, StaleRef,
    Unverified,
};
use crate::frame::{self, FrameError, FrameGeometry};
use crate::geometry::GlobalPoint;
use crate::menus::{self, MenuItem, MenuPath};
use crate::platform::{self, AxHandle, Backend, EscapeMonitor};
use crate::text_range::{utf16_slice, TextSelectRequest, TextSelection};
use crate::types::{
    DeliveryMode, MenuPress, Takeover, Window, WindowFilter, WindowId, WindowSelector,
};

/// Answers a caller; one that stopped waiting needs no answer.
fn answer<T>(reply: &mpsc::SyncSender<T>, value: T) {
    reply.send(value).ok();
}

/// Opens the backend, reports it through `ready`, then serves `inbox` until
/// every sender is gone.
pub(super) fn run(
    options: &SessionOptions,
    cancel: CancelSource,
    inbox: &mpsc::Receiver<Job>,
    ready: &mpsc::SyncSender<Result<(), Error>>,
) {
    let backend = match Backend::open() {
        Ok(backend) => backend,
        Err(error) => return answer(ready, Err(error)),
    };
    answer(ready, Ok(()));
    let mut worker = Worker {
        backend,
        registry: Registry::default(),
        frames: HashMap::new(),
        listener: Listener::default(),
        options,
        cancel,
    };
    for job in inbox {
        worker.serve(job);
    }
}

/// The session's state on its worker thread.
struct Worker<'o> {
    backend: Backend,
    registry: Registry<AxHandle>,
    /// Each window's last delivered screenshot.
    frames: HashMap<WindowId, FrameGeometry>,
    listener: Listener,
    options: &'o SessionOptions,
    cancel: CancelSource,
}

/// What every attempt of one step shares.
#[derive(Clone, Copy)]
struct Attempt<'a> {
    window: &'a Window,
    takeover: Takeover,
    token: &'a Token,
    watch: &'a InputWatch,
}

fn unconfirmed(detail: impl Into<Detail>) -> Error {
    Error::Unverified(Unverified::AxUnconfirmed {
        detail: detail.into(),
    })
}

impl Worker<'_> {
    fn serve(&mut self, job: Job) {
        match job {
            Job::Capabilities { reply } => answer(&reply, self.backend.capabilities()),
            Job::Windows { filter, reply } => answer(&reply, self.windows(&filter)),
            Job::Window { selector, reply } => answer(&reply, self.window(&selector)),
            Job::Observe {
                selector,
                options,
                token,
                reply,
            } => answer(&reply, self.observe(&selector, options, &token)),
            Job::Find {
                selector,
                query,
                token,
                reply,
            } => answer(&reply, self.find(&selector, &query, &token)),
            Job::MenuItems {
                selector,
                path,
                reply,
            } => answer(&reply, self.menu_items(&selector, &path)),
            Job::Applications { query, reply } => answer(
                &reply,
                platform::list_applications().map(|apps| applications::filter(apps, &query)),
            ),
            Job::Roster { reply } => answer(&reply, platform::window_roster()),
            Job::Act {
                selector,
                steps,
                takeover,
                token,
                reply,
            } => answer(&reply, self.act(&selector, &steps, takeover, &token)),
            Job::Open {
                request,
                token,
                reply,
            } => answer(&reply, self.open(&request, &token)),
        }
    }

    fn windows(&mut self, filter: &WindowFilter) -> Result<Vec<Window>, Error> {
        let mut windows = self.backend.windows()?;
        windows.retain(|window| filter.matches(window));
        Ok(windows)
    }

    fn window(&mut self, selector: &WindowSelector) -> Result<Window, Error> {
        Ok(selector.resolve(self.backend.windows()?)?)
    }

    /// Watches the user's input into `window`'s app from now on.
    fn touch(&mut self, window: &Window) {
        if let Some(pid) = window.pid {
            self.listener.touch(pid, &window.app);
        }
    }

    fn observe(
        &mut self,
        selector: &WindowSelector,
        options: ObserveOptions,
        token: &Token,
    ) -> Result<Observation, Error> {
        let began = Instant::now();
        let window = self.window(selector)?;
        token.check()?;
        self.touch(&window);
        let screenshot = match options.screenshot {
            Some(caps) => {
                let capture = self.backend.capture(&window)?;
                let (screenshot, geometry) = frame::deliver(capture, &window, caps)?;
                self.frames.insert(window.id.clone(), geometry);
                Some(screenshot)
            }
            None => None,
        };
        let tree = match &options.tree {
            Some(tree) => Some(ax::snapshot(
                &mut self.backend,
                &mut self.registry,
                &window,
                tree,
                platform::ACTION_NAMES,
                token,
            )?),
            None => None,
        };
        if let Some(pid) = window.pid {
            self.listener.read(pid, began);
        }
        Ok(Observation {
            window,
            screenshot,
            tree,
        })
    }

    fn find(
        &mut self,
        selector: &WindowSelector,
        query: &FindQuery,
        token: &Token,
    ) -> Result<Vec<FoundNode>, Error> {
        let window = self.window(selector)?;
        self.touch(&window);
        ax::query(&mut self.backend, &mut self.registry, &window, query, token)
    }

    fn menu_items(
        &mut self,
        selector: &WindowSelector,
        path: &[String],
    ) -> Result<Vec<MenuItem>, Error> {
        let window = self.window(selector)?;
        self.backend.menu_items(&window, path)
    }

    fn open(&mut self, request: &OpenRequest, token: &Token) -> Result<Opened, Error> {
        let _lease = InputLease::acquire(&self.options.input_lock, &self.options.holder, token)?;
        token.check()?;
        applications::open(request)
    }

    /// Runs `steps` in order under the input lease, stopping after the
    /// first step that is not confirmed.
    fn act(
        &mut self,
        selector: &WindowSelector,
        steps: &[Step],
        takeover: Takeover,
        token: &Token,
    ) -> Result<ActReport, Error> {
        let window = self.window(selector)?;
        let _lease = InputLease::acquire(&self.options.input_lock, &self.options.holder, token)?;
        self.touch(&window);
        let watch = match window.pid {
            Some(pid) => self.listener.admit(pid, token)?,
            None => InputWatch::Unwatched,
        };
        let attempt = Attempt {
            window: &window,
            takeover,
            token,
            watch: &watch,
        };
        let mut effects = Vec::with_capacity(steps.len());
        for step in steps {
            let effect = match self.step(attempt, step) {
                Ok(done) => Effect::Confirmed { done },
                Err(error) => Effect::from(error),
            };
            let confirmed = matches!(effect, Effect::Confirmed { .. });
            effects.push(effect);
            if !confirmed {
                break;
            }
        }
        Ok(ActReport { steps: effects })
    }

    fn step(&mut self, attempt: Attempt<'_>, step: &Step) -> Result<Done, Error> {
        attempt.token.check()?;
        match step {
            Step::Press { target } => self
                .on_element(attempt, *target, |backend, handle, delivery| {
                    backend.press(handle, delivery)
                })
                .map(|()| Done::Delivered),
            Step::SetValue { target, value } => self.set_value(attempt, *target, value),
            Step::Type { text, into } => self.typing(attempt, *into, Typing::Text(text)),
            Step::Key { chord, into } => self.typing(attempt, *into, Typing::Chord(*chord)),
            Step::Click {
                at,
                button,
                count,
                modifiers,
            } => {
                let (window, at) = self.point(attempt, *at)?;
                let event = PointerEvent::Click {
                    at,
                    button: *button,
                    count: *count,
                    modifiers: *modifiers,
                };
                self.send(attempt, |backend, delivery| {
                    backend.pointer(&window, &event, delivery)
                })
                .map(|()| Done::Delivered)
            }
            Step::Scroll { at, delta } => {
                let (window, at) = self.point(attempt, *at)?;
                let event = PointerEvent::Scroll { at, delta: *delta };
                self.send(attempt, |backend, delivery| {
                    backend.pointer(&window, &event, delivery)
                })
                .map(|()| Done::Delivered)
            }
            Step::Menu { path } => self.menu(attempt, path),
            Step::SelectText { target, request } => self.select_text(attempt, *target, request),
        }
    }

    /// Sends `input` in the background; when the background route refuses
    /// and the policy allows it, reruns it once as a takeover.
    fn send<T>(
        &mut self,
        attempt: Attempt<'_>,
        mut input: impl FnMut(&mut Backend, &Delivery<'_>) -> Result<T, Error>,
    ) -> Result<T, Error> {
        let background = Delivery::new(
            DeliveryMode::Background,
            MenuPress::from(attempt.takeover),
            attempt.token,
            attempt.watch,
        );
        let result = input(&mut self.backend, &background);
        let refused = matches!(
            result,
            Err(Error::Refused(Refusal::BackgroundUnavailable { .. }))
        );
        match (refused, attempt.takeover) {
            (true, Takeover::Fallback) => {
                let backend = &mut self.backend;
                attempt
                    .watch
                    .admit_takeover(attempt.token, || backend.input_held())?;
                self.backend.admit_takeover(attempt.token)?;
                let _escape = self.escape_stop()?;
                let takeover = Delivery::new(
                    DeliveryMode::Takeover,
                    MenuPress::Allow,
                    attempt.token,
                    attempt.watch,
                );
                input(&mut self.backend, &takeover)
            }
            (true, Takeover::Refuse) | (false, _) => result,
        }
    }

    /// Arms the physical Escape stop for a takeover.
    fn escape_stop(&self) -> Result<Option<EscapeMonitor>, Error> {
        match EscapeMonitor::start(self.cancel.emergency_stop()) {
            Ok(monitor) => Ok(Some(monitor)),
            // A desktop without the stop takes over without it; a cancel
            // still stops the takeover.
            Err(Error::Refused(Refusal::Unsupported {
                feature: Feature::EscapeStop,
            })) => Ok(None),
            Err(error) => Err(error),
        }
    }

    /// Sends `input` to `reference`'s element, naming where the element went
    /// when the app destroyed or relabelled it.
    fn on_element<T>(
        &mut self,
        attempt: Attempt<'_>,
        reference: ElementRef,
        mut input: impl FnMut(&mut Backend, &AxHandle, &Delivery<'_>) -> Result<T, Error>,
    ) -> Result<T, Error> {
        let (handle, read) = self.element(attempt, reference)?;
        let result = self.send(attempt, |backend, delivery| {
            input(backend, &handle, delivery)
        });
        result.map_err(|error| self.stale(attempt, reference, error, read))
    }

    /// The live element `reference` names in the step's window, held to the
    /// role and label it was read with.
    fn element(
        &mut self,
        attempt: Attempt<'_>,
        reference: ElementRef,
    ) -> Result<(AxHandle, Option<WindowRead<AxHandle>>), Error> {
        let read = self.follow_row(attempt, reference)?;
        let (handle, owner) = self.registry.resolve(reference)?;
        if *owner != attempt.window.id {
            return Err(ElementError::OtherWindow {
                reference,
                window: owner.clone(),
            }
            .into());
        }
        let handle = handle.clone();
        let Some(held) = self.registry.held(reference) else {
            return Ok((handle, read));
        };
        let props = self
            .backend
            .props(&handle)
            .map_err(|error| self.stale(attempt, reference, error, None))?;
        if props.label_read == Completeness::Whole && props.fingerprint() != held {
            let label = props.label().map(str::to_owned);
            let candidate = ax::find_read_as(
                &mut self.backend,
                &mut self.registry,
                attempt.window,
                reference,
                attempt.token,
            )?;
            return Err(StaleRef {
                reference,
                cause: StaleCause::ReadsAs {
                    role: props.role,
                    label,
                    candidate,
                },
            }
            .into());
        }
        Ok((handle, read))
    }

    /// Points a ref read in a table row at the row's rebuilt copy once its
    /// own element is gone; returns the whole read when no copy matched.
    fn follow_row(
        &mut self,
        attempt: Attempt<'_>,
        reference: ElementRef,
    ) -> Result<Option<WindowRead<AxHandle>>, Error> {
        if !self.registry.has_row(reference) {
            return Ok(None);
        }
        let handle = self.registry.resolve(reference)?.0.clone();
        match self.backend.liveness(&handle) {
            Liveness::Alive => Ok(None),
            Liveness::Gone => ax::follow_row(
                &mut self.backend,
                &mut self.registry,
                attempt.window,
                reference,
                attempt.token,
            ),
        }
    }

    /// Turns an element's `Vanished` or `ReadsAs` into a `StaleRef` naming
    /// the one candidate the window holds.
    fn stale(
        &mut self,
        attempt: Attempt<'_>,
        reference: ElementRef,
        error: Error,
        read: Option<WindowRead<AxHandle>>,
    ) -> Error {
        if let Error::Refused(Refusal::Vanished) = error {
            return match ax::refind_in(
                &mut self.backend,
                &mut self.registry,
                attempt.window,
                reference,
                read,
                attempt.token,
            ) {
                Ok(candidate) => StaleRef {
                    reference,
                    cause: StaleCause::Destroyed { candidate },
                }
                .into(),
                Err(search) => search,
            };
        }
        if let Error::Refused(Refusal::ReadsAs { role, label }) = error {
            return match ax::find_read_as(
                &mut self.backend,
                &mut self.registry,
                attempt.window,
                reference,
                attempt.token,
            ) {
                Ok(candidate) => StaleRef {
                    reference,
                    cause: StaleCause::ReadsAs {
                        role,
                        label,
                        candidate,
                    },
                }
                .into(),
                Err(search) => search,
            };
        }
        error
    }

    fn set_value(
        &mut self,
        attempt: Attempt<'_>,
        reference: ElementRef,
        value: &str,
    ) -> Result<Done, Error> {
        let readback = self.on_element(attempt, reference, |backend, handle, delivery| {
            backend.set_value(handle, value, delivery)
        })?;
        ax::text_readback(value, value, readback.actual.as_deref(), readback.field)
            .map_err(|readback| Error::Unverified(Unverified::Readback(readback)))?;
        self.confirm_read_as(reference)?;
        Ok(Done::Delivered)
    }

    /// After a write: a confirmed write to an element that now reads as
    /// another control may have gone to that control.
    fn confirm_read_as(&mut self, reference: ElementRef) -> Result<(), Error> {
        let Some(held) = self.registry.held(reference) else {
            return Ok(());
        };
        let handle = self.registry.resolve(reference)?.0.clone();
        // A read failing after the write (the app rebuilt the element) cannot
        // tell: the write's own read-back stands.
        let Ok(props) = self.backend.props(&handle) else {
            return Ok(());
        };
        if props.label_read == Completeness::Whole && props.fingerprint() != held {
            return Err(unconfirmed(format!(
                "the value was written, but {reference} now reads as {}{} after the write, so it \
                 may have gone to that control",
                props.role,
                Quoted(props.label())
            )));
        }
        Ok(())
    }

    fn typing(
        &mut self,
        attempt: Attempt<'_>,
        into: KeyTarget,
        typing: Typing<'_>,
    ) -> Result<Done, Error> {
        match into {
            KeyTarget::Focused => self.send(attempt, |backend, delivery| {
                backend.window_input(attempt.window, typing, delivery)
            }),
            KeyTarget::Element(reference) => {
                self.on_element(attempt, reference, |backend, handle, delivery| {
                    backend.element_input(handle, typing, delivery)
                })
            }
        }
        .map(|()| Done::Delivered)
    }

    /// The window a pointer step goes to, as it is now, and the global point:
    /// an element's center, or a frame pixel mapped through the window's
    /// last screenshot.
    fn point<'a>(
        &mut self,
        attempt: Attempt<'a>,
        target: PointTarget,
    ) -> Result<(Cow<'a, Window>, GlobalPoint), Error> {
        match target {
            PointTarget::Element(reference) => {
                let (handle, _) = self.element(attempt, reference)?;
                let props = self
                    .backend
                    .props(&handle)
                    .map_err(|error| self.stale(attempt, reference, error, None))?;
                let bounds = props.bounds.ok_or(ElementError::NoBounds(reference))?;
                Ok((Cow::Borrowed(attempt.window), bounds.center()))
            }
            PointTarget::Pixel(point) => {
                let id = &attempt.window.id;
                let geometry = *self
                    .frames
                    .get(id)
                    .ok_or_else(|| FrameError::NoCapture { window: id.clone() })?;
                let current = self.window(&WindowSelector::Id(id.clone()))?;
                let at = geometry.map_point(point, &current)?;
                Ok((Cow::Owned(current), at))
            }
        }
    }

    /// Resolves `path` level by level against the menus the window offers,
    /// then presses the command it names.
    fn menu(&mut self, attempt: Attempt<'_>, path: &MenuPath) -> Result<Done, Error> {
        let labels = path.labels();
        let mut resolved: Vec<String> = Vec::with_capacity(labels.len());
        for (depth, label) in labels.iter().enumerate() {
            let mut items = self.backend.menu_items(attempt.window, &resolved)?;
            let item = items.swap_remove(menus::match_label(&items, label)?);
            if depth + 1 == labels.len() {
                menus::require_command(&item)?;
            }
            resolved.push(item.title);
        }
        self.send(attempt, |backend, delivery| {
            backend.menu_press(attempt.window, &resolved, delivery)
        })
        .map(|()| Done::Delivered)
    }

    fn select_text(
        &mut self,
        attempt: Attempt<'_>,
        reference: ElementRef,
        request: &TextSelectRequest,
    ) -> Result<Done, Error> {
        let readback = self.on_element(attempt, reference, |backend, handle, delivery| {
            let value = backend.text_value(handle)?;
            let range = request.locate(&value)?;
            backend.select_range(handle, range, delivery)
        })?;
        let text = utf16_slice(&readback.value, readback.range)
            .ok_or_else(|| unconfirmed("the selection read back runs past the element's value"))?;
        let offset = |units: usize| {
            u32::try_from(units)
                .map_err(|_| unconfirmed("the selection read back is past 4 GiB of text"))
        };
        Ok(Done::Selected {
            selection: TextSelection {
                start: offset(readback.range.start)?,
                length: offset(readback.range.length)?,
                text: text.to_owned(),
                focus: readback.focus,
            },
        })
    }
}
