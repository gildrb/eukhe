//! `TypeBox`'s evaluation contexts (`schema/engine/_context.mjs`): the stack of
//! evaluated array indices and object keys `unevaluatedItems` /
//! `unevaluatedProperties` consult, plus the collected errors.
//!
//! Frames are shared (`Rc<RefCell<..>>`) because `TypeBox` captures the live
//! top frame (`context.GetKeys()`) and keeps reading it while nested checks
//! push, pop, or leak frames.

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Default)]
pub(crate) struct Evaluated {
    pub(crate) indices: HashSet<usize>,
    pub(crate) keys: HashSet<String>,
}

pub(crate) type Frame = Rc<RefCell<Evaluated>>;

/// `CheckContext`.
pub(crate) struct CheckContext {
    stack: Vec<Frame>,
}

impl CheckContext {
    pub(crate) fn new() -> Self {
        Self {
            stack: vec![Frame::default()],
        }
    }

    pub(crate) fn push(&mut self) -> bool {
        self.stack.push(Frame::default());
        true
    }

    pub(crate) fn pop(&mut self) -> bool {
        self.stack.pop();
        true
    }

    /// The live top frame (`GetIndices()` / `GetKeys()`).
    pub(crate) fn top(&self) -> Option<Frame> {
        self.stack.last().cloned()
    }

    pub(crate) fn add_index(&mut self, index: usize) -> bool {
        if let Some(top) = self.stack.last() {
            top.borrow_mut().indices.insert(index);
        }
        true
    }

    pub(crate) fn add_key(&mut self, key: &str) -> bool {
        if let Some(top) = self.stack.last() {
            top.borrow_mut().keys.insert(key.to_owned());
        }
        true
    }

    /// `Merge(results)`: each context's top frame into this top frame.
    pub(crate) fn merge<'c>(&mut self, results: impl IntoIterator<Item = &'c Self>) -> bool {
        let Some(top) = self.stack.last().cloned() else {
            return true;
        };
        for context in results {
            let Some(other) = context.stack.last() else {
                continue;
            };
            if Rc::ptr_eq(&top, other) {
                continue;
            }
            let other = other.borrow();
            let mut top = top.borrow_mut();
            top.indices.extend(other.indices.iter().copied());
            top.keys.extend(other.keys.iter().cloned());
        }
        true
    }
}

/// `TypeBox` `Settings.maxErrors`.
const MAX_ERRORS: usize = 8;

/// One `TypeBox` validation error, localized with the `en_US` messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SchemaError {
    pub(crate) keyword: &'static str,
    pub(crate) instance_path: String,
    /// `params.requiredProperties` of a `required` error.
    pub(crate) required_properties: Vec<String>,
    pub(crate) message: String,
}

/// `ErrorContext`: a [`CheckContext`] that also collects errors, up to
/// `maxErrors` per context.
pub(crate) struct ErrorContext {
    pub(crate) check: CheckContext,
    errors: Vec<SchemaError>,
}

impl ErrorContext {
    pub(crate) fn new() -> Self {
        Self {
            check: CheckContext::new(),
            errors: Vec::new(),
        }
    }

    pub(crate) fn at_capacity(&self) -> bool {
        self.errors.len() >= MAX_ERRORS
    }

    /// `AddError(error)`: always `false`, so `check || AddError(..)` fails.
    pub(crate) fn add_error(&mut self, error: SchemaError) -> bool {
        if !self.at_capacity() {
            self.errors.push(error);
        }
        false
    }

    pub(crate) fn into_errors(self) -> Vec<SchemaError> {
        self.errors
    }
}
