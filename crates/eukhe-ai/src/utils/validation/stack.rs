//! `TypeBox`'s traversal scope tracker (`schema/engine/_stack.mjs`): `$id`
//! resources, `$recursiveAnchor`/`$dynamicAnchor` scopes, and the base URLs
//! references resolve against. Schema identity is pointer identity.

use super::js_value::{JsError, JsValue};
use super::keywords;
use super::resolve::{self, Resolved, StackFrame, DEFAULT_BASE};

struct RetrievedFrame<'s> {
    schema: &'s JsValue,
    base: String,
    id_depth: usize,
    resource_depth: usize,
}

struct Retrieved<'s> {
    target: &'s JsValue,
    base: String,
    root: &'s JsValue,
}

pub(crate) struct Stack<'s> {
    schema: &'s JsValue,
    ids: Vec<&'s JsValue>,
    resource_ids: Vec<&'s JsValue>,
    recursive_anchors: Vec<&'s JsValue>,
    dynamic_anchors: Vec<&'s JsValue>,
    retrieved_resources: Vec<Retrieved<'s>>,
    retrieved_frames: Vec<RetrievedFrame<'s>>,
    resolved_resources: Vec<(&'s JsValue, &'s JsValue)>,
    pending_resource: bool,
}

impl<'s> Stack<'s> {
    pub(crate) fn new(schema: &'s JsValue) -> Self {
        Self {
            schema,
            ids: Vec::new(),
            resource_ids: Vec::new(),
            recursive_anchors: Vec::new(),
            dynamic_anchors: Vec::new(),
            retrieved_resources: Vec::new(),
            retrieved_frames: Vec::new(),
            resolved_resources: Vec::new(),
            pending_resource: true,
        }
    }

    fn retrieved(&self, schema: &JsValue) -> Option<&Retrieved<'s>> {
        self.retrieved_resources
            .iter()
            .find(|retrieved| std::ptr::eq(retrieved.target, schema))
    }

    /// `Stack.LexicalBaseURL()`.
    pub(crate) fn lexical_base_url(&self) -> Result<String, JsError> {
        self.build_base(&self.ids)
    }

    /// `Stack.Push(schema)`. (`$anchor` scopes are tracked by `TypeBox` but never read.)
    pub(crate) fn push(&mut self, schema: &'s JsValue) {
        if !keywords::is_schema_object(schema) {
            return;
        }
        if keywords::id(schema).is_some() {
            self.register_resource(schema);
        }
        if keywords::is_recursive_anchor_true(schema) {
            self.recursive_anchors.push(schema);
        }
        if keywords::dynamic_anchor(schema).is_some() {
            self.dynamic_anchors.push(schema);
        }
        if let Some(retrieved) = self.retrieved(schema) {
            let frame = RetrievedFrame {
                schema: retrieved.root,
                base: retrieved.base.clone(),
                id_depth: self.ids.len(),
                resource_depth: self.resource_ids.len(),
            };
            self.retrieved_frames.push(frame);
        }
    }

    /// `Stack.Pop(schema)`.
    pub(crate) fn pop(&mut self, schema: &'s JsValue) {
        if !keywords::is_schema_object(schema) {
            return;
        }
        if keywords::id(schema).is_some() {
            self.unregister_resource(schema);
        }
        if keywords::is_recursive_anchor_true(schema) {
            self.recursive_anchors.pop();
        }
        if keywords::dynamic_anchor(schema).is_some() {
            self.dynamic_anchors.pop();
        }
        if self.retrieved(schema).is_some() {
            self.retrieved_frames.pop();
        }
        self.exit_resolved_resource(schema);
    }

    /// `Stack.Ref(ref)`.
    pub(crate) fn resolve_ref(&mut self, reference: &str) -> Result<Option<Resolved<'s>>, JsError> {
        let result = resolve::resolve_ref(&self.stack_frame()?, reference)?;
        if result.schema.is_some() {
            self.pending_resource = true;
        }
        if let Some((target, resource)) = result.resolved_resource {
            self.register_resource(resource);
            self.resolved_resources.push((target, resource));
        }
        if let Some(retrieved) = result.retrieved_resource {
            let entry = Retrieved {
                target: retrieved.target,
                base: retrieved.base,
                root: retrieved.root,
            };
            match self
                .retrieved_resources
                .iter_mut()
                .find(|existing| std::ptr::eq(existing.target, retrieved.target))
            {
                Some(existing) => *existing = entry,
                None => self.retrieved_resources.push(entry),
            }
        }
        Ok(result.schema)
    }

    /// `Stack.RecursiveRef(recursiveRef)`.
    pub(crate) fn resolve_recursive_ref(
        &mut self,
        reference: &str,
    ) -> Result<Option<Resolved<'s>>, JsError> {
        let result = resolve::resolve_recursive_ref(&self.stack_frame()?, reference)?;
        if result.is_some() {
            self.pending_resource = true;
        }
        Ok(result)
    }

    /// `Stack.DynamicRef(dynamicRef)`.
    pub(crate) fn resolve_dynamic_ref(
        &mut self,
        reference: &str,
    ) -> Result<Option<Resolved<'s>>, JsError> {
        let result = resolve::resolve_dynamic_ref(&self.stack_frame()?, reference)?;
        if result.is_some() {
            self.pending_resource = true;
        }
        Ok(result)
    }

    fn stack_frame(&self) -> Result<StackFrame<'_, 's>, JsError> {
        Ok(StackFrame {
            root: self.schema,
            ids: &self.ids,
            lexical_schema: self.lexical_schema(),
            lexical_base: self.lexical_base_url()?,
            reference_base: self.reference_base_url()?,
            resource_base: self.resource_base_url()?,
            recursive_anchors: &self.recursive_anchors,
            dynamic_anchors: &self.dynamic_anchors,
            in_retrieved_frame: !self.retrieved_frames.is_empty(),
        })
    }

    fn build_base(&self, ids: &[&'s JsValue]) -> Result<String, JsError> {
        match self.retrieved_frames.last() {
            Some(frame) => {
                resolve::apply_ids(&frame.base, ids.get(frame.id_depth..).unwrap_or_default())
            }
            None => resolve::apply_ids(DEFAULT_BASE, ids),
        }
    }

    fn resource_base_url(&self) -> Result<String, JsError> {
        match self.retrieved_frames.last() {
            Some(frame) => resolve::apply_ids(
                &frame.base,
                self.resource_ids
                    .get(frame.resource_depth..)
                    .unwrap_or_default(),
            ),
            None => self.build_base(&self.resource_ids),
        }
    }

    fn reference_base_url(&self) -> Result<String, JsError> {
        if !self.retrieved_frames.is_empty() {
            return self.resource_base_url();
        }
        if let Some(id) = self.ids.last().and_then(|lexical| keywords::id(lexical)) {
            if !has_scheme(id) {
                return self.lexical_base_url();
            }
        }
        self.resource_base_url()
    }

    fn lexical_schema(&self) -> &'s JsValue {
        match self.retrieved_frames.last() {
            Some(frame) if self.ids.len() > frame.id_depth => {
                self.ids.last().copied().unwrap_or(frame.schema)
            }
            Some(frame) => frame.schema,
            None => self.ids.last().copied().unwrap_or(self.schema),
        }
    }

    fn register_resource(&mut self, schema: &'s JsValue) {
        self.ids.push(schema);
        let is_resource = self.pending_resource;
        self.pending_resource = false;
        if is_resource {
            self.resource_ids.push(schema);
        }
        self.register_resource_anchors(schema, true);
    }

    fn unregister_resource(&mut self, schema: &'s JsValue) {
        self.ids.pop();
        if self
            .resource_ids
            .last()
            .is_some_and(|last| std::ptr::eq(*last, schema))
        {
            self.resource_ids.pop();
        }
        self.unregister_resource_anchors(schema, true);
    }

    /// Registers the `$dynamicAnchor`s of a resource, stopping at nested `$id`s.
    fn register_resource_anchors(&mut self, schema: &'s JsValue, is_root: bool) {
        match schema {
            JsValue::Array(items) => {
                for item in items {
                    self.register_resource_anchors(item, false);
                }
            }
            JsValue::Object(object) => {
                if !is_root && keywords::id(schema).is_some() {
                    return;
                }
                if !is_root && keywords::dynamic_anchor(schema).is_some() {
                    self.dynamic_anchors.push(schema);
                }
                for (_, value) in object.entries() {
                    self.register_resource_anchors(value, false);
                }
            }
            JsValue::Null
            | JsValue::Bool(_)
            | JsValue::Number(_)
            | JsValue::String(_)
            | JsValue::Function(_) => {}
        }
    }

    fn unregister_resource_anchors(&mut self, schema: &'s JsValue, is_root: bool) {
        match schema {
            JsValue::Array(items) => {
                for item in items {
                    self.unregister_resource_anchors(item, false);
                }
            }
            JsValue::Object(object) => {
                if !is_root && keywords::id(schema).is_some() {
                    return;
                }
                if !is_root && keywords::dynamic_anchor(schema).is_some() {
                    self.dynamic_anchors.pop();
                }
                for (_, value) in object.entries() {
                    self.unregister_resource_anchors(value, false);
                }
            }
            JsValue::Null
            | JsValue::Bool(_)
            | JsValue::Number(_)
            | JsValue::String(_)
            | JsValue::Function(_) => {}
        }
    }

    fn exit_resolved_resource(&mut self, target: &'s JsValue) {
        let Some(position) = self
            .resolved_resources
            .iter()
            .position(|(entry, _)| std::ptr::eq(*entry, target))
        else {
            return;
        };
        let (_, resource) = self.resolved_resources.remove(position);
        self.unregister_resource(resource);
    }
}

/// `/^[A-Za-z][A-Za-z0-9+.-]*:/.test(id)`.
fn has_scheme(id: &str) -> bool {
    let mut chars = id.chars();
    if !chars.next().is_some_and(|c| c.is_ascii_alphabetic()) {
        return false;
    }
    for c in chars {
        if c == ':' {
            return true;
        }
        if !(c.is_ascii_alphanumeric() || matches!(c, '+' | '.' | '-')) {
            return false;
        }
    }
    false
}
