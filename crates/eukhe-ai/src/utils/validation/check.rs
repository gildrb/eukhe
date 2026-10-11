//! `TypeBox` `Check` (`schema/engine/*` `Check*` functions): a boolean
//! validation of a value against a schema.
//!
//! Node runs the JIT-compiled checker; it agrees with the interpreter except
//! where [`Mode::Compiled`] says otherwise: the `additionalProperties` own-key
//! count fast path, `not` discarding the inner context, and keywordless `$ref`
//! targets (arrays, functions) passing.

use super::context::CheckContext;
use super::engine::{
    can_additional_properties_fast, check_type, const_matches, hash, instance_entries,
    is_max_length, is_min_length, is_multiple_of, properties_pattern, property, ref_target, Engine,
    Mode, RefTarget,
};
use super::format;
use super::js_value::{usize_to_f64, JsError, JsObject, JsValue, TRUE_SCHEMA};
use super::keywords::{self, Items};
use super::resolve::Resolved;

type CheckResult = Result<bool, JsError>;

impl<'s> Engine<'_, 's> {
    /// `CheckSchema(stack, context, schema, value)`.
    pub(crate) fn check_schema(
        &mut self,
        cx: &mut CheckContext,
        schema: &'s JsValue,
        value: &JsValue,
    ) -> CheckResult {
        self.enter()?;
        self.stack.push(schema);
        let result = self.check_keywords(cx, schema, value);
        self.stack.pop(schema);
        self.leave();
        result
    }

    /// `CheckSchemaPushStack`: `(Push() && CheckSchema(..)) && Pop()` — a
    /// failing check leaves its frame on the context stack, as in `TypeBox`.
    pub(crate) fn check_schema_push_stack(
        &mut self,
        cx: &mut CheckContext,
        schema: &'s JsValue,
        value: &JsValue,
    ) -> CheckResult {
        Ok(cx.push() && self.check_schema(cx, schema, value)? && cx.pop())
    }

    #[allow(clippy::too_many_lines)] // One branch per keyword, in TypeBox's order.
    fn check_keywords(
        &mut self,
        cx: &mut CheckContext,
        schema: &'s JsValue,
        value: &JsValue,
    ) -> CheckResult {
        if let JsValue::Bool(flag) = schema {
            return Ok(*flag);
        }
        if let Some(type_) = keywords::type_(schema) {
            if !check_type(type_, value) {
                return Ok(false);
            }
        }
        if let JsValue::Object(object) = value {
            if !self.check_object(cx, schema, value, object)? {
                return Ok(false);
            }
        }
        if let JsValue::Array(items) = value {
            if !self.check_array(cx, schema, items)? {
                return Ok(false);
            }
        }
        if let JsValue::String(text) = value {
            if !self.check_string(schema, text)? {
                return Ok(false);
            }
        }
        if let JsValue::Number(number) = value {
            if number.is_finite() && !check_number(schema, *number) {
                return Ok(false);
            }
        }
        if let Some(reference) = keywords::ref_(schema) {
            let target = self.stack.resolve_ref(reference)?;
            if !self.check_ref(cx, target, value)? {
                return Ok(false);
            }
        }
        if let Some(reference) = keywords::recursive_ref(schema) {
            let target = self.stack.resolve_recursive_ref(reference)?;
            if !self.check_scoped_ref(cx, target, value)? {
                return Ok(false);
            }
        }
        if let Some(reference) = keywords::dynamic_ref(schema) {
            let target = self.stack.resolve_dynamic_ref(reference)?;
            if !self.check_scoped_ref(cx, target, value)? {
                return Ok(false);
            }
        }
        if let Some(constant) = keywords::const_(schema) {
            if !const_matches(value, constant) {
                return Ok(false);
            }
        }
        if let Some(options) = keywords::enum_(schema) {
            if !options.iter().any(|option| const_matches(value, option)) {
                return Ok(false);
            }
        }
        if let Some(condition) = keywords::if_(schema) {
            let branch = if self.check_schema(cx, condition, value)? {
                keywords::then(schema).unwrap_or(&TRUE_SCHEMA)
            } else {
                keywords::else_(schema).unwrap_or(&TRUE_SCHEMA)
            };
            if !self.check_schema(cx, branch, value)? {
                return Ok(false);
            }
        }
        if let Some(negated) = keywords::not(schema) {
            if !self.check_not(cx, negated, value)? {
                return Ok(false);
            }
        }
        if let Some(schemas) = keywords::all_of(schema) {
            let passed = self.check_each(schemas, value)?;
            if !(passed.len() == schemas.len() && cx.merge(&passed)) {
                return Ok(false);
            }
        }
        if let Some(schemas) = keywords::any_of(schema) {
            let passed = self.check_each(schemas, value)?;
            if passed.is_empty() || !cx.merge(&passed) {
                return Ok(false);
            }
        }
        if let Some(schemas) = keywords::one_of(schema) {
            let passed = self.check_each(schemas, value)?;
            if !(passed.len() == 1 && cx.merge(&passed)) {
                return Ok(false);
            }
        }
        if let (Some(unevaluated), JsValue::Array(items)) =
            (keywords::unevaluated_items(schema), value)
        {
            if !self.check_unevaluated_items(cx, unevaluated, items)? {
                return Ok(false);
            }
        }
        if let Some(unevaluated) =
            keywords::unevaluated_properties(schema).filter(|_| value.is_object())
        {
            if !self.check_unevaluated_properties(cx, unevaluated, value)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Runs each schema in a fresh context; returns the passing contexts.
    pub(crate) fn check_each(
        &mut self,
        schemas: &'s [JsValue],
        value: &JsValue,
    ) -> Result<Vec<CheckContext>, JsError> {
        let mut passed = Vec::new();
        for schema in schemas {
            let mut next = CheckContext::new();
            if self.check_schema(&mut next, schema, value)? {
                passed.push(next);
            }
        }
        Ok(passed)
    }

    /// `CheckNot`; the compiled form never merges the inner context.
    pub(crate) fn check_not(
        &mut self,
        cx: &mut CheckContext,
        negated: &'s JsValue,
        value: &JsValue,
    ) -> CheckResult {
        let mut next = CheckContext::new();
        let is_not = !self.check_schema(&mut next, negated, value)?;
        Ok(is_not && (self.mode == Mode::Compiled || cx.merge([&next])))
    }

    /// `CheckRef`: the target runs in a fresh context merged on success.
    fn check_ref(
        &mut self,
        cx: &mut CheckContext,
        target: Option<Resolved<'s>>,
        value: &JsValue,
    ) -> CheckResult {
        match (ref_target(target), self.mode) {
            (RefTarget::Schema(target), Mode::Compiled | Mode::Interpreted) => {
                let mut next = CheckContext::new();
                let result = self.check_schema(&mut next, target, value)?;
                if result {
                    cx.merge([&next]);
                }
                Ok(result)
            }
            (RefTarget::Keywordless, Mode::Compiled) => Ok(true),
            (RefTarget::Primitive(error), Mode::Compiled) => Err(error),
            (RefTarget::Keywordless | RefTarget::Primitive(_), Mode::Interpreted) => Ok(false),
        }
    }

    /// `CheckRecursiveRef` / `CheckDynamicRef`: the target runs in this context.
    fn check_scoped_ref(
        &mut self,
        cx: &mut CheckContext,
        target: Option<Resolved<'s>>,
        value: &JsValue,
    ) -> CheckResult {
        match (ref_target(target), self.mode) {
            (RefTarget::Schema(target), Mode::Compiled | Mode::Interpreted) => {
                self.check_schema(cx, target, value)
            }
            (RefTarget::Keywordless, Mode::Compiled) => Ok(true),
            (RefTarget::Primitive(error), Mode::Compiled) => Err(error),
            (RefTarget::Keywordless | RefTarget::Primitive(_), Mode::Interpreted) => Ok(false),
        }
    }

    fn check_object(
        &mut self,
        cx: &mut CheckContext,
        schema: &'s JsValue,
        value: &JsValue,
        object: &JsObject,
    ) -> CheckResult {
        if let Some(required) = keywords::required(schema) {
            if !keywords::strings(required).all(|key| object.has_property_key(key)) {
                return Ok(false);
            }
        }
        if let Some(additional) = keywords::additional_properties(schema) {
            if !self.check_additional_properties(cx, schema, additional, object)? {
                return Ok(false);
            }
        }
        if let Some(dependencies) = keywords::dependencies(schema) {
            let is_length = object.len() == 0;
            let mut is_every = true;
            for (key, dependency) in dependencies.entries() {
                let satisfied = !object.has_property_key(&key)
                    || match dependency {
                        JsValue::Array(keys) => {
                            keywords::strings(keys).all(|key| object.has_property_key(key))
                        }
                        _ => self.check_schema(cx, dependency, value)?,
                    };
                if !satisfied {
                    is_every = false;
                    break;
                }
            }
            if !(is_length || is_every) {
                return Ok(false);
            }
        }
        if let Some(dependent) = keywords::dependent_required(schema) {
            let is_length = object.len() == 0;
            let is_every = dependent.entries().into_iter().all(|(key, keys)| {
                !object.has_property_key(&key)
                    || match keys {
                        JsValue::Array(keys) => {
                            keywords::strings(keys).all(|key| object.has_property_key(key))
                        }
                        _ => true,
                    }
            });
            if !(is_length || is_every) {
                return Ok(false);
            }
        }
        if let Some(dependent) = keywords::dependent_schemas(schema) {
            let is_length = object.len() == 0;
            let mut is_every = true;
            for (key, dependency) in dependent.entries() {
                if object.has_property_key(&key) && !self.check_schema(cx, dependency, value)? {
                    is_every = false;
                    break;
                }
            }
            if !(is_length || is_every) {
                return Ok(false);
            }
        }
        if let Some(pattern_properties) = keywords::pattern_properties(schema) {
            for (pattern, property_schema) in pattern_properties.entries() {
                let regexp = self.regexps.unicode(&pattern)?;
                for (key, property_value) in object.entries() {
                    if regexp.test(key)
                        && !(self.check_schema_push_stack(cx, property_schema, property_value)?
                            && cx.add_key(key))
                    {
                        return Ok(false);
                    }
                }
            }
        }
        if let Some(properties) = keywords::properties(schema) {
            // `InexactOptionalCheck` (`value[key] === undefined`) only holds for
            // absent keys, which already pass, so it is omitted.
            for (key, property_schema) in properties.entries() {
                if object.has_property_key(&key) {
                    let property_value = property(object, &key);
                    if !(self.check_schema_push_stack(cx, property_schema, &property_value)?
                        && cx.add_key(&key))
                    {
                        return Ok(false);
                    }
                }
            }
        }
        if let Some(names) = keywords::property_names(schema) {
            for key in object.keys() {
                if !self.check_schema(cx, names, &JsValue::String(key.to_owned()))? {
                    return Ok(false);
                }
            }
        }
        if keywords::min_properties(schema).is_some_and(|limit| usize_to_f64(object.len()) < limit)
        {
            return Ok(false);
        }
        if keywords::max_properties(schema).is_some_and(|limit| usize_to_f64(object.len()) > limit)
        {
            return Ok(false);
        }
        Ok(true)
    }

    fn check_additional_properties(
        &mut self,
        cx: &mut CheckContext,
        schema: &'s JsValue,
        additional: &'s JsValue,
        object: &JsObject,
    ) -> CheckResult {
        if self.mode == Mode::Compiled {
            if let Some(required) = can_additional_properties_fast(schema) {
                return Ok(object.len() == required);
            }
        }
        let regexp = self.regexps.unicode(&properties_pattern(schema))?;
        for (key, property_value) in object.entries() {
            if !(regexp.test(key)
                || (self.check_schema_push_stack(cx, additional, property_value)?
                    && cx.add_key(key)))
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn check_array(
        &mut self,
        cx: &mut CheckContext,
        schema: &'s JsValue,
        items: &[JsValue],
    ) -> CheckResult {
        if let (Some(additional), Some(Items::Sized(tuple))) =
            (keywords::additional_items(schema), keywords::items(schema))
        {
            for (index, item) in items.iter().enumerate().skip(tuple.len()) {
                if !(self.check_schema_push_stack(cx, additional, item)? && cx.add_index(index)) {
                    return Ok(false);
                }
            }
        }
        if let Some(contains) = keywords::contains(schema) {
            if keywords::min_contains(schema) != Some(0.0) {
                let mut found = false;
                for (index, item) in items.iter().enumerate() {
                    if self.check_schema(cx, contains, item)? && cx.add_index(index) {
                        found = true;
                    }
                }
                if items.is_empty() || !found {
                    return Ok(false);
                }
            }
        }
        if let Some(item_schemas) = keywords::items(schema) {
            if !self.check_items(cx, schema, item_schemas, items)? {
                return Ok(false);
            }
        }
        if let (Some(limit), Some(contains)) =
            (keywords::max_contains(schema), keywords::contains(schema))
        {
            if self.count_contains(cx, contains, items, /*add_index*/ false)? > limit {
                return Ok(false);
            }
        }
        if keywords::max_items(schema).is_some_and(|limit| usize_to_f64(items.len()) > limit) {
            return Ok(false);
        }
        if let (Some(limit), Some(contains)) =
            (keywords::min_contains(schema), keywords::contains(schema))
        {
            if self.count_contains(cx, contains, items, /*add_index*/ true)? < limit {
                return Ok(false);
            }
        }
        if keywords::min_items(schema).is_some_and(|limit| usize_to_f64(items.len()) < limit) {
            return Ok(false);
        }
        if let Some(prefix) = keywords::prefix_items(schema) {
            if !items.is_empty() {
                for (index, (prefix_schema, item)) in prefix.iter().zip(items).enumerate() {
                    if !(self.check_schema_push_stack(cx, prefix_schema, item)?
                        && cx.add_index(index))
                    {
                        return Ok(false);
                    }
                }
            }
        }
        if keywords::unique_items(schema) == Some(true) {
            let mut hashes: Vec<u64> = items.iter().map(hash).collect();
            hashes.sort_unstable();
            hashes.dedup();
            if hashes.len() != items.len() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn check_items(
        &mut self,
        cx: &mut CheckContext,
        schema: &'s JsValue,
        item_schemas: Items<'s>,
        items: &[JsValue],
    ) -> CheckResult {
        match item_schemas {
            Items::Sized(tuple) => {
                for (index, (item_schema, item)) in tuple.iter().zip(items).enumerate() {
                    if !(self.check_schema_push_stack(cx, item_schema, item)?
                        && cx.add_index(index))
                    {
                        return Ok(false);
                    }
                }
            }
            Items::Unsized(item_schema) => {
                let offset = keywords::prefix_items(schema).map_or(0, <[JsValue]>::len);
                for (index, item) in items.iter().enumerate().skip(offset) {
                    if !(self.check_schema_push_stack(cx, item_schema, item)?
                        && cx.add_index(index))
                    {
                        return Ok(false);
                    }
                }
            }
        }
        Ok(true)
    }

    /// `G.Counted(value, item => CheckSchema(contains, item) [&& AddIndex])`.
    pub(crate) fn count_contains(
        &mut self,
        cx: &mut CheckContext,
        contains: &'s JsValue,
        items: &[JsValue],
        add_index: bool,
    ) -> Result<f64, JsError> {
        let mut count = 0.0;
        for (index, item) in items.iter().enumerate() {
            if self.check_schema(cx, contains, item)? && (!add_index || cx.add_index(index)) {
                count += 1.0;
            }
        }
        Ok(count)
    }

    fn check_string(&mut self, schema: &'s JsValue, text: &str) -> CheckResult {
        if keywords::max_length(schema).is_some_and(|limit| !is_max_length(text, limit)) {
            return Ok(false);
        }
        if keywords::min_length(schema).is_some_and(|limit| !is_min_length(text, limit)) {
            return Ok(false);
        }
        if keywords::format(schema).is_some_and(|name| !format::test(name, text)) {
            return Ok(false);
        }
        if let Some(pattern) = keywords::pattern(schema) {
            if !self.regexps.unicode(pattern)?.test(text) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn check_unevaluated_items(
        &mut self,
        cx: &mut CheckContext,
        unevaluated: &'s JsValue,
        items: &[JsValue],
    ) -> CheckResult {
        let indices = cx.top();
        for (index, item) in items.iter().enumerate() {
            let evaluated = indices
                .as_ref()
                .is_some_and(|frame| frame.borrow().indices.contains(&index));
            if !((evaluated || self.check_schema(cx, unevaluated, item)?) && cx.add_index(index)) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn check_unevaluated_properties(
        &mut self,
        cx: &mut CheckContext,
        unevaluated: &'s JsValue,
        value: &JsValue,
    ) -> CheckResult {
        let keys = cx.top();
        for (key, property_value) in instance_entries(value) {
            let evaluated = keys
                .as_ref()
                .is_some_and(|frame| frame.borrow().keys.contains(key.as_ref()));
            if !(evaluated
                || (self.check_schema(cx, unevaluated, property_value)? && cx.add_key(&key)))
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

/// The number keywords (`exclusiveMaximum`, `exclusiveMinimum`, `maximum`,
/// `minimum`, `multipleOf`) for a finite number.
pub(crate) fn check_number(schema: &JsValue, number: f64) -> bool {
    keywords::exclusive_maximum(schema).is_none_or(|limit| number < limit)
        && keywords::exclusive_minimum(schema).is_none_or(|limit| number > limit)
        && keywords::maximum(schema).is_none_or(|limit| number <= limit)
        && keywords::minimum(schema).is_none_or(|limit| number >= limit)
        && keywords::multiple_of(schema).is_none_or(|divisor| is_multiple_of(number, divisor))
}
