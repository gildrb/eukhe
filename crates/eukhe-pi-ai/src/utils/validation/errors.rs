//! `TypeBox` `Errors` (`schema/engine/*` `Error*` functions, `schema/errors.mjs`)
//! with the `en_US` locale messages (`system/locale/en_US.mjs`).
//!
//! Every keyword is evaluated (`TypeBox` combines them with `&`, not `&&`), so
//! all failures are reported in keyword order, up to `maxErrors` (8) per
//! context; `allOf`/`anyOf`/`oneOf`/`$ref` operands collect into their own
//! contexts first.

use super::context::{ErrorContext, SchemaError};
use super::engine::{
    check_type, const_matches, hash, instance_entries, is_max_length, is_min_length,
    properties_pattern, property, ref_target, Engine, RefTarget,
};
use super::format;
use super::js_value::{usize_to_f64, JsError, JsObject, JsValue, TRUE_SCHEMA};
use super::keywords::{self, Items};
use super::resolve::Resolved;
use crate::utils::js::number_to_js_string;

type ErrorResult = Result<bool, JsError>;

fn error(keyword: &'static str, instance_path: &str, message: String) -> SchemaError {
    SchemaError {
        keyword,
        instance_path: instance_path.to_owned(),
        required_properties: Vec::new(),
        message,
    }
}

fn join_strings(items: &[JsValue]) -> String {
    keywords::strings(items).collect::<Vec<_>>().join(", ")
}

impl<'s> Engine<'_, 's> {
    /// `ErrorSchema(stack, context, schemaPath, instancePath, schema, value)`.
    pub(crate) fn error_schema(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        schema: &'s JsValue,
        value: &JsValue,
    ) -> ErrorResult {
        if cx.at_capacity() {
            return Ok(false);
        }
        self.enter()?;
        self.stack.push(schema);
        let result = self.error_keywords(cx, path, schema, value);
        self.stack.pop(schema);
        self.leave();
        result
    }

    /// `ErrorSchemaPushStack`: the frame stays pushed when the schema fails.
    fn error_schema_push_stack(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        schema: &'s JsValue,
        value: &JsValue,
    ) -> ErrorResult {
        Ok(cx.check.push() && self.error_schema(cx, path, schema, value)? && cx.check.pop())
    }

    #[allow(clippy::too_many_lines)] // One branch per keyword, in TypeBox's order.
    fn error_keywords(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        schema: &'s JsValue,
        value: &JsValue,
    ) -> ErrorResult {
        if let JsValue::Bool(flag) = schema {
            return Ok(*flag || cx.add_error(error("boolean", path, "schema is false".to_owned())));
        }
        let mut ok = true;
        if let Some(type_) = keywords::type_(schema) {
            let message = match type_ {
                JsValue::String(name) => format!("must be {name}"),
                JsValue::Array(names) => format!(
                    "must be either {}",
                    keywords::strings(names).collect::<Vec<_>>().join(" or ")
                ),
                JsValue::Null
                | JsValue::Bool(_)
                | JsValue::Number(_)
                | JsValue::Object(_)
                | JsValue::Function(_) => String::new(),
            };
            ok &= check_type(type_, value) || cx.add_error(error("type", path, message));
        }
        if let JsValue::Object(object) = value {
            ok &= self.error_object(cx, path, schema, value, object)?;
        }
        if let JsValue::Array(items) = value {
            ok &= self.error_array(cx, path, schema, items)?;
        }
        if let JsValue::String(text) = value {
            ok &= self.error_string(cx, path, schema, text)?;
        }
        if let JsValue::Number(number) = value {
            if number.is_finite() {
                ok &= error_number(cx, path, schema, *number);
            }
        }
        if let Some(reference) = keywords::ref_(schema) {
            let target = self.stack.resolve_ref(reference)?;
            ok &= self.error_ref(cx, path, target, value)?;
        }
        if let Some(reference) = keywords::recursive_ref(schema) {
            let target = self.stack.resolve_recursive_ref(reference)?;
            ok &= self.error_scoped_ref(cx, path, target, value)?;
        }
        if let Some(reference) = keywords::dynamic_ref(schema) {
            let target = self.stack.resolve_dynamic_ref(reference)?;
            ok &= self.error_scoped_ref(cx, path, target, value)?;
        }
        if let Some(constant) = keywords::const_(schema) {
            ok &= const_matches(value, constant)
                || cx.add_error(error("const", path, "must be equal to constant".to_owned()));
        }
        if let Some(options) = keywords::enum_(schema) {
            ok &= options.iter().any(|option| const_matches(value, option))
                || cx.add_error(error(
                    "enum",
                    path,
                    "must be equal to one of the allowed values".to_owned(),
                ));
        }
        if let Some(condition) = keywords::if_(schema) {
            ok &= self.error_if(cx, path, schema, condition, value)?;
        }
        if let Some(negated) = keywords::not(schema) {
            ok &= self.check_not(&mut cx.check, negated, value)?
                || cx.add_error(error("not", path, "must not be valid".to_owned()));
        }
        if let Some(schemas) = keywords::all_of(schema) {
            let (passed, failed) = self.error_each(path, schemas, value)?;
            let is_all_of =
                failed.is_empty() && cx.check.merge(passed.iter().map(|context| &context.check));
            if !is_all_of {
                add_errors(cx, failed);
            }
            ok &= is_all_of;
        }
        if let Some(schemas) = keywords::any_of(schema) {
            let (passed, failed) = self.error_each(path, schemas, value)?;
            let is_any_of =
                !passed.is_empty() && cx.check.merge(passed.iter().map(|context| &context.check));
            if !is_any_of {
                add_errors(cx, failed);
            }
            ok &= is_any_of
                || cx.add_error(error(
                    "anyOf",
                    path,
                    "must match a schema in anyOf".to_owned(),
                ));
        }
        if let Some(schemas) = keywords::one_of(schema) {
            let (passed, failed) = self.error_each(path, schemas, value)?;
            let is_one_of =
                passed.len() == 1 && cx.check.merge(passed.iter().map(|context| &context.check));
            if !is_one_of && passed.is_empty() {
                add_errors(cx, failed);
            }
            ok &= is_one_of
                || cx.add_error(error(
                    "oneOf",
                    path,
                    "must match exactly one schema in oneOf".to_owned(),
                ));
        }
        if let (Some(unevaluated), JsValue::Array(items)) =
            (keywords::unevaluated_items(schema), value)
        {
            ok &= self.error_unevaluated_items(cx, path, unevaluated, items)?;
        }
        if let Some(unevaluated) =
            keywords::unevaluated_properties(schema).filter(|_| value.is_object())
        {
            ok &= self.error_unevaluated_properties(cx, path, unevaluated, value)?;
        }
        Ok(ok)
    }

    /// Runs each operand into its own error context: (passed, failed).
    fn error_each(
        &mut self,
        path: &str,
        schemas: &'s [JsValue],
        value: &JsValue,
    ) -> Result<(Vec<ErrorContext>, Vec<ErrorContext>), JsError> {
        let mut passed = Vec::new();
        let mut failed = Vec::new();
        for schema in schemas {
            let mut next = ErrorContext::new();
            if self.error_schema(&mut next, path, schema, value)? {
                passed.push(next);
            } else {
                failed.push(next);
            }
        }
        Ok((passed, failed))
    }

    fn error_if(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        schema: &'s JsValue,
        condition: &'s JsValue,
        value: &JsValue,
    ) -> ErrorResult {
        let then_schema = keywords::then(schema).unwrap_or(&TRUE_SCHEMA);
        let else_schema = keywords::else_(schema).unwrap_or(&TRUE_SCHEMA);
        let mut true_context = ErrorContext::new();
        let is_if = if self.error_schema(&mut true_context, path, condition, value)? {
            self.error_schema(&mut true_context, path, then_schema, value)?
                || cx.add_error(error("if", path, "must match \"then\" schema".to_owned()))
        } else {
            self.error_schema(cx, path, else_schema, value)?
                || cx.add_error(error("if", path, "must match \"else\" schema".to_owned()))
        };
        if is_if {
            cx.check.merge([&true_context.check]);
        }
        Ok(is_if)
    }

    /// `ErrorRef`: errors surface from a fresh context; the schema path restarts at `#`.
    fn error_ref(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        target: Option<Resolved<'s>>,
        value: &JsValue,
    ) -> ErrorResult {
        let mut next = ErrorContext::new();
        let result = match ref_target(target) {
            RefTarget::Schema(target) => self.error_schema(&mut next, path, target, value)?,
            RefTarget::Keywordless | RefTarget::Primitive(_) => false,
        };
        if result {
            cx.check.merge([&next.check]);
        } else {
            add_errors(cx, vec![next]);
        }
        Ok(result)
    }

    /// `ErrorRecursiveRef` / `ErrorDynamicRef`: the target reports into this context.
    fn error_scoped_ref(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        target: Option<Resolved<'s>>,
        value: &JsValue,
    ) -> ErrorResult {
        match ref_target(target) {
            RefTarget::Schema(target) => self.error_schema(cx, path, target, value),
            RefTarget::Keywordless | RefTarget::Primitive(_) => Ok(false),
        }
    }

    #[allow(clippy::too_many_lines)] // One branch per object keyword, in TypeBox's order.
    fn error_object(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        schema: &'s JsValue,
        value: &JsValue,
        object: &JsObject,
    ) -> ErrorResult {
        let mut ok = true;
        if let Some(required) = keywords::required(schema) {
            let missing: Vec<String> = keywords::strings(required)
                .filter(|key| !object.has_property_key(key))
                .map(str::to_owned)
                .collect();
            if !missing.is_empty() {
                let message = format!("must have required properties {}", missing.join(", "));
                cx.add_error(SchemaError {
                    keyword: "required",
                    instance_path: path.to_owned(),
                    required_properties: missing,
                    message,
                });
                ok = false;
            }
        }
        if let Some(additional) = keywords::additional_properties(schema) {
            let regexp = self.regexps.unicode(&properties_pattern(schema))?;
            let mut additional_keys = false;
            for (key, property_value) in object.entries() {
                let is_additional_property = regexp.test(key)
                    || (self.error_schema_push_stack(
                        cx,
                        &format!("{path}/{key}"),
                        additional,
                        property_value,
                    )? && cx.check.add_key(key));
                additional_keys |= !is_additional_property;
            }
            if additional_keys {
                ok &= cx.add_error(error(
                    "additionalProperties",
                    path,
                    "must not have additional properties".to_owned(),
                ));
            }
        }
        if let Some(dependencies) = keywords::dependencies(schema) {
            let is_length = object.len() == 0;
            let mut is_every = true;
            for (key, dependency) in dependencies.entries() {
                let satisfied = !object.has_property_key(&key)
                    || match dependency {
                        JsValue::Array(keys) => {
                            let message = format!(
                                "must have properties {} when property {key} is present",
                                join_strings(keys)
                            );
                            keywords::strings(keys).all(|dependency| {
                                object.has_property_key(dependency)
                                    || cx.add_error(error("dependencies", path, message.clone()))
                            })
                        }
                        _ => self.error_schema(cx, path, dependency, value)?,
                    };
                is_every &= satisfied;
            }
            ok &= is_length || is_every;
        }
        if let Some(dependent) = keywords::dependent_required(schema) {
            let is_length = object.len() == 0;
            let mut is_every = true;
            for (key, keys) in dependent.entries() {
                if !object.has_property_key(&key) {
                    continue;
                }
                if let JsValue::Array(keys) = keys {
                    let message = format!(
                        "must have properties {} when property {key} is present",
                        join_strings(keys)
                    );
                    for dependency in keywords::strings(keys) {
                        if !object.has_property_key(dependency) {
                            is_every &=
                                cx.add_error(error("dependentRequired", path, message.clone()));
                        }
                    }
                }
            }
            ok &= is_length || is_every;
        }
        if let Some(dependent) = keywords::dependent_schemas(schema) {
            let is_length = object.len() == 0;
            let mut is_every = true;
            for (key, dependency) in dependent.entries() {
                if object.has_property_key(&key) {
                    is_every &= self.error_schema(cx, path, dependency, value)?;
                }
            }
            ok &= is_length || is_every;
        }
        if let Some(pattern_properties) = keywords::pattern_properties(schema) {
            for (pattern, property_schema) in pattern_properties.entries() {
                let regexp = self.regexps.unicode(&pattern)?;
                for (key, property_value) in object.entries() {
                    if regexp.test(key) {
                        ok &= self.error_schema_push_stack(
                            cx,
                            &format!("{path}/{key}"),
                            property_schema,
                            property_value,
                        )? && cx.check.add_key(key);
                    }
                }
            }
        }
        if let Some(properties) = keywords::properties(schema) {
            for (key, property_schema) in properties.entries() {
                if object.has_property_key(&key) {
                    let property_value = property(object, &key);
                    ok &= self.error_schema_push_stack(
                        cx,
                        &format!("{path}/{key}"),
                        property_schema,
                        &property_value,
                    )? && cx.check.add_key(&key);
                }
            }
        }
        if let Some(names) = keywords::property_names(schema) {
            let mut invalid: Vec<&str> = Vec::new();
            for key in object.keys() {
                if !self.error_schema(
                    cx,
                    &format!("{path}/{key}"),
                    names,
                    &JsValue::String(key.to_owned()),
                )? {
                    invalid.push(key);
                }
            }
            if !invalid.is_empty() {
                ok &= cx.add_error(error(
                    "propertyNames",
                    path,
                    format!("property names {} are invalid", invalid.join(", ")),
                ));
            }
        }
        if let Some(limit) = keywords::min_properties(schema) {
            ok &= usize_to_f64(object.len()) >= limit
                || cx.add_error(error(
                    "minProperties",
                    path,
                    format!(
                        "must not have fewer than {} properties",
                        number_to_js_string(limit)
                    ),
                ));
        }
        if let Some(limit) = keywords::max_properties(schema) {
            ok &= usize_to_f64(object.len()) <= limit
                || cx.add_error(error(
                    "maxProperties",
                    path,
                    format!(
                        "must not have more than {} properties",
                        number_to_js_string(limit)
                    ),
                ));
        }
        Ok(ok)
    }

    #[allow(clippy::too_many_lines)] // One branch per array keyword, in TypeBox's order.
    fn error_array(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        schema: &'s JsValue,
        items: &[JsValue],
    ) -> ErrorResult {
        let contains_message = || "must contain at least 1 valid item".to_owned();
        let mut ok = true;
        if let (Some(additional), Some(Items::Sized(tuple))) =
            (keywords::additional_items(schema), keywords::items(schema))
        {
            // `G.Every`: stops at the first failing additional item.
            for (index, item) in items.iter().enumerate().skip(tuple.len()) {
                if !(self.error_schema_push_stack(
                    cx,
                    &format!("{path}/{index}"),
                    additional,
                    item,
                )? && cx.check.add_index(index))
                {
                    ok = false;
                    break;
                }
            }
        }
        if let Some(contains) = keywords::contains(schema) {
            if keywords::min_contains(schema) != Some(0.0) {
                let mut found = false;
                for (index, item) in items.iter().enumerate() {
                    if self.check_schema(&mut cx.check, contains, item)?
                        && cx.check.add_index(index)
                    {
                        found = true;
                    }
                }
                ok &= (!items.is_empty() && found)
                    || cx.add_error(error("contains", path, contains_message()));
            }
        }
        if let Some(item_schemas) = keywords::items(schema) {
            match item_schemas {
                Items::Sized(tuple) => {
                    for (index, (item_schema, item)) in tuple.iter().zip(items).enumerate() {
                        ok &= self.error_schema_push_stack(
                            cx,
                            &format!("{path}/{index}"),
                            item_schema,
                            item,
                        )? && cx.check.add_index(index);
                    }
                }
                Items::Unsized(item_schema) => {
                    let offset = keywords::prefix_items(schema).map_or(0, <[JsValue]>::len);
                    for (index, item) in items.iter().enumerate().skip(offset) {
                        ok &= self.error_schema_push_stack(
                            cx,
                            &format!("{path}/{index}"),
                            item_schema,
                            item,
                        )? && cx.check.add_index(index);
                    }
                }
            }
        }
        if let (Some(limit), Some(contains)) =
            (keywords::max_contains(schema), keywords::contains(schema))
        {
            ok &= self.count_contains(&mut cx.check, contains, items, /*add_index*/ false)?
                <= limit
                || cx.add_error(error("contains", path, contains_message()));
        }
        if let Some(limit) = keywords::max_items(schema) {
            ok &= usize_to_f64(items.len()) <= limit
                || cx.add_error(error(
                    "maxItems",
                    path,
                    format!(
                        "must not have more than {} items",
                        number_to_js_string(limit)
                    ),
                ));
        }
        if let (Some(limit), Some(contains)) =
            (keywords::min_contains(schema), keywords::contains(schema))
        {
            ok &= self.count_contains(&mut cx.check, contains, items, /*add_index*/ true)? >= limit
                || cx.add_error(error("contains", path, contains_message()));
        }
        if let Some(limit) = keywords::min_items(schema) {
            ok &= usize_to_f64(items.len()) >= limit
                || cx.add_error(error(
                    "minItems",
                    path,
                    format!(
                        "must not have fewer than {} items",
                        number_to_js_string(limit)
                    ),
                ));
        }
        if let Some(prefix) = keywords::prefix_items(schema) {
            if !items.is_empty() {
                for (index, (prefix_schema, item)) in prefix.iter().zip(items).enumerate() {
                    ok &= self.error_schema_push_stack(
                        cx,
                        &format!("{path}/{index}"),
                        prefix_schema,
                        item,
                    )? && cx.check.add_index(index);
                }
            }
        }
        if keywords::unique_items(schema) == Some(true) {
            let mut seen = std::collections::HashSet::new();
            let unique = items.iter().all(|item| seen.insert(hash(item)));
            ok &= unique
                || cx.add_error(error(
                    "uniqueItems",
                    path,
                    "must not have duplicate items".to_owned(),
                ));
        }
        Ok(ok)
    }

    fn error_string(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        schema: &'s JsValue,
        text: &str,
    ) -> ErrorResult {
        let mut ok = true;
        if let Some(limit) = keywords::max_length(schema) {
            ok &= is_max_length(text, limit)
                || cx.add_error(error(
                    "maxLength",
                    path,
                    format!(
                        "must not have more than {} characters",
                        number_to_js_string(limit)
                    ),
                ));
        }
        if let Some(limit) = keywords::min_length(schema) {
            ok &= is_min_length(text, limit)
                || cx.add_error(error(
                    "minLength",
                    path,
                    format!(
                        "must not have fewer than {} characters",
                        number_to_js_string(limit)
                    ),
                ));
        }
        if let Some(name) = keywords::format(schema) {
            ok &= format::test(name, text)
                || cx.add_error(error(
                    "format",
                    path,
                    format!("must match format \"{name}\""),
                ));
        }
        if let Some(pattern) = keywords::pattern(schema) {
            ok &= self.regexps.unicode(pattern)?.test(text)
                || cx.add_error(error(
                    "pattern",
                    path,
                    format!("must match pattern \"{pattern}\""),
                ));
        }
        Ok(ok)
    }

    fn error_unevaluated_items(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        unevaluated: &'s JsValue,
        items: &[JsValue],
    ) -> ErrorResult {
        let indices = cx.check.top();
        let mut all_evaluated = true;
        for (index, item) in items.iter().enumerate() {
            let evaluated = indices
                .as_ref()
                .is_some_and(|frame| frame.borrow().indices.contains(&index));
            let mut next = ErrorContext::new();
            all_evaluated &= (evaluated
                || self.error_schema(&mut next, path, unevaluated, item)?)
                && cx.check.add_index(index);
        }
        Ok(all_evaluated
            || cx.add_error(error(
                "unevaluatedItems",
                path,
                "must not have unevaluated items".to_owned(),
            )))
    }

    fn error_unevaluated_properties(
        &mut self,
        cx: &mut ErrorContext,
        path: &str,
        unevaluated: &'s JsValue,
        value: &JsValue,
    ) -> ErrorResult {
        let keys = cx.check.top();
        let mut all_evaluated = true;
        for (key, property_value) in instance_entries(value) {
            let evaluated = keys
                .as_ref()
                .is_some_and(|frame| frame.borrow().keys.contains(key.as_ref()));
            let mut next = ErrorContext::new();
            all_evaluated &= evaluated
                || (self.error_schema(&mut next, path, unevaluated, property_value)?
                    && cx.check.add_key(&key));
        }
        Ok(all_evaluated
            || cx.add_error(error(
                "unevaluatedProperties",
                path,
                "must not have unevaluated properties".to_owned(),
            )))
    }
}

/// Re-adds the errors of failed operand contexts (`failed.GetErrors().forEach(AddError)`).
fn add_errors(cx: &mut ErrorContext, failed: Vec<ErrorContext>) {
    for context in failed {
        for schema_error in context.into_errors() {
            cx.add_error(schema_error);
        }
    }
}

fn error_number(cx: &mut ErrorContext, path: &str, schema: &JsValue, number: f64) -> bool {
    let mut ok = true;
    let mut compare = |keyword: &'static str,
                       limit: Option<f64>,
                       comparison: &str,
                       passes: fn(f64, f64) -> bool| {
        if let Some(limit) = limit {
            ok &= passes(number, limit)
                || cx.add_error(error(
                    keyword,
                    path,
                    format!("must be {comparison} {}", number_to_js_string(limit)),
                ));
        }
    };
    compare(
        "exclusiveMaximum",
        keywords::exclusive_maximum(schema),
        "<",
        |value, limit| value < limit,
    );
    compare(
        "exclusiveMinimum",
        keywords::exclusive_minimum(schema),
        ">",
        |value, limit| value > limit,
    );
    compare(
        "maximum",
        keywords::maximum(schema),
        "<=",
        |value, limit| value <= limit,
    );
    compare(
        "minimum",
        keywords::minimum(schema),
        ">=",
        |value, limit| value >= limit,
    );
    if let Some(divisor) = keywords::multiple_of(schema) {
        ok &= super::engine::is_multiple_of(number, divisor)
            || cx.add_error(error(
                "multipleOf",
                path,
                format!("must be multiple of {}", number_to_js_string(divisor)),
            ));
    }
    ok
}
