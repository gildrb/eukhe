//! `TypeBox` `Compile(schema)` (`compile/validator.mjs`, `schema/build.mjs`).
//!
//! Compilation walks the schema the way `Build` does — every keyword, every
//! `$ref` target once per lexical base — so it throws exactly where `TypeBox`'s
//! code generation throws (invalid `pattern`/`patternProperties` regexps,
//! invalid URLs, malformed `$ref` fragments, primitive `$ref` targets). Checks
//! then run on the evaluation engine with the compiled checker's semantics.

use super::context::{CheckContext, ErrorContext, SchemaError};
use super::engine::{
    can_additional_properties_fast, in_operator_error, properties_pattern, ref_target, Engine,
    Mode, RefTarget,
};
use super::js_value::{JsError, JsValue, TRUE_SCHEMA};
use super::keywords::{self, Items};
use super::regexp::RegExpCache;
use super::resolve::Resolved;
use super::stack::Stack;

/// A compiled `TypeBox` validator for one schema.
pub(crate) struct Validator<'s> {
    schema: &'s JsValue,
    regexps: RegExpCache,
}

impl<'s> Validator<'s> {
    /// `Compile(schema)`.
    pub(crate) fn compile(schema: &'s JsValue) -> Result<Self, JsError> {
        let validator = Self {
            schema,
            regexps: RegExpCache::default(),
        };
        let mut builder = Builder {
            regexps: &validator.regexps,
            stack: Stack::new(schema),
            use_unevaluated: has_unevaluated(schema),
            functions: Vec::new(),
            depth: 0,
        };
        builder.create_function(RefTarget::Schema(schema))?;
        Ok(validator)
    }

    /// `Validator.Check(value)`.
    pub(crate) fn check(&self, value: &JsValue) -> Result<bool, JsError> {
        let mut engine = Engine::new(self.schema, &self.regexps, Mode::Compiled);
        engine.check_schema(&mut CheckContext::new(), self.schema, value)
    }

    /// `Validator.Errors(value)`: empty for a passing value, else the
    /// interpreted `Errors` output.
    pub(crate) fn errors(&self, value: &JsValue) -> Result<Vec<SchemaError>, JsError> {
        if self.check(value)? {
            return Ok(Vec::new());
        }
        let mut engine = Engine::new(self.schema, &self.regexps, Mode::Interpreted);
        let mut context = ErrorContext::new();
        engine.error_schema(&mut context, "", self.schema, value)?;
        Ok(context.into_errors())
    }
}

/// `HasUnevaluated`: any `unevaluatedItems`/`unevaluatedProperties` keyword
/// anywhere in the document.
fn has_unevaluated(value: &JsValue) -> bool {
    match value {
        JsValue::Array(items) => items.iter().any(has_unevaluated),
        JsValue::Object(object) => {
            keywords::unevaluated_items(value).is_some()
                || keywords::unevaluated_properties(value).is_some()
                || object
                    .entries()
                    .into_iter()
                    .any(|(_, value)| has_unevaluated(value))
        }
        JsValue::Null
        | JsValue::Bool(_)
        | JsValue::Number(_)
        | JsValue::String(_)
        | JsValue::Function(_) => false,
    }
}

/// The `Build` traversal.
struct Builder<'v, 's> {
    regexps: &'v RegExpCache,
    stack: Stack<'s>,
    use_unevaluated: bool,
    /// `CreateFunction` memo: (schema identity, lexical base).
    functions: Vec<(*const JsValue, String)>,
    depth: usize,
}

/// Nesting limit standing in for V8's call stack during code generation.
const MAX_BUILD_DEPTH: usize = 512;

impl<'s> Builder<'_, 's> {
    /// `CreateFunction(stack, context, schema, value)`.
    fn create_function(&mut self, target: RefTarget<'s>) -> Result<(), JsError> {
        let base = self.stack.lexical_base_url()?;
        match target {
            RefTarget::Schema(schema) => {
                let key = (std::ptr::from_ref(schema), base);
                if self.functions.contains(&key) {
                    return Ok(());
                }
                self.functions.push(key);
                self.build_schema(schema)
            }
            // Arrays and functions build to `true`.
            RefTarget::Keywordless => Ok(()),
            RefTarget::Primitive(error) => Err(error),
        }
    }

    fn build_ref(&mut self, resolved: Option<Resolved<'s>>) -> Result<(), JsError> {
        self.create_function(ref_target(resolved))
    }

    /// `BuildSchema(stack, context, schema, value)`.
    fn build_schema(&mut self, schema: &'s JsValue) -> Result<(), JsError> {
        self.depth += 1;
        if self.depth > MAX_BUILD_DEPTH {
            return Err(JsError::stack_overflow());
        }
        self.stack.push(schema);
        let result = self.build_keywords(schema);
        self.stack.pop(schema);
        self.depth -= 1;
        result
    }

    fn build_keywords(&mut self, schema: &'s JsValue) -> Result<(), JsError> {
        match schema {
            JsValue::Object(_) => {}
            JsValue::Bool(_) | JsValue::Array(_) | JsValue::Function(_) => return Ok(()),
            JsValue::Null | JsValue::Number(_) | JsValue::String(_) => {
                return Err(in_operator_error(schema))
            }
        }
        if let Some(additional) = keywords::additional_properties(schema) {
            let ignored = !self.use_unevaluated
                && match additional {
                    JsValue::Bool(flag) => *flag,
                    JsValue::Object(object) => object.len() == 0,
                    _ => false,
                };
            if !ignored && can_additional_properties_fast(schema).is_none() {
                self.regexps.unicode(&properties_pattern(schema))?;
                self.build_schema(additional)?;
            }
        }
        if let Some(dependencies) = keywords::dependencies(schema) {
            for (_, dependency) in dependencies.entries() {
                self.build_schema(dependency)?;
            }
        }
        if let Some(dependent) = keywords::dependent_schemas(schema) {
            for (_, dependency) in dependent.entries() {
                self.build_schema(dependency)?;
            }
        }
        if let Some(pattern_properties) = keywords::pattern_properties(schema) {
            for (pattern, property_schema) in pattern_properties.entries() {
                self.regexps.unicode(&pattern)?;
                self.build_schema(property_schema)?;
            }
        }
        if let Some(properties) = keywords::properties(schema) {
            for (_, property_schema) in properties.entries() {
                self.build_schema(property_schema)?;
            }
        }
        if let Some(names) = keywords::property_names(schema) {
            self.build_schema(names)?;
        }
        self.build_array_keywords(schema)?;
        if let Some(pattern) = keywords::pattern(schema) {
            self.regexps.unicode(pattern)?;
        }
        if let Some(reference) = keywords::ref_(schema) {
            let resolved = self.stack.resolve_ref(reference)?;
            self.build_ref(resolved)?;
        }
        if let Some(reference) = keywords::recursive_ref(schema) {
            let resolved = self.stack.resolve_recursive_ref(reference)?;
            self.build_ref(resolved)?;
        }
        if let Some(reference) = keywords::dynamic_ref(schema) {
            let resolved = self.stack.resolve_dynamic_ref(reference)?;
            self.build_ref(resolved)?;
        }
        if let Some(condition) = keywords::if_(schema) {
            self.build_schema(condition)?;
            self.build_schema(keywords::then(schema).unwrap_or(&TRUE_SCHEMA))?;
            self.build_schema(keywords::else_(schema).unwrap_or(&TRUE_SCHEMA))?;
        }
        if let Some(negated) = keywords::not(schema) {
            self.build_schema(negated)?;
        }
        for schemas in [
            keywords::all_of(schema),
            keywords::any_of(schema),
            keywords::one_of(schema),
        ]
        .into_iter()
        .flatten()
        {
            for operand in schemas {
                self.build_schema(operand)?;
            }
        }
        if let Some(unevaluated) = keywords::unevaluated_items(schema) {
            self.build_schema(unevaluated)?;
        }
        if let Some(unevaluated) = keywords::unevaluated_properties(schema) {
            self.build_schema(unevaluated)?;
        }
        Ok(())
    }

    fn build_array_keywords(&mut self, schema: &'s JsValue) -> Result<(), JsError> {
        let item_schemas = keywords::items(schema);
        if let (Some(additional), Some(Items::Sized(_))) =
            (keywords::additional_items(schema), &item_schemas)
        {
            self.build_schema(additional)?;
        }
        let contains = keywords::contains(schema);
        if let Some(contains) = contains.filter(|_| keywords::min_contains(schema) != Some(0.0)) {
            self.build_schema(contains)?;
        }
        match item_schemas {
            Some(Items::Sized(tuple)) => {
                for item_schema in tuple {
                    self.build_schema(item_schema)?;
                }
            }
            Some(Items::Unsized(item_schema)) => self.build_schema(item_schema)?,
            None => {}
        }
        if let (Some(contains), Some(_)) = (contains, keywords::max_contains(schema)) {
            self.build_schema(contains)?;
        }
        if let (Some(contains), Some(_)) = (contains, keywords::min_contains(schema)) {
            self.build_schema(contains)?;
        }
        if let Some(prefix) = keywords::prefix_items(schema) {
            for prefix_schema in prefix {
                self.build_schema(prefix_schema)?;
            }
        }
        Ok(())
    }
}
