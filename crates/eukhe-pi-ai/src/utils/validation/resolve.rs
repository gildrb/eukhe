//! `TypeBox` `$ref` / `$recursiveRef` / `$dynamicRef` resolution
//! (`schema/resolve`, `schema/pointer`), with WHATWG URL semantics.
//!
//! The validator context is always empty (`Compile(schema)`), so remote
//! lookups never succeed; the only context hits are `Object.prototype` member
//! names, which resolve to a function.

use url::Url;

use super::js_value::{
    decode_uri_component, is_unsafe_property_key, usize_to_f64, JsError, JsValue, NativeFunction,
};
use super::keywords;
use crate::utils::js::array_index_key;

/// `Resolve.DefaultBase`.
pub(crate) const DEFAULT_BASE: &str = "https://json-schema.org";

/// A value a reference can resolve to.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Resolved<'s> {
    /// A value inside the schema document.
    Value(&'s JsValue),
    /// A native function (an inherited member reached by name).
    Function,
    /// An array `length` reached by a JSON pointer.
    Number(f64),
}

impl<'s> Resolved<'s> {
    /// `value ?? fallback` treats `null` as absent.
    fn non_nullish(self) -> Option<Self> {
        match self {
            Self::Value(JsValue::Null) => None,
            Self::Value(_) | Self::Function | Self::Number(_) => Some(self),
        }
    }

    /// The schema object, when this is one (`Schema.IsSchemaObject`).
    pub(crate) fn schema_object(self) -> Option<&'s JsValue> {
        match self {
            Self::Value(value @ JsValue::Object(_)) => Some(value),
            Self::Value(_) | Self::Function | Self::Number(_) => None,
        }
    }

    /// JS truthiness (`!schema` in `ResolveRef`).
    fn is_truthy(self) -> bool {
        match self {
            Self::Value(value) => value.is_truthy(),
            Self::Function => true,
            Self::Number(number) => number != 0.0 && !number.is_nan(),
        }
    }
}

/// `new URL(input, base)`.
pub(crate) fn new_url(input: &str, base: &str) -> Result<Url, JsError> {
    Url::parse(base)
        .and_then(|base| base.join(input))
        .map_err(|_| JsError::invalid_url())
}

/// `url.hash`: empty for no or an empty fragment, else `#fragment`.
fn url_hash(url: &Url) -> String {
    match url.fragment() {
        Some(fragment) if !fragment.is_empty() => format!("#{fragment}"),
        Some(_) | None => String::new(),
    }
}

/// `new URL(base || '.', DefaultBase)`.
fn initial_base(base: &str) -> Result<Url, JsError> {
    new_url(if base.is_empty() { "." } else { base }, DEFAULT_BASE)
}

// ------------------------------------------------------------------
// Pointer
// ------------------------------------------------------------------

/// `Pointer.Indices(pointer)`.
fn pointer_indices(pointer: &str) -> Vec<String> {
    if pointer.is_empty() {
        return Vec::new();
    }
    let mut indices: Vec<String> = pointer
        .split('/')
        .map(|index| index.replace("~1", "/").replace("~0", "~"))
        .collect();
    if indices.first().is_some_and(String::is_empty) {
        indices.remove(0);
    }
    indices
}

/// `Array.prototype` members other than `length` and `constructor`.
const ARRAY_METHODS: [&str; 38] = [
    "at",
    "concat",
    "copyWithin",
    "fill",
    "find",
    "findIndex",
    "findLast",
    "findLastIndex",
    "lastIndexOf",
    "pop",
    "push",
    "reverse",
    "shift",
    "unshift",
    "slice",
    "sort",
    "splice",
    "includes",
    "indexOf",
    "join",
    "keys",
    "entries",
    "values",
    "forEach",
    "filter",
    "flat",
    "flatMap",
    "map",
    "every",
    "some",
    "reduce",
    "reduceRight",
    "toReversed",
    "toSorted",
    "toSpliced",
    "with",
    "toLocaleString",
    "toString",
];

/// `GetIndex(index, value)`: a property read on an object or array.
fn pointer_index<'s>(index: &str, value: Resolved<'s>) -> Option<Resolved<'s>> {
    if is_unsafe_property_key(index) {
        return None;
    }
    match value {
        Resolved::Value(JsValue::Object(object)) => match object.get_own(index) {
            Some(found) => Some(Resolved::Value(found)),
            None => NativeFunction::inherited(index).map(|_| Resolved::Function),
        },
        Resolved::Value(JsValue::Array(items)) => {
            if index == "length" {
                return Some(Resolved::Number(usize_to_f64(items.len())));
            }
            if let Some(position) = array_index_key(index) {
                return usize::try_from(position)
                    .ok()
                    .and_then(|position| items.get(position))
                    .map(Resolved::Value);
            }
            (ARRAY_METHODS.contains(&index) || NativeFunction::inherited(index).is_some())
                .then_some(Resolved::Function)
        }
        Resolved::Value(_) | Resolved::Function | Resolved::Number(_) => None,
    }
}

/// `Pointer.Get(value, pointer)`.
fn pointer_get<'s>(value: &'s JsValue, pointer: &str) -> Option<Resolved<'s>> {
    pointer_indices(pointer)
        .iter()
        .try_fold(Resolved::Value(value), |current, index| {
            pointer_index(index, current)
        })
}

// ------------------------------------------------------------------
// Matching
// ------------------------------------------------------------------

fn find_dynamic_anchor<'s>(schema: &'s JsValue, name: &str) -> Option<&'s JsValue> {
    if schema.is_object() && keywords::dynamic_anchor(schema) == Some(name) {
        return Some(schema);
    }
    match schema {
        JsValue::Object(object) => object
            .entries()
            .into_iter()
            .find_map(|(_, value)| find_dynamic_anchor(value, name)),
        JsValue::Array(items) => items
            .iter()
            .find_map(|item| find_dynamic_anchor(item, name)),
        JsValue::Null
        | JsValue::Bool(_)
        | JsValue::Number(_)
        | JsValue::String(_)
        | JsValue::Function(_) => None,
    }
}

fn find_base(schema: &JsValue, base: &Url, target: &JsValue) -> Result<Option<String>, JsError> {
    if std::ptr::eq(schema, target) {
        return Ok(Some(base.as_str().to_owned()));
    }
    let next_base = match keywords::id(schema) {
        Some(id) => new_url(id, base.as_str())?,
        None => base.clone(),
    };
    match schema {
        JsValue::Array(items) => {
            for item in items {
                if let Some(found) = find_base(item, &next_base, target)? {
                    return Ok(Some(found));
                }
            }
            Ok(None)
        }
        JsValue::Object(object) => {
            for (_, value) in object.entries() {
                if let Some(found) = find_base(value, &next_base, target)? {
                    return Ok(Some(found));
                }
            }
            Ok(None)
        }
        JsValue::Null
        | JsValue::Bool(_)
        | JsValue::Number(_)
        | JsValue::String(_)
        | JsValue::Function(_) => Ok(None),
    }
}

fn match_id<'s>(
    schema: &'s JsValue,
    id: &str,
    base: &Url,
    reference: &Url,
) -> Result<Option<Resolved<'s>>, JsError> {
    let hash = url_hash(reference);
    if id == hash {
        return Ok(Some(Resolved::Value(schema)));
    }
    let absolute = new_url(reference.as_str(), base.as_str())?;
    if base.path() == absolute.path() {
        return if hash.starts_with('#') {
            match_hash(schema, reference)
        } else {
            Ok(Some(Resolved::Value(schema)))
        };
    }
    Ok(None)
}

fn match_anchor<'s>(
    schema: &'s JsValue,
    anchor: &str,
    base: &Url,
    reference: &Url,
) -> Result<Option<Resolved<'s>>, JsError> {
    let absolute_anchor = new_url(&format!("#{anchor}"), base.as_str())?;
    let absolute_reference = new_url(reference.as_str(), base.as_str())?;
    Ok(
        (absolute_anchor.as_str() == absolute_reference.as_str())
            .then_some(Resolved::Value(schema)),
    )
}

fn match_hash<'s>(schema: &'s JsValue, reference: &Url) -> Result<Option<Resolved<'s>>, JsError> {
    if reference.as_str().ends_with('#') {
        return Ok(Some(Resolved::Value(schema)));
    }
    let hash = url_hash(reference);
    let Some(fragment) = hash.strip_prefix('#') else {
        return Ok(None);
    };
    let fragment = decode_uri_component(fragment)?;
    if !fragment.starts_with('/') {
        return Ok(None);
    }
    Ok(pointer_get(schema, &fragment))
}

fn match_schema<'s>(
    schema: &'s JsValue,
    base: &Url,
    reference: &Url,
) -> Result<Option<Resolved<'s>>, JsError> {
    if let Some(id) = keywords::id(schema) {
        if let Some(found) = match_id(schema, id, base, reference)? {
            return Ok(Some(found));
        }
    }
    if let Some(anchor) = keywords::anchor(schema) {
        if let Some(found) = match_anchor(schema, anchor, base, reference)? {
            return Ok(Some(found));
        }
    }
    if let Some(anchor) = keywords::dynamic_anchor(schema) {
        if let Some(found) = match_anchor(schema, anchor, base, reference)? {
            return Ok(Some(found));
        }
    }
    match_hash(schema, reference)
}

/// `FromValue`: every match is computed; the last one found wins.
fn from_value<'s>(
    schema: &'s JsValue,
    base: &Url,
    reference: &Url,
) -> Result<Option<Resolved<'s>>, JsError> {
    let next_base = match keywords::id(schema) {
        Some(id) => new_url(id, base.as_str())?,
        None => base.clone(),
    };
    if matches!(schema, JsValue::Object(_)) {
        if let Some(found) = match_schema(schema, &next_base, reference)? {
            return Ok(Some(found));
        }
    }
    let mut result = None;
    match schema {
        JsValue::Array(items) => {
            for item in items {
                if let Some(found) = from_value(item, &next_base, reference)? {
                    result = Some(found);
                }
            }
        }
        JsValue::Object(object) => {
            for (key, value) in object.entries() {
                if key == "const" || key == "enum" {
                    continue;
                }
                if let Some(found) = from_value(value, &next_base, reference)? {
                    result = Some(found);
                }
            }
        }
        JsValue::Null
        | JsValue::Bool(_)
        | JsValue::Number(_)
        | JsValue::String(_)
        | JsValue::Function(_) => {}
    }
    Ok(result)
}

/// `Resolve.Base(schema, base, target)`.
fn base_of(schema: &JsValue, base: &str, target: &JsValue) -> Result<Option<String>, JsError> {
    find_base(schema, &initial_base(base)?, target)
}

/// `Resolve.Ref(context, schema, base, ref, applySchemaId = false)` with an
/// empty context.
fn resolve<'s>(
    schema: Option<&'s JsValue>,
    base: &str,
    reference: &str,
) -> Result<Option<Resolved<'s>>, JsError> {
    let resolved_base = initial_base(base)?;
    let initial_reference = new_url(reference, resolved_base.as_str())?;
    // RefContext: `reference in {}` holds for inherited Object.prototype names.
    if !is_unsafe_property_key(reference) && NativeFunction::inherited(reference).is_some() {
        return Ok(Some(Resolved::Function));
    }
    let local = match schema {
        Some(schema) => from_value(schema, &resolved_base, &initial_reference)?,
        None => None,
    };
    // RefRemote never finds anything in an empty context.
    Ok(local.and_then(Resolved::non_nullish))
}

/// `Resolve.Resource`.
fn resource<'s>(
    schema: &'s JsValue,
    base: &str,
    reference: &str,
) -> Result<Option<&'s JsValue>, JsError> {
    Ok(resolve(Some(schema), base, reference)?
        .and_then(Resolved::schema_object)
        .filter(|found| keywords::id(found).is_some()))
}

/// The traversal state `ResolveRef` reads (`Stack.#StackFrame`).
pub(crate) struct StackFrame<'a, 's> {
    pub(crate) root: &'s JsValue,
    pub(crate) ids: &'a [&'s JsValue],
    pub(crate) lexical_schema: &'s JsValue,
    pub(crate) lexical_base: String,
    pub(crate) reference_base: String,
    pub(crate) resource_base: String,
    pub(crate) recursive_anchors: &'a [&'s JsValue],
    pub(crate) dynamic_anchors: &'a [&'s JsValue],
    pub(crate) in_retrieved_frame: bool,
}

/// A schema whose base comes from where it was found (`retrievedResource`).
pub(crate) struct RetrievedResource<'s> {
    pub(crate) target: &'s JsValue,
    pub(crate) base: String,
    pub(crate) root: &'s JsValue,
}

/// A `$ref` resolution with its scope side effects.
pub(crate) struct RefResult<'s> {
    pub(crate) schema: Option<Resolved<'s>>,
    pub(crate) retrieved_resource: Option<RetrievedResource<'s>>,
    /// `(target, resource)`: the enclosing `$id` resource to enter.
    pub(crate) resolved_resource: Option<(&'s JsValue, &'s JsValue)>,
}

fn legacy_retrieved_resource<'s>(
    frame: &StackFrame<'_, 's>,
    reference: &str,
    schema: &'s JsValue,
) -> Result<Option<RetrievedResource<'s>>, JsError> {
    if !reference.starts_with('#') {
        return Ok(None);
    }
    if let JsValue::Object(root) = frame.root {
        if root.has_own("$schema") {
            return Ok(None);
        }
    }
    let Some(target_base) = base_of(frame.lexical_schema, &frame.reference_base, schema)? else {
        return Ok(None);
    };
    if target_base == frame.reference_base {
        return Ok(None);
    }
    Ok(Some(RetrievedResource {
        target: schema,
        base: target_base,
        root: frame.lexical_schema,
    }))
}

/// `Resolve.ResolveRef`.
pub(crate) fn resolve_ref<'s>(
    frame: &StackFrame<'_, 's>,
    reference: &str,
) -> Result<RefResult<'s>, JsError> {
    let source = if frame.in_retrieved_frame {
        frame.lexical_schema
    } else {
        frame.root
    };
    let ref_root = if reference.starts_with('#') {
        frame.lexical_schema
    } else {
        source
    };
    let schema = resolve(Some(ref_root), &frame.reference_base, reference)?;
    let Some(target) = schema
        .filter(|found| found.is_truthy())
        .and_then(Resolved::schema_object)
    else {
        return Ok(RefResult {
            schema,
            retrieved_resource: None,
            resolved_resource: None,
        });
    };
    let canonical = canonical_href(&new_url(reference, &frame.reference_base)?);
    let is_remote = canonical != frame.resource_base;
    // RemoteRetrievedResource needs a context entry; only the legacy lookup applies.
    let retrieved_resource = legacy_retrieved_resource(frame, reference, target)?;
    let resolved_resource = if is_remote && keywords::id(target).is_none() {
        resource(frame.root, &frame.reference_base, &canonical)?
            .filter(|found| !frame.ids.iter().any(|id| std::ptr::eq(*id, *found)))
            .map(|found| (target, found))
    } else {
        None
    };
    Ok(RefResult {
        schema,
        retrieved_resource,
        resolved_resource,
    })
}

/// `url.href.split('#')[0]`.
fn canonical_href(url: &Url) -> String {
    url.as_str()
        .split('#')
        .next()
        .unwrap_or_default()
        .to_owned()
}

/// `Resolve.ResolveRecursiveRef`.
pub(crate) fn resolve_recursive_ref<'s>(
    frame: &StackFrame<'_, 's>,
    reference: &str,
) -> Result<Option<Resolved<'s>>, JsError> {
    let ref_root = if keywords::is_recursive_anchor_true(frame.lexical_schema) {
        frame.recursive_anchors.first().copied()
    } else {
        Some(frame.lexical_schema)
    };
    resolve(ref_root, &frame.lexical_base, reference)
}

/// `Resolve.ResolveDynamicRef` / `Resolve.DynamicRef`.
pub(crate) fn resolve_dynamic_ref<'s>(
    frame: &StackFrame<'_, 's>,
    reference: &str,
) -> Result<Option<Resolved<'s>>, JsError> {
    let initial = initial_base(&frame.lexical_base)?;
    let fragment_root = if reference.starts_with('#') {
        frame.lexical_schema
    } else {
        frame.root
    };
    let fragment_target = resolve(Some(fragment_root), &frame.lexical_base, reference)?;
    let find_anchor = |name: &str| {
        frame
            .dynamic_anchors
            .iter()
            .copied()
            .find(|anchor| keywords::dynamic_anchor(anchor) == Some(name))
    };
    let Some(fragment_target) = fragment_target else {
        let fragment = url_hash(&new_url(reference, initial.as_str())?);
        if !fragment.starts_with("#/") && fragment.starts_with('#') {
            let name = decode_uri_component(&fragment[1..])?;
            return Ok(find_anchor(&name)
                .or_else(|| find_dynamic_anchor(frame.root, &name))
                .map(Resolved::Value));
        }
        return Ok(None);
    };
    let Some(target_anchor) = fragment_target
        .schema_object()
        .and_then(keywords::dynamic_anchor)
    else {
        return Ok(Some(fragment_target));
    };
    let fragment = url_hash(&new_url(reference, initial.as_str())?);
    if fragment.starts_with("#/") {
        return Ok(Some(fragment_target));
    }
    Ok(Some(
        find_anchor(target_anchor).map_or(fragment_target, Resolved::Value),
    ))
}

/// `new URL(base).href` and the `$id` chain applied on top of it.
pub(crate) fn apply_ids(base: &str, ids: &[&JsValue]) -> Result<String, JsError> {
    let mut href = Url::parse(base)
        .map_err(|_| JsError::invalid_url())?
        .as_str()
        .to_owned();
    for schema in ids {
        if let Some(id) = keywords::id(schema) {
            new_url(id, &href)?.as_str().clone_into(&mut href);
        }
    }
    Ok(href)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pointer_get_reads_objects_arrays_and_inherited_members() {
        let document =
            JsValue::from_json(&serde_json::json!({ "a": [{ "b~/c": true }], "n": null }));
        assert!(matches!(
            pointer_get(&document, "/a/0/b~0~1c"),
            Some(Resolved::Value(JsValue::Bool(true)))
        ));
        assert!(
            matches!(pointer_get(&document, "/a/length"), Some(Resolved::Number(length)) if length.to_bits() == 1.0_f64.to_bits())
        );
        assert!(matches!(
            pointer_get(&document, "/a/map"),
            Some(Resolved::Function)
        ));
        assert!(matches!(
            pointer_get(&document, "/toString"),
            Some(Resolved::Function)
        ));
        assert!(matches!(
            pointer_get(&document, "/n"),
            Some(Resolved::Value(JsValue::Null))
        ));
        assert!(pointer_get(&document, "/missing/x").is_none());
        assert!(pointer_get(&document, "/constructor").is_none());
    }

    #[test]
    fn resolve_finds_defs_and_ids() {
        let document = JsValue::from_json(&serde_json::json!({
            "$defs": { "A": { "$id": "A", "type": "string" }, "B": { "type": "number" } }
        }));
        let by_pointer = resolve(Some(&document), "", "#/$defs/B")
            .expect("resolves")
            .and_then(Resolved::schema_object);
        assert_eq!(
            by_pointer.map(|schema| keywords::id(schema).is_none()),
            Some(true)
        );
        let by_id = resolve(Some(&document), "", "A")
            .expect("resolves")
            .and_then(Resolved::schema_object);
        assert_eq!(by_id.and_then(keywords::id), Some("A"));
        assert!(resolve(Some(&document), "", "missing")
            .expect("resolves")
            .is_none());
        assert!(matches!(
            resolve(Some(&document), "", "toString"),
            Ok(Some(Resolved::Function))
        ));
        assert_eq!(
            resolve(Some(&document), "", "http://[")
                .map(|_| ())
                .map_err(|error| error.message),
            Err("Invalid URL".to_owned())
        );
    }
}
