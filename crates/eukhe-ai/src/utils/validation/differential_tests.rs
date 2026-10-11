//! Differential table: outputs of pi-ai 1.0.4's `validateToolArguments`
//! (`dist/utils/validation.js`) and `TypeBox` 1.3.27's `Format.Test`, captured
//! under Node 26 for each schema/arguments pair below and asserted verbatim
//! (result JSON and key order, or the thrown error class and message).

use eukhe_types::pi_ai::{JsonValue, Tool, ToolCall};

use super::format;
use super::{validate_tool_arguments, JsErrorKind, ValidationError};

enum Expected {
    Ok(&'static str),
    Invalid(&'static str),
    Thrown(JsErrorKind, &'static str),
}

struct Case {
    name: &'static str,
    schema: &'static str,
    args: &'static str,
    expected: Expected,
}

const CASES: &[Case] = &[
    Case {
        name: "required_missing",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"string\"},\"b\":{\"type\":\"number\"}},\"required\":[\"a\",\"b\"]}",
        args: "{}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a: must have required properties a, b\n\nReceived arguments:\n{}"),
    },
    Case {
        name: "nested_required",
        schema: "{\"type\":\"object\",\"properties\":{\"meta\":{\"type\":\"object\",\"properties\":{\"id\":{\"type\":\"string\"}},\"required\":[\"id\"]}},\"required\":[\"meta\"]}",
        args: "{\"meta\":{}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - meta.id: must have required properties id\n\nReceived arguments:\n{\n  \"meta\": {}\n}"),
    },
    Case {
        name: "type_string_object",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"string\"}}}",
        args: "{\"a\":{}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a: must be string\n\nReceived arguments:\n{\n  \"a\": {}\n}"),
    },
    Case {
        name: "type_union_message",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":[\"string\",\"number\"]}}}",
        args: "{\"a\":{}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a: must be either string or number\n\nReceived arguments:\n{\n  \"a\": {}\n}"),
    },
    Case {
        name: "type_number_null_union",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":[\"number\",\"null\"]}}}",
        args: "{\"a\":\"abc\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a: must be either number or null\n\nReceived arguments:\n{\n  \"a\": \"abc\"\n}"),
    },
    Case {
        name: "additional_properties_false",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{}},\"additionalProperties\":false}",
        args: "{\"a\":1,\"b\":2,\"c\":3}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - b: schema is false\n  - c: schema is false\n  - root: must not have additional properties\n\nReceived arguments:\n{\n  \"a\": 1,\n  \"b\": 2,\n  \"c\": 3\n}"),
    },
    Case {
        name: "additional_properties_fast_path",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"number\"}},\"required\":[\"a\"],\"additionalProperties\":false}",
        args: "{\"a\":1,\"b\":2}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - b: schema is false\n  - root: must not have additional properties\n\nReceived arguments:\n{\n  \"a\": 1,\n  \"b\": 2\n}"),
    },
    Case {
        name: "additional_properties_schema_coerces",
        schema: "{\"type\":\"object\",\"properties\":{},\"additionalProperties\":{\"type\":\"number\"}}",
        args: "{\"x\":\"5\",\"y\":\"z\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - y: must be number\n  - root: must not have additional properties\n\nReceived arguments:\n{\n  \"x\": \"5\",\n  \"y\": \"z\"\n}"),
    },
    Case {
        name: "string_lengths",
        schema: "{\"type\":\"object\",\"properties\":{\"s\":{\"type\":\"string\",\"minLength\":3},\"t\":{\"type\":\"string\",\"maxLength\":5}}}",
        args: "{\"s\":\"ab\",\"t\":\"abcdef\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - s: must not have fewer than 3 characters\n  - t: must not have more than 5 characters\n\nReceived arguments:\n{\n  \"s\": \"ab\",\n  \"t\": \"abcdef\"\n}"),
    },
    Case {
        name: "grapheme_lengths",
        schema: "{\"type\":\"object\",\"properties\":{\"s\":{\"type\":\"string\",\"maxLength\":1},\"t\":{\"type\":\"string\",\"maxLength\":1}}}",
        args: "{\"s\":\"e\u{301}\",\"t\":\"\u{1f600}\u{1f600}\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - t: must not have more than 1 characters\n\nReceived arguments:\n{\n  \"s\": \"e\u{301}\",\n  \"t\": \"\u{1f600}\u{1f600}\"\n}"),
    },
    Case {
        name: "number_bounds",
        schema: "{\"type\":\"object\",\"properties\":{\"n\":{\"type\":\"number\",\"minimum\":1.5,\"exclusiveMaximum\":10},\"m\":{\"type\":\"number\",\"exclusiveMaximum\":10,\"maximum\":9,\"exclusiveMinimum\":20,\"minimum\":30}}}",
        args: "{\"n\":0,\"m\":10}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - n: must be >= 1.5\n  - m: must be < 10\n  - m: must be > 20\n  - m: must be <= 9\n  - m: must be >= 30\n\nReceived arguments:\n{\n  \"n\": 0,\n  \"m\": 10\n}"),
    },
    Case {
        name: "multiple_of",
        schema: "{\"type\":\"object\",\"properties\":{\"n\":{\"type\":\"number\",\"multipleOf\":0.1},\"m\":{\"type\":\"integer\",\"multipleOf\":3}}}",
        args: "{\"n\":0.35,\"m\":7}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - n: must be multiple of 0.1\n  - m: must be multiple of 3\n\nReceived arguments:\n{\n  \"n\": 0.35,\n  \"m\": 7\n}"),
    },
    Case {
        name: "enum_and_const",
        schema: "{\"type\":\"object\",\"properties\":{\"e\":{\"enum\":[\"a\",\"b\"]},\"c\":{\"const\":\"x\"},\"o\":{\"const\":{\"a\":[1,2]}}}}",
        args: "{\"e\":\"c\",\"c\":\"y\",\"o\":{\"a\":[1]}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - e: must be equal to one of the allowed values\n  - c: must be equal to constant\n  - o: must be equal to constant\n\nReceived arguments:\n{\n  \"e\": \"c\",\n  \"c\": \"y\",\n  \"o\": {\n    \"a\": [\n      1\n    ]\n  }\n}"),
    },
    Case {
        name: "const_object_passes",
        schema: "{\"type\":\"object\",\"properties\":{\"o\":{\"const\":{\"a\":[1,2]}}}}",
        args: "{\"o\":{\"a\":[1,2]}}",
        expected: Expected::Ok("{\"o\":{\"a\":[1,2]}}"),
    },
    Case {
        name: "pattern",
        schema: "{\"type\":\"object\",\"properties\":{\"p\":{\"type\":\"string\",\"pattern\":\"^[a-z]+$\"}}}",
        args: "{\"p\":\"ABC\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - p: must match pattern \"^[a-z]+$\"\n\nReceived arguments:\n{\n  \"p\": \"ABC\"\n}"),
    },
    Case {
        name: "pattern_unicode",
        schema: "{\"type\":\"object\",\"properties\":{\"p\":{\"type\":\"string\",\"pattern\":\"^\\\\p{L}+$\"}}}",
        args: "{\"p\":\"h\u{e9}llo\"}",
        expected: Expected::Ok("{\"p\":\"h\u{e9}llo\"}"),
    },
    Case {
        name: "formats",
        schema: "{\"type\":\"object\",\"properties\":{\"e\":{\"type\":\"string\",\"format\":\"email\"},\"d\":{\"type\":\"string\",\"format\":\"date-time\"},\"u\":{\"type\":\"string\",\"format\":\"uuid\"},\"x\":{\"type\":\"string\",\"format\":\"custom\"}}}",
        args: "{\"e\":\"nope\",\"d\":\"2020-01-01\",\"u\":\"zz\",\"x\":\"any\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - e: must match format \"email\"\n  - d: must match format \"date-time\"\n  - u: must match format \"uuid\"\n\nReceived arguments:\n{\n  \"e\": \"nope\",\n  \"d\": \"2020-01-01\",\n  \"u\": \"zz\",\n  \"x\": \"any\"\n}"),
    },
    Case {
        name: "array_items_unique",
        schema: "{\"type\":\"object\",\"properties\":{\"arr\":{\"type\":\"array\",\"items\":{\"type\":\"number\"},\"minItems\":3,\"uniqueItems\":true}}}",
        args: "{\"arr\":[\"1\",\"x\"]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - arr.1: must be number\n  - arr: must not have fewer than 3 items\n\nReceived arguments:\n{\n  \"arr\": [\n    \"1\",\n    \"x\"\n  ]\n}"),
    },
    Case {
        name: "array_unique_duplicates",
        schema: "{\"type\":\"object\",\"properties\":{\"arr\":{\"type\":\"array\",\"uniqueItems\":true,\"maxItems\":1}}}",
        args: "{\"arr\":[{\"a\":1,\"b\":2},{\"b\":2,\"a\":1}]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - arr: must not have more than 1 items\n  - arr: must not have duplicate items\n\nReceived arguments:\n{\n  \"arr\": [\n    {\n      \"a\": 1,\n      \"b\": 2\n    },\n    {\n      \"b\": 2,\n      \"a\": 1\n    }\n  ]\n}"),
    },
    Case {
        name: "array_unique_constructor_key",
        schema: "{\"type\":\"object\",\"properties\":{\"arr\":{\"type\":\"array\",\"uniqueItems\":true}}}",
        args: "{\"arr\":[{\"constructor\":1},{}]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - arr: must not have duplicate items\n\nReceived arguments:\n{\n  \"arr\": [\n    {\n      \"constructor\": 1\n    },\n    {}\n  ]\n}"),
    },
    Case {
        name: "tuple_additional_items",
        schema: "{\"type\":\"object\",\"properties\":{\"t\":{\"type\":\"array\",\"additionalItems\":false,\"items\":[{\"type\":\"string\"},{\"type\":\"number\"}],\"minItems\":2}}}",
        args: "{\"t\":[\"a\",\"2\",\"extra\",\"more\"]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - t.2: schema is false\n\nReceived arguments:\n{\n  \"t\": [\n    \"a\",\n    \"2\",\n    \"extra\",\n    \"more\"\n  ]\n}"),
    },
    Case {
        name: "prefix_items",
        schema: "{\"type\":\"object\",\"properties\":{\"t\":{\"type\":\"array\",\"prefixItems\":[{\"type\":\"string\"}],\"items\":{\"type\":\"number\"}}}}",
        args: "{\"t\":[1,\"b\",\"c\"]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - t.1: must be number\n  - t.2: must be number\n  - t.0: must be string\n\nReceived arguments:\n{\n  \"t\": [\n    1,\n    \"b\",\n    \"c\"\n  ]\n}"),
    },
    Case {
        name: "contains",
        schema: "{\"type\":\"object\",\"properties\":{\"c\":{\"type\":\"array\",\"contains\":{\"type\":\"string\"}},\"d\":{\"type\":\"array\",\"contains\":{\"type\":\"number\"},\"minContains\":2,\"maxContains\":3},\"e\":{\"type\":\"array\",\"contains\":{\"type\":\"number\"},\"maxContains\":1}}}",
        args: "{\"c\":[1,2],\"d\":[1,\"x\"],\"e\":[1,2]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - c: must contain at least 1 valid item\n  - d: must contain at least 1 valid item\n  - e: must contain at least 1 valid item\n\nReceived arguments:\n{\n  \"c\": [\n    1,\n    2\n  ],\n  \"d\": [\n    1,\n    \"x\"\n  ],\n  \"e\": [\n    1,\n    2\n  ]\n}"),
    },
    Case {
        name: "contains_empty",
        schema: "{\"type\":\"object\",\"properties\":{\"c\":{\"type\":\"array\",\"contains\":{\"type\":\"string\"}}}}",
        args: "{\"c\":[]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - c: must contain at least 1 valid item\n\nReceived arguments:\n{\n  \"c\": []\n}"),
    },
    Case {
        name: "any_of_errors",
        schema: "{\"type\":\"object\",\"properties\":{\"u\":{\"anyOf\":[{\"type\":\"string\",\"minLength\":2},{\"type\":\"number\"}]}}}",
        args: "{\"u\":{}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - u: must be string\n  - u: must be number\n  - u: must match a schema in anyOf\n\nReceived arguments:\n{\n  \"u\": {}\n}"),
    },
    Case {
        name: "one_of_both_pass",
        schema: "{\"type\":\"object\",\"properties\":{\"o\":{\"oneOf\":[{\"type\":\"number\"},{\"minimum\":0}]}}}",
        args: "{\"o\":5}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - o: must match exactly one schema in oneOf\n\nReceived arguments:\n{\n  \"o\": 5\n}"),
    },
    Case {
        name: "one_of_none_pass",
        schema: "{\"type\":\"object\",\"properties\":{\"o\":{\"oneOf\":[{\"type\":\"number\"},{\"type\":\"boolean\"}]}}}",
        args: "{\"o\":{}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - o: must be number\n  - o: must be boolean\n  - o: must match exactly one schema in oneOf\n\nReceived arguments:\n{\n  \"o\": {}\n}"),
    },
    Case {
        name: "all_of",
        schema: "{\"allOf\":[{\"required\":[\"a\"]},{\"required\":[\"b\"]}]}",
        args: "{}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a: must have required properties a\n  - b: must have required properties b\n\nReceived arguments:\n{}"),
    },
    Case {
        name: "all_of_coerces",
        schema: "{\"allOf\":[{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"number\"}}}]}",
        args: "{\"a\":\"1\"}",
        expected: Expected::Ok("{\"a\":1}"),
    },
    Case {
        name: "not",
        schema: "{\"type\":\"object\",\"properties\":{\"n\":{\"not\":{\"type\":\"string\"}}}}",
        args: "{\"n\":\"x\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - n: must not be valid\n\nReceived arguments:\n{\n  \"n\": \"x\"\n}"),
    },
    Case {
        name: "if_then",
        schema: "{\"type\":\"object\",\"properties\":{\"x\":{\"if\":{\"type\":\"number\"},\"then\":{\"minimum\":10},\"else\":{\"type\":\"string\"}}}}",
        args: "{\"x\":5}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - x: must match \"then\" schema\n\nReceived arguments:\n{\n  \"x\": 5\n}"),
    },
    Case {
        name: "if_else",
        schema: "{\"type\":\"object\",\"properties\":{\"x\":{\"if\":{\"type\":\"number\"},\"then\":{\"minimum\":10},\"else\":{\"type\":\"string\"}}}}",
        args: "{\"x\":{}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - x: must be string\n  - x: must match \"else\" schema\n\nReceived arguments:\n{\n  \"x\": {}\n}"),
    },
    Case {
        name: "dependent_required",
        schema: "{\"dependentRequired\":{\"a\":[\"b\",\"c\"]}}",
        args: "{\"a\":1}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - root: must have properties b, c when property a is present\n  - root: must have properties b, c when property a is present\n\nReceived arguments:\n{\n  \"a\": 1\n}"),
    },
    Case {
        name: "dependencies_array",
        schema: "{\"dependencies\":{\"a\":[\"b\",\"c\"]}}",
        args: "{\"a\":1}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - root: must have properties b, c when property a is present\n\nReceived arguments:\n{\n  \"a\": 1\n}"),
    },
    Case {
        name: "dependent_schemas",
        schema: "{\"dependentSchemas\":{\"a\":{\"required\":[\"z\"]}}}",
        args: "{\"a\":1}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - z: must have required properties z\n\nReceived arguments:\n{\n  \"a\": 1\n}"),
    },
    Case {
        name: "property_names",
        schema: "{\"propertyNames\":{\"pattern\":\"^[a-z]+$\",\"maxLength\":3}}",
        args: "{\"A\":1,\"b\":2,\"abcd\":3}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - A: must match pattern \"^[a-z]+$\"\n  - abcd: must not have more than 3 characters\n  - root: property names A, abcd are invalid\n\nReceived arguments:\n{\n  \"A\": 1,\n  \"b\": 2,\n  \"abcd\": 3\n}"),
    },
    Case {
        name: "min_max_properties",
        schema: "{\"type\":\"object\",\"properties\":{\"o\":{\"type\":\"object\",\"minProperties\":2},\"p\":{\"type\":\"object\",\"maxProperties\":1}}}",
        args: "{\"o\":{\"a\":1},\"p\":{\"a\":1,\"b\":2}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - o: must not have fewer than 2 properties\n  - p: must not have more than 1 properties\n\nReceived arguments:\n{\n  \"o\": {\n    \"a\": 1\n  },\n  \"p\": {\n    \"a\": 1,\n    \"b\": 2\n  }\n}"),
    },
    Case {
        name: "record_pattern_properties",
        schema: "{\"type\":\"object\",\"properties\":{\"r\":{\"type\":\"object\",\"patternProperties\":{\"^.*$\":{\"type\":\"number\"}}}}}",
        args: "{\"r\":{\"a\":\"x\",\"b\":2}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - r.a: must be number\n\nReceived arguments:\n{\n  \"r\": {\n    \"a\": \"x\",\n    \"b\": 2\n  }\n}"),
    },
    Case {
        name: "ref_defs_failure",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"#/$defs/v\"}},\"$defs\":{\"v\":{\"type\":\"number\"}}}",
        args: "{\"v\":\"x\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - v: must be number\n\nReceived arguments:\n{\n  \"v\": \"x\"\n}"),
    },
    Case {
        name: "cyclic_passes",
        schema: "{\"$defs\":{\"A\":{\"type\":\"object\",\"required\":[\"n\"],\"properties\":{\"n\":{\"anyOf\":[{\"$ref\":\"A\"},{\"type\":\"null\"}]}},\"$id\":\"A\"}},\"$ref\":\"A\"}",
        args: "{\"n\":{\"n\":null}}",
        expected: Expected::Ok("{\"n\":{\"n\":null}}"),
    },
    Case {
        name: "cyclic_fails",
        schema: "{\"$defs\":{\"A\":{\"type\":\"object\",\"required\":[\"n\"],\"properties\":{\"n\":{\"anyOf\":[{\"$ref\":\"A\"},{\"type\":\"null\"}]}},\"$id\":\"A\"}},\"$ref\":\"A\"}",
        args: "{\"n\":{\"n\":3}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - n.n: must be object\n  - n.n: must be null\n  - n.n: must match a schema in anyOf\n  - n: must be null\n  - n: must match a schema in anyOf\n\nReceived arguments:\n{\n  \"n\": {\n    \"n\": 3\n  }\n}"),
    },
    Case {
        name: "unresolvable_ref",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"#/nope\"}}}",
        args: "{\"v\":1}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - v: schema is false\n\nReceived arguments:\n{\n  \"v\": 1\n}"),
    },
    Case {
        name: "ref_to_non_schema",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"#/properties/v/x\"}}}",
        args: "{\"v\":1}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - v: schema is false\n\nReceived arguments:\n{\n  \"v\": 1\n}"),
    },
    Case {
        name: "anchor_ref",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"#foo\"}},\"$defs\":{\"x\":{\"$anchor\":\"foo\",\"type\":\"number\"}}}",
        args: "{\"v\":\"x\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - v: must be number\n\nReceived arguments:\n{\n  \"v\": \"x\"\n}"),
    },
    Case {
        name: "id_relative_ref",
        schema: "{\"$id\":\"https://example.com/root.json\",\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"item.json\"}},\"$defs\":{\"item\":{\"$id\":\"item.json\",\"type\":\"string\",\"minLength\":2}}}",
        args: "{\"v\":\"x\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - v: must not have fewer than 2 characters\n\nReceived arguments:\n{\n  \"v\": \"x\"\n}"),
    },
    Case {
        name: "dynamic_ref",
        schema: "{\"$id\":\"https://example.com/tree\",\"$dynamicAnchor\":\"node\",\"type\":\"object\",\"properties\":{\"child\":{\"$dynamicRef\":\"#node\"},\"n\":{\"type\":\"number\"}}}",
        args: "{\"n\":1,\"child\":{\"n\":\"x\"}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - child.n: must be number\n\nReceived arguments:\n{\n  \"n\": 1,\n  \"child\": {\n    \"n\": \"x\"\n  }\n}"),
    },
    Case {
        name: "max_errors_cap",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"string\"},\"b\":{\"type\":\"string\"},\"c\":{\"type\":\"string\"},\"d\":{\"type\":\"string\"},\"e\":{\"type\":\"string\"},\"f\":{\"type\":\"string\"},\"g\":{\"type\":\"string\"},\"h\":{\"type\":\"string\"},\"i\":{\"type\":\"string\"},\"j\":{\"type\":\"string\"}},\"required\":[\"a\",\"b\",\"c\",\"d\",\"e\",\"f\",\"g\",\"h\",\"i\",\"j\",\"k\"]}",
        args: "{\"a\":{},\"b\":{},\"c\":{},\"d\":{},\"e\":{},\"f\":{},\"g\":{},\"h\":{},\"i\":{},\"j\":{}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - k: must have required properties k\n  - a: must be string\n  - b: must be string\n  - c: must be string\n  - d: must be string\n  - e: must be string\n  - f: must be string\n  - g: must be string\n\nReceived arguments:\n{\n  \"a\": {},\n  \"b\": {},\n  \"c\": {},\n  \"d\": {},\n  \"e\": {},\n  \"f\": {},\n  \"g\": {},\n  \"h\": {},\n  \"i\": {},\n  \"j\": {}\n}"),
    },
    Case {
        name: "integer_keys_order",
        schema: "{\"type\":\"object\",\"properties\":{\"b\":{\"type\":\"string\"},\"1\":{\"type\":\"string\"},\"a\":{\"type\":\"string\"},\"0\":{\"type\":\"string\"}}}",
        args: "{\"b\":{},\"a\":{},\"1\":{},\"0\":{}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - 0: must be string\n  - 1: must be string\n  - b: must be string\n  - a: must be string\n\nReceived arguments:\n{\n  \"0\": {},\n  \"1\": {},\n  \"b\": {},\n  \"a\": {}\n}"),
    },
    Case {
        name: "number_formatting_in_received",
        schema: "{\"type\":\"object\",\"properties\":{\"f\":{\"type\":\"boolean\"}}}",
        args: "{\"f\":\"nope\",\"big\":1e+21,\"small\":1e-06,\"tiny\":1.5e-07,\"neg\":-2.5,\"int\":12345678901234567000,\"frac\":0.1}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - f: must be boolean\n\nReceived arguments:\n{\n  \"f\": \"nope\",\n  \"big\": 1e+21,\n  \"small\": 0.000001,\n  \"tiny\": 1.5e-7,\n  \"neg\": -2.5,\n  \"int\": 12345678901234567000,\n  \"frac\": 0.1\n}"),
    },
    Case {
        name: "string_escapes_in_received",
        schema: "{\"type\":\"object\",\"properties\":{\"f\":{\"type\":\"boolean\"}}}",
        args: "{\"f\":\"x\",\"s\":\"quote \\\" back \\\\ nl \\n tab \\t ctl \\u0001 del \u{7f} emoji \u{1f600} ls \u{2028}\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - f: must be boolean\n\nReceived arguments:\n{\n  \"f\": \"x\",\n  \"s\": \"quote \\\" back \\\\ nl \\n tab \\t ctl \\u0001 del \u{7f} emoji \u{1f600} ls \u{2028}\"\n}"),
    },
    Case {
        name: "nested_arrays_in_received",
        schema: "{\"type\":\"object\",\"properties\":{\"f\":{\"type\":\"boolean\"}}}",
        args: "{\"f\":\"x\",\"a\":[],\"o\":{},\"n\":[[1,[2]],{\"k\":[null,true]}]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - f: must be boolean\n\nReceived arguments:\n{\n  \"f\": \"x\",\n  \"a\": [],\n  \"o\": {},\n  \"n\": [\n    [\n      1,\n      [\n        2\n      ]\n    ],\n    {\n      \"k\": [\n        null,\n        true\n      ]\n    }\n  ]\n}"),
    },
    Case {
        name: "coerce_number_strings",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"number\"},\"b\":{\"type\":\"number\"},\"c\":{\"type\":\"number\"},\"d\":{\"type\":\"number\"},\"e\":{\"type\":\"integer\"}}}",
        args: "{\"a\":\" 42 \",\"b\":\"0x10\",\"c\":\"1e3\",\"d\":\"Infinity\",\"e\":\"-0\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - d: must be number\n\nReceived arguments:\n{\n  \"a\": \" 42 \",\n  \"b\": \"0x10\",\n  \"c\": \"1e3\",\n  \"d\": \"Infinity\",\n  \"e\": \"-0\"\n}"),
    },
    Case {
        name: "coerce_number_to_string",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"string\"},\"b\":{\"type\":\"string\"},\"c\":{\"type\":\"string\"}}}",
        args: "{\"a\":1.5,\"b\":1e+21,\"c\":1e-07}",
        expected: Expected::Ok("{\"a\":\"1.5\",\"b\":\"1e+21\",\"c\":\"1e-7\"}"),
    },
    Case {
        name: "normalize_nulls_in_arrays",
        schema: "{\"type\":\"object\",\"properties\":{\"items\":{\"type\":\"array\",\"items\":{\"type\":\"object\",\"properties\":{\"x\":{\"type\":\"number\"},\"y\":{\"type\":[\"number\",\"null\"]}}}}}}",
        args: "{\"items\":[{\"x\":null,\"y\":null}]}",
        expected: Expected::Ok("{\"items\":[{\"y\":null}]}"),
    },
    Case {
        name: "required_null_coerced",
        schema: "{\"type\":\"object\",\"properties\":{\"s\":{\"type\":\"string\"}},\"required\":[\"s\"]}",
        args: "{\"s\":null}",
        expected: Expected::Ok("{\"s\":\"\"}"),
    },
    Case {
        name: "inherited_to_string_key",
        schema: "{\"type\":\"object\",\"properties\":{\"toString\":{\"type\":\"string\"}}}",
        args: "{}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - toString: must be string\n\nReceived arguments:\n{}"),
    },
    Case {
        name: "inherited_constructor_key",
        schema: "{\"type\":\"object\",\"properties\":{\"constructor\":{\"type\":\"string\"}}}",
        args: "{}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - constructor: must be string\n\nReceived arguments:\n{}"),
    },
    Case {
        name: "inherited_key_accepting_schema",
        schema: "{\"type\":\"object\",\"properties\":{\"valueOf\":{}}}",
        args: "{}",
        expected: Expected::Ok("{}"),
    },
    Case {
        name: "inherited_key_union_clone",
        schema: "{\"type\":\"object\",\"properties\":{\"toString\":{\"anyOf\":[{\"type\":\"string\"},{\"type\":\"number\"}]}}}",
        args: "{}",
        expected: Expected::Thrown(JsErrorKind::DataCloneError, "function toString() { [native code] } could not be cloned."),
    },
    Case {
        name: "required_inherited_key",
        schema: "{\"type\":\"object\",\"required\":[\"toString\"]}",
        args: "{}",
        expected: Expected::Ok("{}"),
    },
    Case {
        name: "root_number_schema",
        schema: "5",
        args: "{}",
        expected: Expected::Thrown(JsErrorKind::TypeError, "Cannot use 'in' operator to search for 'type' in 5"),
    },
    Case {
        name: "root_null_schema",
        schema: "null",
        args: "{}",
        expected: Expected::Thrown(JsErrorKind::TypeError, "Cannot read properties of null (reading 'properties')"),
    },
    Case {
        name: "root_false_schema",
        schema: "false",
        args: "{}",
        expected: Expected::Thrown(JsErrorKind::TypeError, "Invalid value used as weak map key"),
    },
    Case {
        name: "root_true_schema",
        schema: "true",
        args: "{\"a\":1}",
        expected: Expected::Thrown(JsErrorKind::TypeError, "Invalid value used as weak map key"),
    },
    Case {
        name: "null_property_schema",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":null}}",
        args: "{\"a\":null}",
        expected: Expected::Thrown(JsErrorKind::TypeError, "Cannot read properties of null (reading '$ref')"),
    },
    Case {
        name: "required_number_iterable",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"string\"}},\"required\":5}",
        args: "{\"a\":null}",
        expected: Expected::Thrown(JsErrorKind::TypeError, "number 5 is not iterable (cannot read property Symbol(Symbol.iterator))"),
    },
    Case {
        name: "unevaluated_properties",
        schema: "{\"allOf\":[{\"type\":\"object\",\"properties\":{\"a\":{}}}],\"unevaluatedProperties\":false}",
        args: "{\"a\":1,\"b\":2}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - root: must not have unevaluated properties\n\nReceived arguments:\n{\n  \"a\": 1,\n  \"b\": 2\n}"),
    },
    Case {
        name: "unevaluated_items",
        schema: "{\"type\":\"array\",\"prefixItems\":[{\"type\":\"number\"}],\"unevaluatedItems\":false}",
        args: "{}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - root: must be array\n\nReceived arguments:\n{}"),
    },
    Case {
        name: "unevaluated_items_nested",
        schema: "{\"type\":\"object\",\"properties\":{\"t\":{\"prefixItems\":[{\"type\":\"number\"}],\"unevaluatedItems\":{\"type\":\"string\"}}}}",
        args: "{\"t\":[1,\"a\",2]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - t: must not have unevaluated items\n\nReceived arguments:\n{\n  \"t\": [\n    1,\n    \"a\",\n    2\n  ]\n}"),
    },
    Case {
        name: "union_coercion_picks_valid_arm",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"anyOf\":[{\"type\":\"boolean\"},{\"type\":\"number\"}]}}}",
        args: "{\"v\":\"1\"}",
        expected: Expected::Ok("{\"v\":1}"),
    },
    Case {
        name: "string_enum_helper",
        schema: "{\"type\":\"object\",\"properties\":{\"op\":{\"type\":\"string\",\"enum\":[\"add\",\"sub\"],\"description\":\"op\"}},\"required\":[\"op\"]}",
        args: "{\"op\":\"mul\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - op: must be equal to one of the allowed values\n\nReceived arguments:\n{\n  \"op\": \"mul\"\n}"),
    },
    Case {
        name: "slash_in_key_path",
        schema: "{\"type\":\"object\",\"properties\":{\"a/b\":{\"type\":\"number\"}}}",
        args: "{\"a/b\":\"x\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a.b: must be number\n\nReceived arguments:\n{\n  \"a/b\": \"x\"\n}"),
    },
    Case {
        name: "deep_required_path",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"object\",\"properties\":{\"b\":{\"type\":\"object\",\"properties\":{\"c\":{\"type\":\"string\"}},\"required\":[\"c\"]}}}}}",
        args: "{\"a\":{\"b\":{}}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a.b.c: must have required properties c\n\nReceived arguments:\n{\n  \"a\": {\n    \"b\": {}\n  }\n}"),
    },
    Case {
        name: "boolean_schema_property",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":false}}",
        args: "{\"a\":1}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a: schema is false\n\nReceived arguments:\n{\n  \"a\": 1\n}"),
    },
    Case {
        name: "empty_args_valid",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"string\"}}}",
        args: "{}",
        expected: Expected::Ok("{}"),
    },
    Case {
        name: "integer_float_literal",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"integer\"}}}",
        args: "{\"a\":1}",
        expected: Expected::Ok("{\"a\":1}"),
    },
    Case {
        name: "ref_cycle_root",
        schema: "{\"$ref\":\"#\"}",
        args: "{}",
        expected: Expected::Thrown(JsErrorKind::RangeError, "Maximum call stack size exceeded"),
    },
    Case {
        name: "invalid_url_ref",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"http://[\"}}}",
        args: "{\"v\":1}",
        expected: Expected::Thrown(JsErrorKind::TypeError, "Invalid URL"),
    },
    Case {
        name: "malformed_ref_fragment",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"#%E0\"}}}",
        args: "{\"v\":1}",
        expected: Expected::Thrown(JsErrorKind::UriError, "URI malformed"),
    },
    Case {
        name: "ref_to_missing_pointer",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"#/properties/v/x\"},\"w\":{\"x\":5}}}",
        args: "{\"v\":1}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - v: schema is false\n\nReceived arguments:\n{\n  \"v\": 1\n}"),
    },
    Case {
        name: "ref_to_number_target",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"#/$defs/n\"}},\"$defs\":{\"n\":5}}",
        args: "{\"v\":1}",
        expected: Expected::Thrown(JsErrorKind::TypeError, "Cannot use 'in' operator to search for 'type' in 5"),
    },
    Case {
        name: "ref_to_array_target",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"#/required\"}},\"required\":[]}",
        args: "{\"v\":1}",
        expected: Expected::Ok("{\"v\":1}"),
    },
    Case {
        name: "ref_to_array_length",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"#/required/length\"}},\"required\":[]}",
        args: "{\"v\":1}",
        expected: Expected::Thrown(JsErrorKind::TypeError, "Cannot use 'in' operator to search for 'type' in 0"),
    },
    Case {
        name: "ref_to_inherited_function",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"$ref\":\"toString\"}}}",
        args: "{\"v\":1}",
        expected: Expected::Ok("{\"v\":1}"),
    },
    Case {
        name: "not_with_unevaluated",
        schema: "{\"properties\":{\"a\":{}},\"not\":{\"required\":[\"b\"]},\"unevaluatedProperties\":false}",
        args: "{\"a\":1,\"c\":2}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - root: must not have unevaluated properties\n\nReceived arguments:\n{\n  \"a\": 1,\n  \"c\": 2\n}"),
    },
    Case {
        name: "required_null_number_coerced",
        schema: "{\"type\":\"object\",\"properties\":{\"n\":{\"type\":\"number\"}},\"required\":[\"n\"]}",
        args: "{\"n\":null}",
        expected: Expected::Ok("{\"n\":0}"),
    },
    Case {
        name: "union_ref_arm_not_coerced",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"anyOf\":[{\"$ref\":\"#/$defs/n\"},{\"type\":\"null\"}]}},\"$defs\":{\"n\":{\"type\":\"number\"}}}",
        args: "{\"v\":\"5\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - v: must be number\n  - v: must be null\n  - v: must match a schema in anyOf\n\nReceived arguments:\n{\n  \"v\": \"5\"\n}"),
    },
    Case {
        name: "boolean_false_property_null_kept",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":false}}",
        args: "{\"a\":null}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a: schema is false\n\nReceived arguments:\n{\n  \"a\": null\n}"),
    },
    Case {
        name: "boolean_union_arms",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"anyOf\":[false,{\"type\":\"number\"}]}}}",
        args: "{\"a\":\"3\"}",
        expected: Expected::Ok("{\"a\":3}"),
    },
    Case {
        name: "boolean_true_union_arm",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"anyOf\":[true,{\"type\":\"number\"}]}}}",
        args: "{\"a\":\"3\"}",
        expected: Expected::Ok("{\"a\":3}"),
    },
    Case {
        name: "nested_any_of_cap",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"anyOf\":[{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"string\"},\"b\":{\"type\":\"string\"},\"c\":{\"type\":\"string\"},\"d\":{\"type\":\"string\"},\"e\":{\"type\":\"string\"},\"f\":{\"type\":\"string\"},\"g\":{\"type\":\"string\"},\"h\":{\"type\":\"string\"},\"i\":{\"type\":\"string\"},\"j\":{\"type\":\"string\"}}},{\"type\":\"number\"}]}}}",
        args: "{\"a\":{\"a\":{},\"b\":{},\"c\":{},\"d\":{},\"e\":{},\"f\":{},\"g\":{},\"h\":{},\"i\":{},\"j\":{}}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a.a: must be string\n  - a.b: must be string\n  - a.c: must be string\n  - a.d: must be string\n  - a.e: must be string\n  - a.f: must be string\n  - a.g: must be string\n  - a.h: must be string\n\nReceived arguments:\n{\n  \"a\": {\n    \"a\": {},\n    \"b\": {},\n    \"c\": {},\n    \"d\": {},\n    \"e\": {},\n    \"f\": {},\n    \"g\": {},\n    \"h\": {},\n    \"i\": {},\n    \"j\": {}\n  }\n}"),
    },
    Case {
        name: "record_with_additional",
        schema: "{\"type\":\"object\",\"properties\":{\"r\":{\"type\":\"object\",\"patternProperties\":{\"^x\":{\"type\":\"number\"}},\"additionalProperties\":{\"type\":\"string\"}}}}",
        args: "{\"r\":{\"x1\":\"n\",\"y\":1}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - r.x1: must be number\n\nReceived arguments:\n{\n  \"r\": {\n    \"x1\": \"n\",\n    \"y\": 1\n  }\n}"),
    },
    Case {
        name: "unique_numbers_float",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"array\",\"uniqueItems\":true}}}",
        args: "{\"a\":[1,1,\"1\"]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a: must not have duplicate items\n\nReceived arguments:\n{\n  \"a\": [\n    1,\n    1,\n    \"1\"\n  ]\n}"),
    },
    Case {
        name: "contains_with_unevaluated_items",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"type\":\"array\",\"contains\":{\"type\":\"string\"},\"unevaluatedItems\":false}}}",
        args: "{\"a\":[\"x\",1]}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a: must not have unevaluated items\n\nReceived arguments:\n{\n  \"a\": [\n    \"x\",\n    1\n  ]\n}"),
    },
    Case {
        name: "property_names_false",
        schema: "{\"type\":\"object\",\"properties\":{\"o\":{\"type\":\"object\",\"propertyNames\":false}}}",
        args: "{\"o\":{\"k\":1}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - o.k: schema is false\n  - o: property names k are invalid\n\nReceived arguments:\n{\n  \"o\": {\n    \"k\": 1\n  }\n}"),
    },
    Case {
        name: "fractional_min_length",
        schema: "{\"type\":\"object\",\"properties\":{\"s\":{\"type\":\"string\",\"minLength\":1.5}}}",
        args: "{\"s\":\"a\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - s: must not have fewer than 1.5 characters\n\nReceived arguments:\n{\n  \"s\": \"a\"\n}"),
    },
    Case {
        name: "const_null_and_enum_objects",
        schema: "{\"type\":\"object\",\"properties\":{\"n\":{\"const\":null},\"e\":{\"enum\":[{\"a\":1},[1,2]]}}}",
        args: "{\"n\":0,\"e\":{\"a\":2}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - n: must be equal to constant\n  - e: must be equal to one of the allowed values\n\nReceived arguments:\n{\n  \"n\": 0,\n  \"e\": {\n    \"a\": 2\n  }\n}"),
    },
    Case {
        name: "enum_objects_pass",
        schema: "{\"type\":\"object\",\"properties\":{\"e\":{\"enum\":[{\"a\":1},[1,2]]}}}",
        args: "{\"e\":[1,2]}",
        expected: Expected::Ok("{\"e\":[1,2]}"),
    },
    Case {
        name: "format_hostname_error",
        schema: "{\"type\":\"object\",\"properties\":{\"h\":{\"type\":\"string\",\"format\":\"hostname\"}}}",
        args: "{\"h\":\"bad_host\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - h: must match format \"hostname\"\n\nReceived arguments:\n{\n  \"h\": \"bad_host\"\n}"),
    },
    Case {
        name: "integer_from_decimal_string",
        schema: "{\"type\":\"object\",\"properties\":{\"i\":{\"type\":\"integer\"}}}",
        args: "{\"i\":\"1.0\"}",
        expected: Expected::Ok("{\"i\":1}"),
    },
    Case {
        name: "number_from_blank_string",
        schema: "{\"type\":\"object\",\"properties\":{\"n\":{\"type\":\"number\"}}}",
        args: "{\"n\":\"   \"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - n: must be number\n\nReceived arguments:\n{\n  \"n\": \"   \"\n}"),
    },
    Case {
        name: "string_from_negative_zero",
        schema: "{\"type\":\"object\",\"properties\":{\"s\":{\"type\":\"string\"}}}",
        args: "{\"s\":0}",
        expected: Expected::Ok("{\"s\":\"0\"}"),
    },
    Case {
        name: "boolean_case_sensitive",
        schema: "{\"type\":\"object\",\"properties\":{\"b\":{\"type\":\"boolean\"}}}",
        args: "{\"b\":\"TRUE\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - b: must be boolean\n\nReceived arguments:\n{\n  \"b\": \"TRUE\"\n}"),
    },
    Case {
        name: "if_then_errors_hidden",
        schema: "{\"type\":\"object\",\"properties\":{\"x\":{\"if\":{\"type\":\"object\"},\"then\":{\"required\":[\"a\",\"b\"]}}}}",
        args: "{\"x\":{}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - x: must match \"then\" schema\n\nReceived arguments:\n{\n  \"x\": {}\n}"),
    },
    Case {
        name: "items_array_coercion",
        schema: "{\"type\":\"object\",\"properties\":{\"t\":{\"type\":\"array\",\"items\":[{\"type\":\"number\"},{\"type\":\"boolean\"}]}}}",
        args: "{\"t\":[\"1\",\"true\",\"x\"]}",
        expected: Expected::Ok("{\"t\":[1,true,\"x\"]}"),
    },
    Case {
        name: "array_items_null_schema_entry",
        schema: "{\"type\":\"object\",\"properties\":{\"t\":{\"type\":\"array\",\"items\":[null,{\"type\":\"number\"}]}}}",
        args: "{\"t\":[\"a\",\"2\"]}",
        expected: Expected::Ok("{\"t\":[\"a\",2]}"),
    },
    Case {
        name: "nested_type_array_union_object",
        schema: "{\"type\":\"object\",\"properties\":{\"o\":{\"type\":[\"object\",\"null\"],\"properties\":{\"n\":{\"type\":\"number\"}}}}}",
        args: "{\"o\":{\"n\":\"7\"}}",
        expected: Expected::Ok("{\"o\":{\"n\":7}}"),
    },
    Case {
        name: "one_of_coercion",
        schema: "{\"type\":\"object\",\"properties\":{\"v\":{\"oneOf\":[{\"type\":\"number\"},{\"type\":\"string\",\"minLength\":5}]}}}",
        args: "{\"v\":\"abc\"}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - v: must be number\n  - v: must not have fewer than 5 characters\n  - v: must match exactly one schema in oneOf\n\nReceived arguments:\n{\n  \"v\": \"abc\"\n}"),
    },
    Case {
        name: "properties_array_container",
        schema: "{\"type\":\"object\",\"properties\":[{\"type\":\"string\"}]}",
        args: "{\"0\":5}",
        expected: Expected::Ok("{\"0\":\"5\"}"),
    },
    Case {
        name: "properties_string_container",
        schema: "{\"type\":\"object\",\"properties\":\"ab\"}",
        args: "{\"0\":null}",
        expected: Expected::Ok("{\"0\":null}"),
    },
    Case {
        name: "dependencies_schema",
        schema: "{\"dependencies\":{\"a\":{\"required\":[\"q\"]}}}",
        args: "{\"a\":1}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - q: must have required properties q\n\nReceived arguments:\n{\n  \"a\": 1\n}"),
    },
    Case {
        name: "nested_ref_defs_in_subschema",
        schema: "{\"type\":\"object\",\"properties\":{\"a\":{\"$defs\":{\"s\":{\"type\":\"string\"}},\"$ref\":\"#/$defs/s\"}}}",
        args: "{\"a\":1}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - a: must be string\n\nReceived arguments:\n{\n  \"a\": 1\n}"),
    },
    Case {
        name: "multiple_of_float_tolerance",
        schema: "{\"type\":\"object\",\"properties\":{\"n\":{\"type\":\"number\",\"multipleOf\":0.01}}}",
        args: "{\"n\":1.13}",
        expected: Expected::Ok("{\"n\":1.13}"),
    },
    Case {
        name: "multiple_of_zero_divisor",
        schema: "{\"type\":\"object\",\"properties\":{\"n\":{\"type\":\"number\",\"multipleOf\":0}}}",
        args: "{\"n\":3}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - n: must be multiple of 0\n\nReceived arguments:\n{\n  \"n\": 3\n}"),
    },
    Case {
        name: "unicode_pattern_properties_keys",
        schema: "{\"type\":\"object\",\"properties\":{\"r\":{\"type\":\"object\",\"patternProperties\":{\"^\\\\p{Lu}\":{\"type\":\"number\"}},\"additionalProperties\":false}}}",
        args: "{\"r\":{\"\u{c4}\":\"x\",\"b\":1}}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - r.b: schema is false\n  - r: must not have additional properties\n  - r.\u{c4}: must be number\n\nReceived arguments:\n{\n  \"r\": {\n    \"\u{c4}\": \"x\",\n    \"b\": 1\n  }\n}"),
    },
    Case {
        name: "deep_value_recursive_schema",
        schema: "{\"$defs\":{\"N\":{\"type\":\"object\",\"properties\":{\"next\":{\"$ref\":\"#/$defs/N\"},\"v\":{\"type\":\"number\"}}}},\"$ref\":\"#/$defs/N\"}",
        args: "{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"next\":{\"v\":\"bad\"},\"v\":0},\"v\":1},\"v\":2},\"v\":3},\"v\":4},\"v\":5},\"v\":6},\"v\":7},\"v\":8},\"v\":9},\"v\":10},\"v\":11},\"v\":12},\"v\":13},\"v\":14},\"v\":15},\"v\":16},\"v\":17},\"v\":18},\"v\":19},\"v\":20},\"v\":21},\"v\":22},\"v\":23},\"v\":24},\"v\":25},\"v\":26},\"v\":27},\"v\":28},\"v\":29},\"v\":30},\"v\":31},\"v\":32},\"v\":33},\"v\":34},\"v\":35},\"v\":36},\"v\":37},\"v\":38},\"v\":39},\"v\":40},\"v\":41},\"v\":42},\"v\":43},\"v\":44},\"v\":45},\"v\":46},\"v\":47},\"v\":48},\"v\":49},\"v\":50},\"v\":51},\"v\":52},\"v\":53},\"v\":54},\"v\":55},\"v\":56},\"v\":57},\"v\":58},\"v\":59}",
        expected: Expected::Invalid("Validation failed for tool \"echo\":\n  - next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.next.v: must be number\n\nReceived arguments:\n{\n  \"next\": {\n    \"next\": {\n      \"next\": {\n        \"next\": {\n          \"next\": {\n            \"next\": {\n              \"next\": {\n                \"next\": {\n                  \"next\": {\n                    \"next\": {\n                      \"next\": {\n                        \"next\": {\n                          \"next\": {\n                            \"next\": {\n                              \"next\": {\n                                \"next\": {\n                                  \"next\": {\n                                    \"next\": {\n                                      \"next\": {\n                                        \"next\": {\n                                          \"next\": {\n                                            \"next\": {\n                                              \"next\": {\n                                                \"next\": {\n                                                  \"next\": {\n                                                    \"next\": {\n                                                      \"next\": {\n                                                        \"next\": {\n                                                          \"next\": {\n                                                            \"next\": {\n                                                              \"next\": {\n                                                                \"next\": {\n                                                                  \"next\": {\n                                                                    \"next\": {\n                                                                      \"next\": {\n                                                                        \"next\": {\n                                                                          \"next\": {\n                                                                            \"next\": {\n                                                                              \"next\": {\n                                                                                \"next\": {\n                                                                                  \"next\": {\n                                                                                    \"next\": {\n                                                                                      \"next\": {\n                                                                                        \"next\": {\n                                                                                          \"next\": {\n                                                                                            \"next\": {\n                                                                                              \"next\": {\n                                                                                                \"next\": {\n                                                                                                  \"next\": {\n                                                                                                    \"next\": {\n                                                                                                      \"next\": {\n                                                                                                        \"next\": {\n                                                                                                          \"next\": {\n                                                                                                            \"next\": {\n                                                                                                              \"next\": {\n                                                                                                                \"next\": {\n                                                                                                                  \"next\": {\n                                                                                                                    \"next\": {\n                                                                                                                      \"next\": {\n                                                                                                                        \"next\": {\n                                                                                                                          \"v\": \"bad\"\n                                                                                                                        },\n                                                                                                                        \"v\": 0\n                                                                                                                      },\n                                                                                                                      \"v\": 1\n                                                                                                                    },\n                                                                                                                    \"v\": 2\n                                                                                                                  },\n                                                                                                                  \"v\": 3\n                                                                                                                },\n                                                                                                                \"v\": 4\n                                                                                                              },\n                                                                                                              \"v\": 5\n                                                                                                            },\n                                                                                                            \"v\": 6\n                                                                                                          },\n                                                                                                          \"v\": 7\n                                                                                                        },\n                                                                                                        \"v\": 8\n                                                                                                      },\n                                                                                                      \"v\": 9\n                                                                                                    },\n                                                                                                    \"v\": 10\n                                                                                                  },\n                                                                                                  \"v\": 11\n                                                                                                },\n                                                                                                \"v\": 12\n                                                                                              },\n                                                                                              \"v\": 13\n                                                                                            },\n                                                                                            \"v\": 14\n                                                                                          },\n                                                                                          \"v\": 15\n                                                                                        },\n                                                                                        \"v\": 16\n                                                                                      },\n                                                                                      \"v\": 17\n                                                                                    },\n                                                                                    \"v\": 18\n                                                                                  },\n                                                                                  \"v\": 19\n                                                                                },\n                                                                                \"v\": 20\n                                                                              },\n                                                                              \"v\": 21\n                                                                            },\n                                                                            \"v\": 22\n                                                                          },\n                                                                          \"v\": 23\n                                                                        },\n                                                                        \"v\": 24\n                                                                      },\n                                                                      \"v\": 25\n                                                                    },\n                                                                    \"v\": 26\n                                                                  },\n                                                                  \"v\": 27\n                                                                },\n                                                                \"v\": 28\n                                                              },\n                                                              \"v\": 29\n                                                            },\n                                                            \"v\": 30\n                                                          },\n                                                          \"v\": 31\n                                                        },\n                                                        \"v\": 32\n                                                      },\n                                                      \"v\": 33\n                                                    },\n                                                    \"v\": 34\n                                                  },\n                                                  \"v\": 35\n                                                },\n                                                \"v\": 36\n                                              },\n                                              \"v\": 37\n                                            },\n                                            \"v\": 38\n                                          },\n                                          \"v\": 39\n                                        },\n                                        \"v\": 40\n                                      },\n                                      \"v\": 41\n                                    },\n                                    \"v\": 42\n                                  },\n                                  \"v\": 43\n                                },\n                                \"v\": 44\n                              },\n                              \"v\": 45\n                            },\n                            \"v\": 46\n                          },\n                          \"v\": 47\n                        },\n                        \"v\": 48\n                      },\n                      \"v\": 49\n                    },\n                    \"v\": 50\n                  },\n                  \"v\": 51\n                },\n                \"v\": 52\n              },\n              \"v\": 53\n            },\n            \"v\": 54\n          },\n          \"v\": 55\n        },\n        \"v\": 56\n      },\n      \"v\": 57\n    },\n    \"v\": 58\n  },\n  \"v\": 59\n}"),
    },
    Case {
        name: "additional_properties_true_with_unevaluated",
        schema: "{\"properties\":{\"a\":{}},\"additionalProperties\":true,\"unevaluatedProperties\":false}",
        args: "{\"a\":1,\"b\":2}",
        expected: Expected::Ok("{\"a\":1,\"b\":2}"),
    },
    Case {
        name: "root_array_schema",
        schema: "[]",
        args: "{\"a\":1}",
        expected: Expected::Ok("{\"a\":1}"),
    },
];

fn parse(text: &str) -> JsonValue {
    serde_json::from_str(text).unwrap_or_else(|error| panic!("invalid JSON {text}: {error}"))
}

#[test]
fn validate_tool_arguments_matches_node() {
    for case in CASES {
        let tool = Tool {
            name: "echo".to_owned(),
            description: "Echo tool".to_owned(),
            parameters: parse(case.schema).into(),
            constrained_sampling: None,
        };
        let JsonValue::Object(arguments) = parse(case.args) else {
            panic!("{}: arguments are an object", case.name);
        };
        let call = ToolCall {
            id: "tool-1".to_owned(),
            name: "echo".to_owned(),
            arguments,
            ..ToolCall::default()
        };
        let actual = validate_tool_arguments(&tool, &call);
        let expected = match case.expected {
            Expected::Ok(value) => Ok(parse(value)),
            Expected::Invalid(message) => Err(ValidationError::InvalidArguments {
                message: message.to_owned(),
            }),
            Expected::Thrown(kind, message) => Err(ValidationError::Thrown {
                kind,
                message: message.to_owned(),
            }),
        };
        assert_eq!(actual, expected, "case {}", case.name);
        if let Ok(value) = &actual {
            // Key order is observable (`JSON.stringify` of the result).
            assert_eq!(
                serde_json::to_string(value).ok(),
                expected
                    .ok()
                    .map(|value| serde_json::to_string(&value).unwrap_or_default()),
                "case {}",
                case.name
            );
        }
    }
}

const FORMATS: &[(&str, &str, bool)] = &[
    ("date", "2020-02-29", true),
    ("date", "2021-02-29", false),
    ("date", "2020-13-01", false),
    ("date", "0000-01-01", true),
    ("date-time", "2020-12-12T20:20:40+00:00", true),
    ("date-time", "2020-12-12t20:20:40z", true),
    ("date-time", "2020-12-12T20:20:40", false),
    ("date-time", "2020-12-12T20:20:40.123Z", true),
    ("time", "23:59:60Z", true),
    ("time", "22:59:60Z", false),
    ("time", "23:59:60+01:00", false),
    ("time", "22:59:60-01:00", true),
    ("time", "24:00:00Z", false),
    ("time", "12:00:00+24:00", false),
    ("duration", "P1Y2M", true),
    ("duration", "PT", false),
    ("duration", "P1W", true),
    ("email", "a@b.co", true),
    ("email", "a@", false),
    ("email", "\"quoted\"@x.org", true),
    ("email", "\u{17f}@x.org", false),
    ("email", "A@B.CO", true),
    (
        "idn-email",
        "\u{7528}\u{6237}@\u{4f8b}\u{5b50}.\u{5e7f}\u{544a}",
        true,
    ),
    ("idn-email", "a@-b.c", false),
    ("hostname", "example.com", true),
    ("hostname", "xn--mnchen-3ya.de", true),
    ("hostname", "example.com.", false),
    ("hostname", "-bad.com", false),
    ("hostname", "ab--c.com", false),
    (
        "hostname",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        false,
    ),
    ("hostname", "xn--a", false),
    ("hostname", "XN--MNCHEN-3YA.de", true),
    ("idn-hostname", "m\u{fc}nchen.de", true),
    (
        "idn-hostname",
        "\u{4f8b}\u{3048}.\u{30c6}\u{30b9}\u{30c8}",
        true,
    ),
    ("idn-hostname", "a b", false),
    ("idn-hostname", "l\u{b7}a", false),
    ("idn-hostname", "l\u{b7}l", true),
    (
        "idn-hostname",
        "\u{ff45}\u{ff58}\u{ff41}\u{ff4d}\u{ff50}\u{ff4c}\u{ff45}\u{3002}com",
        true,
    ),
    ("idn-hostname", "\u{5e9}\u{5dc}\u{5d5}\u{5dd}.com", true),
    ("idn-hostname", "a\u{200d}b", false),
    ("idn-hostname", "\u{300}a", false),
    ("idn-hostname", "xn--4gbrim.xn--ygbi2ammx", true),
    ("ipv4", "192.168.0.1", true),
    ("ipv4", "256.1.1.1", false),
    ("ipv6", "::1", true),
    ("ipv6", "1:2:3:4:5:6:7:8:9", false),
    ("ipv6", "::FFFF:1.2.3.4", true),
    ("uuid", "123e4567-e89b-12d3-a456-426614174000", true),
    ("uuid", "123E4567-E89B-12D3-A456-426614174000", true),
    ("uuid", "nope", false),
    ("uri", "https://example.com/a?b#c", true),
    ("uri", "relative/path", false),
    ("uri", "urn:isbn:0451450523", true),
    ("uri", "http://[::1]:80/", true),
    ("uri-reference", "relative/path", true),
    ("uri-reference", "#frag", true),
    ("uri-reference", "http://exa mple.com", false),
    ("uri-template", "http://example.com/{id}", true),
    ("uri-template", "http://example.com/{id", false),
    ("url", "https://example.com", true),
    ("url", "not a url", false),
    ("url", "mailto:x@y.z", true),
    ("iri", "http://[vF.addr]/x", true),
    ("iri", "http://\u{4f8b}\u{3048}.jp/\u{30d1}\u{30b9}", true),
    ("iri", "http://a b", false),
    ("iri", "http://x/%zz", false),
    ("iri-reference", "//\u{4f8b}\u{3048}.jp", true),
    ("iri-reference", "http//x", false),
    ("iri-reference", "a\\b", false),
    ("regex", "(a", false),
    ("regex", "\\p{L}+", true),
    ("regex", "(?<=a)b", true),
    ("json-pointer", "/a~1b", true),
    ("json-pointer", "a", false),
    ("json-pointer-uri-fragment", "#/a%20b", true),
    ("relative-json-pointer", "0#", true),
    ("relative-json-pointer", "01", false),
];

#[test]
fn format_test_matches_node() {
    for (name, value, expected) in FORMATS {
        assert_eq!(
            format::test(name, value),
            *expected,
            "format {name} {value:?}"
        );
    }
}
