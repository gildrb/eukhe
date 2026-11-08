//! Charitable argument repair (omp ADR 0020; `bend/arg_repair.bend`, entry
//! `bend/ffi_arg_repair.bend`; `laws/arg_repair.bend`, spec
//! `spec/harness/arguments.bend`): strict on a tool's contract, charitable
//! on the model's dialect. The caller decodes the JSON and reads each sent
//! argument (its key's JSON string decoding, a string's f64 and container
//! readings); the core decides every key and every value and records each
//! change, or refuses the call. Containers never cross the wire: this
//! module keeps every sent value and reading and builds the repaired
//! arguments from the core's answer.

use eukhe_types::pi_ai::{JsonObject, JsonValue};

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// A string's text crosses the wire when it has at most this many chars; a
/// longer string spells no boolean and no integer (its other readings
/// still count).
pub const SPELL_MAX: usize = 4096;

/// A declared argument: its name, its `type` and its `items.type` (each
/// `None` when absent or not a string).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Prop<'a> {
    pub name: &'a str,
    pub kind: Option<&'a str>,
    pub items: Option<&'a str>,
}

/// The tool's parameters: its declared arguments in order, and whether the
/// schema is closed (`additionalProperties: false`).
#[derive(Clone, Debug)]
pub struct Schema<P> {
    pub props: P,
    pub closed: bool,
}

/// The dialect a tool declares: `(alias, canonical)` pairs it accepts and
/// `(key, hint)` pairs it refuses, each in order.
#[derive(Clone, Debug)]
pub struct Dialect<A, R> {
    pub aliases: A,
    pub refused: R,
}

/// What a string's trimmed text opens with, and the container Rust's JSON
/// reader (with repair) reads it as.
#[derive(Clone, Debug, Default, PartialEq)]
pub enum Container {
    /// It opens with neither `{` nor `[`.
    #[default]
    Plain,
    /// It opens with `{`; the object it reads as.
    Brace(Option<JsonObject>),
    /// It opens with `[`; the array it reads as.
    Bracket(Option<Vec<JsonValue>>),
}

/// What the caller read in a string value's trimmed text (the default for
/// any other value, which ignores it).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Reading {
    /// The number its f64 reading is (`str::parse::<f64>`, finite).
    pub number: Option<JsonValue>,
    pub container: Container,
}

/// A sent argument: its key, the key with its JSON string encoding removed
/// (`None`: the key is no JSON string), its value and the readings of it.
#[derive(Clone, Debug, PartialEq)]
pub struct Arg {
    pub key: String,
    pub plain: Option<String>,
    pub value: JsonValue,
    pub reading: Reading,
}

/// One applied repair.
#[derive(Clone, Debug, PartialEq)]
pub enum Record {
    /// A key read as another name (an alias, or a key in a JSON string).
    Alias { from: String, to: String },
    /// A value read as the value the schema declares.
    Coercion {
        key: String,
        from: JsonValue,
        to: JsonValue,
    },
}

/// Why no repair makes the arguments valid.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// A key of another dialect, with the hint that teaches this one; an
    /// alias whose canonical name is refused names that name.
    Refused { key: String, hint: String },
    /// A key a closed schema does not declare, no alias of a declared one;
    /// an alias whose canonical name it does not declare names that name.
    Unknown { key: String, valid: Vec<String> },
    /// Two keys read as one name: the name, the key sent first, this key.
    Ambiguous {
        canonical: String,
        first: String,
        key: String,
    },
}

/// The core's decision on a call.
#[derive(Clone, Debug, PartialEq)]
pub enum Verdict {
    /// The arguments in the tool's dialect, with one record per change.
    Repaired {
        arguments: JsonObject,
        records: Vec<Record>,
    },
    Rejected(Refusal),
}

/// The arguments `args` in `dialect` of `schema`, decided by the compiled
/// core.
///
/// # Errors
///
/// [`WireError::StrTooLong`] when a key, a name or a hint is longer than
/// the wire carries (the call cannot be read; nothing is decided).
pub fn repair<'a, P, A, R>(
    schema: Schema<P>,
    dialect: Dialect<A, R>,
    args: Vec<Arg>,
) -> Result<Verdict, WireError>
where
    P: ExactSizeIterator<Item = Prop<'a>>,
    A: ExactSizeIterator<Item = (&'a str, &'a str)>,
    R: ExactSizeIterator<Item = (&'a str, &'a str)>,
{
    let request = request(schema, dialect, &args)?;
    Ok(expect_core(Entry::ArgRepair, decide(&request, args)))
}

fn request<'a, P, A, R>(
    schema: Schema<P>,
    dialect: Dialect<A, R>,
    args: &[Arg],
) -> Result<String, WireError>
where
    P: ExactSizeIterator<Item = Prop<'a>>,
    A: ExactSizeIterator<Item = (&'a str, &'a str)>,
    R: ExactSizeIterator<Item = (&'a str, &'a str)>,
{
    let mut writer = Writer::new();
    writer.count(schema.props.len());
    for prop in schema.props {
        writer.str(prop.name);
        maybe_str(&mut writer, prop.kind);
        maybe_str(&mut writer, prop.items);
    }
    writer.bool(schema.closed);
    put_pairs(&mut writer, dialect.aliases);
    put_pairs(&mut writer, dialect.refused);
    writer.count(args.len());
    for arg in args {
        writer.str(&arg.key);
        maybe_str(&mut writer, arg.plain.as_deref());
        put_value(&mut writer, &arg.value, &arg.reading);
    }
    writer.finish()
}

fn put_pairs<'a>(writer: &mut Writer, pairs: impl ExactSizeIterator<Item = (&'a str, &'a str)>) {
    writer.count(pairs.len());
    for (key, text) in pairs {
        writer.str(key).str(text);
    }
}

fn maybe_str(writer: &mut Writer, value: Option<&str>) {
    match value {
        Some(text) => writer.some().str(text),
        None => writer.none(),
    };
}

fn put_value(writer: &mut Writer, value: &JsonValue, reading: &Reading) {
    match value {
        JsonValue::Null => {
            writer.tag(0);
        }
        JsonValue::Bool(b) => {
            writer.tag(1).bool(*b);
        }
        JsonValue::Number(number) => {
            writer.tag(2).str(&number.to_string());
        }
        JsonValue::String(text) => {
            writer.tag(3);
            let short = text.chars().nth(SPELL_MAX).is_none();
            maybe_str(writer, short.then_some(text.as_str()));
            match &reading.number {
                Some(number) => writer.some().str(&number.to_string()),
                None => writer.none(),
            };
            match &reading.container {
                Container::Plain => writer.tag(0),
                Container::Brace(object) => writer.tag(1).bool(object.is_some()),
                Container::Bracket(array) => writer.tag(2).bool(array.is_some()),
            };
        }
        JsonValue::Array(_) => {
            writer.tag(4);
        }
        JsonValue::Object(_) => {
            writer.tag(5);
        }
    }
}

/// A value read as the declared type, as the core answers it.
enum To {
    Value(JsonValue),
    One,
    Object,
    Array,
}

fn malformed(expected: &'static str) -> WireError {
    WireError::Malformed { at: 0, expected }
}

fn decide(request: &str, args: Vec<Arg>) -> Result<Verdict, Error> {
    let reply = call(Entry::ArgRepair, request)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = if reader.tag_of(2, "an argument repair verdict")? == 0 {
        if reader.count()? != args.len() {
            return Err(malformed("one out per sent argument").into());
        }
        let mut arguments = JsonObject::new();
        let mut coerced = Vec::new();
        for Arg { value, reading, .. } in args {
            let key = reader.str()?.to_owned();
            let value = if reader.maybe()? {
                let to = materialize(read_to(&mut reader)?, &value, reading.container)?;
                coerced.push((key.clone(), value, to.clone()));
                to
            } else {
                value
            };
            arguments.insert(key, value);
        }
        let count = reader.count()?;
        let mut records = Vec::with_capacity(count);
        for _ in 0..count {
            records.push(if reader.tag_of(2, "an argument repair record")? == 0 {
                Record::Alias {
                    from: reader.str()?.to_owned(),
                    to: reader.str()?.to_owned(),
                }
            } else {
                let name = reader.str()?;
                let at = coerced
                    .iter()
                    .position(|(key, _, _)| key == name)
                    .ok_or_else(|| malformed("the name of a value read"))?;
                let (key, from, to) = coerced.swap_remove(at);
                Record::Coercion { key, from, to }
            });
        }
        Verdict::Repaired { arguments, records }
    } else {
        Verdict::Rejected(match reader.tag_of(3, "an argument refusal")? {
            0 => Refusal::Refused {
                key: reader.str()?.to_owned(),
                hint: reader.str()?.to_owned(),
            },
            1 => {
                let key = reader.str()?.to_owned();
                let count = reader.count()?;
                let mut valid = Vec::with_capacity(count);
                for _ in 0..count {
                    valid.push(reader.str()?.to_owned());
                }
                Refusal::Unknown { key, valid }
            }
            // `tag_of` answers a tag below 3: this is 2.
            _ => Refusal::Ambiguous {
                canonical: reader.str()?.to_owned(),
                first: reader.str()?.to_owned(),
                key: reader.str()?.to_owned(),
            },
        })
    };
    reader.end()?;
    Ok(verdict)
}

fn read_to(reader: &mut Reader<'_>) -> Result<To, WireError> {
    Ok(
        match reader.tag_of(6, "a value read as the declared type")? {
            0 => To::Value(JsonValue::Bool(reader.bool()?)),
            1 => {
                let number: JsonValue = reader
                    .str()?
                    .parse()
                    .map_err(|_| malformed("the JSON text of a number"))?;
                if !number.is_number() {
                    return Err(malformed("the JSON text of a number"));
                }
                To::Value(number)
            }
            2 => To::Value(JsonValue::String(reader.str()?.to_owned())),
            3 => To::One,
            4 => To::Object,
            // `tag_of` answers a tag below 6: this is 5.
            _ => To::Array,
        },
    )
}

/// The value `to` stands for, from the sent value and the container its
/// text reads as.
fn materialize(to: To, sent: &JsonValue, container: Container) -> Result<JsonValue, WireError> {
    match (to, container) {
        (To::Value(value), _) => Ok(value),
        (To::One, _) => Ok(JsonValue::Array(vec![sent.clone()])),
        (To::Object, Container::Brace(Some(object))) => Ok(JsonValue::Object(object)),
        (To::Array, Container::Bracket(Some(array))) => Ok(JsonValue::Array(array)),
        (
            To::Object | To::Array,
            Container::Plain | Container::Brace(_) | Container::Bracket(_),
        ) => Err(malformed("a container the sent string reads as")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text(value: &str) -> JsonValue {
        JsonValue::String(value.to_owned())
    }

    fn arg(key: &str, value: JsonValue) -> Arg {
        Arg {
            key: key.to_owned(),
            plain: None,
            value,
            reading: Reading::default(),
        }
    }

    fn decide(args: Vec<Arg>) -> Verdict {
        let props = [
            Prop {
                name: "on",
                kind: Some("boolean"),
                items: None,
            },
            Prop {
                name: "paths",
                kind: Some("array"),
                items: Some("string"),
            },
        ];
        repair(
            Schema {
                props: props.into_iter(),
                closed: true,
            },
            Dialect {
                aliases: [("dirs", "paths")].into_iter(),
                refused: [].into_iter(),
            },
            args,
        )
        .unwrap()
    }

    /// The core reads a padded boolean and an alias holding a lone string,
    /// one record per change; a string past `SPELL_MAX` chars crosses
    /// without its text, so it spells no boolean.
    #[test]
    fn the_core_reads_spellings_up_to_spell_max() {
        let padded = format!("{}yes", " ".repeat(SPELL_MAX - 3));
        let long = format!("{}yes", " ".repeat(SPELL_MAX - 2));
        assert_eq!(
            decide(vec![arg("on", text(&padded)), arg("dirs", text("src"))]),
            Verdict::Repaired {
                arguments: JsonObject::from_iter([
                    ("on".to_owned(), JsonValue::Bool(true)),
                    ("paths".to_owned(), JsonValue::Array(vec![text("src")])),
                ]),
                records: vec![
                    Record::Coercion {
                        key: "on".to_owned(),
                        from: text(&padded),
                        to: JsonValue::Bool(true),
                    },
                    Record::Alias {
                        from: "dirs".to_owned(),
                        to: "paths".to_owned(),
                    },
                    Record::Coercion {
                        key: "paths".to_owned(),
                        from: text("src"),
                        to: JsonValue::Array(vec![text("src")]),
                    },
                ],
            }
        );
        assert_eq!(
            decide(vec![arg("on", text(&long))]),
            Verdict::Repaired {
                arguments: JsonObject::from_iter([("on".to_owned(), text(&long))]),
                records: Vec::new(),
            }
        );
        assert_eq!(
            decide(vec![arg("off", JsonValue::Null)]),
            Verdict::Rejected(Refusal::Unknown {
                key: "off".to_owned(),
                valid: vec!["on".to_owned(), "paths".to_owned()],
            })
        );
    }

    /// An alias's canonical name is admitted as that name sent would be: a
    /// closed schema that does not declare it, or a dialect that refuses
    /// it, rejects the call naming the canonical name.
    #[test]
    fn an_alias_is_admitted_as_its_canonical_name_sent() {
        let command = [Prop {
            name: "command",
            kind: Some("string"),
            items: None,
        }];
        assert_eq!(
            repair(
                Schema {
                    props: command.into_iter(),
                    closed: true,
                },
                Dialect {
                    aliases: [("file_path", "path")].into_iter(),
                    refused: [].into_iter(),
                },
                vec![arg("file_path", text("a.rs"))],
            )
            .unwrap(),
            Verdict::Rejected(Refusal::Unknown {
                key: "path".to_owned(),
                valid: vec!["command".to_owned()],
            })
        );
        let old_string = [Prop {
            name: "old_string",
            kind: None,
            items: None,
        }];
        assert_eq!(
            repair(
                Schema {
                    props: old_string.into_iter(),
                    closed: true,
                },
                Dialect {
                    aliases: [("old_str", "old_string")].into_iter(),
                    refused: [("old_string", "send a hashline patch")].into_iter(),
                },
                vec![arg("old_str", text("x"))],
            )
            .unwrap(),
            Verdict::Rejected(Refusal::Refused {
                key: "old_string".to_owned(),
                hint: "send a hashline patch".to_owned(),
            })
        );
    }
}
