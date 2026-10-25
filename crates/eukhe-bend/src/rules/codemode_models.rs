//! What code mode scripts get wrong when they call the `models.*` globals,
//! and the texts of those calls (`bend/codemode_models.bend`, entry
//! `bend/ffi_codemode_models.bend`; `laws/codemode_models/`). The caller
//! reads a script's JSON values and gives only what the checks read
//! ([`Desc`]: a value's kind, an array's emptiness, an object's keys in
//! order; a string's text where a check compares it; serde's JSON text of a
//! value an error prints) and, for a named model, what the catalog finds
//! under its provider and id. The core decides every check, which error
//! wins and its exact text, which model a call uses, what a catalog call
//! does with its arguments, which global runs which model call, and the
//! texts of a call's result and of a context serde cannot read.

use eukhe_types::pi_ai::ModelType;

use crate::wire::{Reader, WireError, Writer};
use crate::{call, Entry, Error};

/// What a check reads of a script's JSON value (`Mod.Desc`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Desc<'a> {
    /// Absent (`undefined`).
    Undefined,
    /// `null`.
    Null,
    /// A boolean.
    Boolean,
    /// A number.
    Number,
    /// A string.
    String,
    /// An array, and whether it is empty.
    Array {
        /// It has no items.
        empty: bool,
    },
    /// An object: its keys in order.
    Object(Vec<&'a str>),
}

/// An item of a classifier context's `images` or an images context's
/// `input` (`Mod.Blk`); the fields are [`Desc::Undefined`] and `None` when
/// the item is no object.
#[derive(Clone, Debug)]
pub struct Block<'a> {
    /// The item.
    pub block: Desc<'a>,
    /// Its `type`, when a string.
    pub kind: Option<&'a str>,
    /// Its `text`.
    pub text: Desc<'a>,
    /// Its `data`.
    pub data: Desc<'a>,
    /// Its `mimeType`.
    pub mime_type: Desc<'a>,
}

/// A question of a classifier context's `questions` (`Mod.Q`); the fields
/// are [`Desc::Undefined`], `None` and `undefined` when the question is no
/// object.
#[derive(Clone, Debug)]
pub struct Question<'a> {
    /// Its id (its key in `questions`).
    pub id: &'a str,
    /// The question.
    pub question: Desc<'a>,
    /// Its `instructions`.
    pub instructions: Desc<'a>,
    /// Its `type`, when a string.
    pub kind: Option<&'a str>,
    /// Its `type`'s JSON text (`JSON.stringify`; `undefined` when absent).
    pub kind_json: String,
    /// Its `criteria`.
    pub criteria: Desc<'a>,
    /// The criteria's values in order when an object, its items when an
    /// array, else none.
    pub values: Vec<Desc<'a>>,
    /// The criteria's `true` (when an object).
    pub yes: Desc<'a>,
    /// The criteria's `false` (when an object).
    pub no: Desc<'a>,
}

/// `models.classify()`'s context (`Mod.Ctx`); the fields are
/// [`Desc::Undefined`] and empty when the context is no object.
#[derive(Clone, Debug)]
pub struct ClassifierContext<'a> {
    /// The context.
    pub context: Desc<'a>,
    /// Its `state`.
    pub state: Desc<'a>,
    /// Its `images`.
    pub images: Desc<'a>,
    /// Its `images` items, when an array.
    pub image_items: Vec<Block<'a>>,
    /// Its `questions`.
    pub questions: Desc<'a>,
    /// Its questions, when `questions` is an object, in its order.
    pub question_items: Vec<Question<'a>>,
}

/// `models.generateImages()`'s context (`Mod.ICtx`).
#[derive(Clone, Debug)]
pub struct ImagesContext<'a> {
    /// The context.
    pub context: Desc<'a>,
    /// Its `input`.
    pub input: Desc<'a>,
    /// Its `input` items, when an array.
    pub blocks: Vec<Block<'a>>,
}

/// A model call of scripts (`Mod.Call`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModelCall {
    /// `models.classify`: a classifier.
    Classify,
    /// `models.generateImages`: an image model.
    GenerateImages,
}

/// The model argument of a model call (`Mod.Res`, without the lookups).
#[derive(Clone, Debug)]
pub struct ModelArg<'a> {
    /// The call.
    pub call: ModelCall,
    /// The session resolves a default classifier.
    pub default_classifier: bool,
    /// The model argument.
    pub model: Desc<'a>,
    /// Its `provider`, when it is an object and that is a string.
    pub provider: Option<&'a str>,
    /// Its `id`, when it is an object and that is a string.
    pub id: Option<&'a str>,
}

/// What the catalog finds under the model's provider and id, per type
/// asked: the found model's own type and the model (all `None` unless both
/// are strings).
#[derive(Clone, Debug)]
pub struct Lookups<M> {
    /// Asked as a chat model.
    pub chat: Option<(ModelType, M)>,
    /// Asked as an image model.
    pub image: Option<(ModelType, M)>,
    /// Asked as a classifier.
    pub classifier: Option<(ModelType, M)>,
}

/// Which model a call uses (`Mod.RAns`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Resolved<M> {
    /// None: the script's error.
    Failed(String),
    /// The session's default classifier.
    Default,
    /// The model the catalog found under the call's type.
    Found(M),
}

/// A catalog call: the global and its spread arguments (`Mod.Cat`).
#[derive(Clone, Debug)]
pub struct CatalogArgs<'a> {
    /// The global's name.
    pub global: &'a str,
    /// The arguments.
    pub args: Vec<Desc<'a>>,
    /// The first argument, when a string.
    pub kind: Option<&'a str>,
    /// The first argument's JSON text (`undefined` when absent).
    pub kind_json: String,
    /// The second argument, when a string (the caller's; not sent).
    pub provider: Option<&'a str>,
    /// The third argument, when a string (the caller's; not sent).
    pub id: Option<&'a str>,
}

/// What a catalog call does (`Mod.CAns`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CatalogCall<'a> {
    /// Nothing: the script's error.
    Failed(String),
    /// List the models of a type, of a provider when given.
    Models {
        /// The type.
        model_type: ModelType,
        /// The provider.
        provider: Option<&'a str>,
    },
    /// List those of them with configured auth.
    Available {
        /// The type.
        model_type: ModelType,
        /// The provider.
        provider: Option<&'a str>,
    },
    /// Get one by provider and id.
    One {
        /// The type.
        model_type: ModelType,
        /// The provider.
        provider: &'a str,
        /// The id.
        id: &'a str,
    },
}

/// How a model call ended.
#[derive(Clone, Copy, Debug)]
pub struct Outcome<'a> {
    /// The call.
    pub call: ModelCall,
    /// The model's provider.
    pub provider: &'a str,
    /// The model's id.
    pub id: &'a str,
    /// The stop reason.
    pub stop_reason: &'a str,
    /// The error message, if any.
    pub error_message: Option<&'a str>,
}

/// A model call's result as the tool returns it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Report {
    /// It ended with `stop`.
    pub ok: bool,
    /// Its text.
    pub text: String,
}

fn malformed(expected: &'static str) -> Error {
    WireError::Malformed { at: 0, expected }.into()
}

fn write_desc(w: &mut Writer, d: &Desc<'_>) {
    match d {
        Desc::Undefined => {
            w.tag(0);
        }
        Desc::Null => {
            w.tag(1);
        }
        Desc::Boolean => {
            w.tag(2);
        }
        Desc::Number => {
            w.tag(3);
        }
        Desc::String => {
            w.tag(4);
        }
        Desc::Array { empty } => {
            w.tag(5).bool(*empty);
        }
        Desc::Object(keys) => {
            w.tag(6).count(keys.len());
            for key in keys {
                w.str(key);
            }
        }
    }
}

fn write_descs(w: &mut Writer, ds: &[Desc<'_>]) {
    w.count(ds.len());
    for d in ds {
        write_desc(w, d);
    }
}

fn write_txt(w: &mut Writer, t: Option<&str>) {
    match t {
        None => {
            w.tag(0);
        }
        Some(text) => {
            w.tag(1).str(text);
        }
    }
}

fn write_blocks(w: &mut Writer, bs: &[Block<'_>]) {
    w.count(bs.len());
    for b in bs {
        write_desc(w, &b.block);
        write_txt(w, b.kind);
        write_desc(w, &b.text);
        write_desc(w, &b.data);
        write_desc(w, &b.mime_type);
    }
}

fn write_call(w: &mut Writer, c: ModelCall) {
    w.tag(match c {
        ModelCall::Classify => 0,
        ModelCall::GenerateImages => 1,
    });
}

fn type_tag(t: ModelType) -> u32 {
    match t {
        ModelType::Chat => 0,
        ModelType::Image => 1,
        ModelType::Classifier => 2,
    }
}

fn read_type(r: &mut Reader<'_>) -> Result<ModelType, Error> {
    Ok(match r.tag_of(3, "a model type")? {
        0 => ModelType::Chat,
        1 => ModelType::Image,
        _ => ModelType::Classifier,
    })
}

fn read_call(r: &mut Reader<'_>) -> Result<ModelCall, Error> {
    Ok(match r.tag_of(2, "a model call")? {
        0 => ModelCall::Classify,
        _ => ModelCall::GenerateImages,
    })
}

fn ask(request: &mut Writer) -> Result<String, Error> {
    Ok(call(Entry::CodemodeModels, &request.finish()?)?)
}

fn problem(reply: &str) -> Result<Option<String>, Error> {
    let mut r = Reader::reply(reply)?;
    let found = if r.maybe()? {
        Some(r.str()?.to_owned())
    } else {
        None
    };
    r.end()?;
    Ok(found)
}

/// What is wrong with a classifier context, if anything: the error
/// `models.classify()` throws (`Mod.classify`).
///
/// # Errors
///
/// [`Error::Wire`] when a key or text is past [`crate::wire::STR_MAX`]
/// chars; else only from an inconsistent build (see [`crate::expect_core`]).
pub fn classifier_problem(context: &ClassifierContext<'_>) -> Result<Option<String>, Error> {
    let mut w = Writer::new();
    w.tag(0);
    write_desc(&mut w, &context.context);
    write_desc(&mut w, &context.state);
    write_desc(&mut w, &context.images);
    write_blocks(&mut w, &context.image_items);
    write_desc(&mut w, &context.questions);
    w.count(context.question_items.len());
    for q in &context.question_items {
        w.str(q.id);
        write_desc(&mut w, &q.question);
        write_desc(&mut w, &q.instructions);
        write_txt(&mut w, q.kind);
        w.str(&q.kind_json);
        write_desc(&mut w, &q.criteria);
        write_descs(&mut w, &q.values);
        write_desc(&mut w, &q.yes);
        write_desc(&mut w, &q.no);
    }
    problem(&ask(&mut w)?)
}

/// What is wrong with an images context, if anything: the error
/// `models.generateImages()` throws (`Mod.images`).
///
/// # Errors
///
/// As [`classifier_problem`].
pub fn images_problem(context: &ImagesContext<'_>) -> Result<Option<String>, Error> {
    let mut w = Writer::new();
    w.tag(1);
    write_desc(&mut w, &context.context);
    write_desc(&mut w, &context.input);
    write_blocks(&mut w, &context.blocks);
    problem(&ask(&mut w)?)
}

/// Which model a call uses (`Mod.resolve`), with the models the catalog
/// found.
///
/// # Errors
///
/// As [`classifier_problem`]; [`WireError::Malformed`] when the core picks a
/// model the lookups do not hold (an inconsistent build).
pub fn resolve<M>(arg: &ModelArg<'_>, found: Lookups<M>) -> Result<Resolved<M>, Error> {
    let mut w = Writer::new();
    w.tag(2);
    write_call(&mut w, arg.call);
    w.bool(arg.default_classifier);
    write_desc(&mut w, &arg.model);
    write_txt(&mut w, arg.provider);
    write_txt(&mut w, arg.id);
    for slot in [&found.chat, &found.image, &found.classifier] {
        match slot {
            None => {
                w.tag(0);
            }
            Some((t, _)) => {
                w.tag(1).tag(type_tag(*t));
            }
        }
    }
    let reply = ask(&mut w)?;
    let mut r = Reader::reply(&reply)?;
    let resolved = match r.tag_of(3, "a resolved model")? {
        0 => Resolved::Failed(r.str()?.to_owned()),
        1 => Resolved::Default,
        _ => {
            let slot = match arg.call {
                ModelCall::Classify => found.classifier,
                ModelCall::GenerateImages => found.image,
            };
            let (_, model) = slot.ok_or_else(|| malformed("a model the catalog found"))?;
            Resolved::Found(model)
        }
    };
    r.end()?;
    Ok(resolved)
}

/// What a catalog call does with its arguments (`Mod.catalog`).
///
/// # Errors
///
/// As [`classifier_problem`]; [`WireError::Malformed`] when the core uses a
/// provider or id the arguments do not hold as strings (an inconsistent
/// build).
pub fn catalog<'a>(args: &CatalogArgs<'a>) -> Result<CatalogCall<'a>, Error> {
    let mut w = Writer::new();
    w.tag(3).str(args.global);
    write_descs(&mut w, &args.args);
    write_txt(&mut w, args.kind);
    w.str(&args.kind_json);
    let reply = ask(&mut w)?;
    let mut r = Reader::reply(&reply)?;
    let provider = |given: bool| -> Result<Option<&'a str>, Error> {
        if given {
            args.provider
                .map(Some)
                .ok_or_else(|| malformed("a provider string"))
        } else {
            Ok(None)
        }
    };
    let answer = match r.tag_of(4, "a catalog call")? {
        0 => CatalogCall::Failed(r.str()?.to_owned()),
        1 => {
            let model_type = read_type(&mut r)?;
            CatalogCall::Models {
                model_type,
                provider: provider(r.bool()?)?,
            }
        }
        2 => {
            let model_type = read_type(&mut r)?;
            CatalogCall::Available {
                model_type,
                provider: provider(r.bool()?)?,
            }
        }
        _ => CatalogCall::One {
            model_type: read_type(&mut r)?,
            provider: args
                .provider
                .ok_or_else(|| malformed("a provider string"))?,
            id: args.id.ok_or_else(|| malformed("an id string"))?,
        },
    };
    r.end()?;
    Ok(answer)
}

/// The model call a script global makes (`Mod.tool`).
///
/// # Errors
///
/// As [`classifier_problem`].
pub fn tool(global: &str) -> Result<Option<ModelCall>, Error> {
    let mut w = Writer::new();
    w.tag(4).str(global);
    let reply = ask(&mut w)?;
    let mut r = Reader::reply(&reply)?;
    let found = if r.maybe()? {
        Some(read_call(&mut r)?)
    } else {
        None
    };
    r.end()?;
    Ok(found)
}

/// A model call's result: whether it ended with `stop`, and its text
/// (`Mod.result`).
///
/// # Errors
///
/// As [`classifier_problem`].
pub fn report(outcome: &Outcome<'_>) -> Result<Report, Error> {
    let mut w = Writer::new();
    w.tag(5);
    write_call(&mut w, outcome.call);
    w.str(outcome.provider)
        .str(outcome.id)
        .str(outcome.stop_reason);
    write_txt(&mut w, outcome.error_message);
    let reply = ask(&mut w)?;
    let mut r = Reader::reply(&reply)?;
    let ok = r.bool()?;
    let text = r.str()?.to_owned();
    r.end()?;
    Ok(Report { ok, text })
}

/// The error of a context serde cannot read: the call and serde's error
/// (`Mod.unread`).
///
/// # Errors
///
/// As [`classifier_problem`].
pub fn unread(call: ModelCall, error: &str) -> Result<String, Error> {
    let mut w = Writer::new();
    w.tag(6);
    write_call(&mut w, call);
    w.str(error);
    let reply = ask(&mut w)?;
    let mut r = Reader::reply(&reply)?;
    let text = r.str()?.to_owned();
    r.end()?;
    Ok(text)
}

/// How many `models.classify()` and `models.generateImages()` calls one
/// script may have in flight (`Mod.max_calls`; the code mode tool's
/// description names the same number).
///
/// # Errors
///
/// Only from an inconsistent build (see [`crate::expect_core`]).
pub fn max_calls() -> Result<usize, Error> {
    let mut w = Writer::new();
    w.tag(7);
    let reply = ask(&mut w)?;
    let mut r = Reader::reply(&reply)?;
    let n = r.count()?;
    r.end()?;
    Ok(n)
}

#[cfg(test)]
mod tests {
    use eukhe_types::pi_ai::ModelType;

    use super::{
        catalog, max_calls, resolve, CatalogArgs, CatalogCall, Desc, Lookups, ModelArg, ModelCall,
        Resolved,
    };

    #[test]
    fn the_codec_carries_the_facts_through_the_core() {
        let args = CatalogArgs {
            global: "models.getModelOfType",
            args: vec![Desc::String, Desc::String, Desc::String],
            kind: Some("chat"),
            kind_json: "\"chat\"".to_owned(),
            provider: Some("faux"),
            id: Some("faux-1"),
        };
        assert_eq!(
            catalog(&args).unwrap(),
            CatalogCall::One {
                model_type: ModelType::Chat,
                provider: "faux",
                id: "faux-1"
            }
        );
        let arg = ModelArg {
            call: ModelCall::Classify,
            default_classifier: false,
            model: Desc::Object(vec!["provider", "id"]),
            provider: Some("faux"),
            id: Some("faux-1"),
        };
        let found = Lookups {
            chat: Some((ModelType::Chat, 1)),
            image: None,
            classifier: Some((ModelType::Classifier, 3)),
        };
        assert_eq!(resolve(&arg, found).unwrap(), Resolved::Found(3));
        assert_eq!(max_calls().unwrap(), 4);
    }
}
