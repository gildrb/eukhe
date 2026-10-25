//! The theme rules (`bend/theme/`, entry `bend/ffi_theme.bend`;
//! `laws/theme.bend`): a theme file read and completed into a palette, or
//! why it is invalid; one load (every file the sources reach read, the
//! theme a name picks, the clashes that warn, the picked file's palette);
//! the colors a shipped theme paints. The caller reads the files and
//! decodes their JSON; a token is its index in `eukhe-theme`'s
//! `Token::ALL`, a color its `[red, green, blue]` channels.

use crate::rules::color::get_rgb;
use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// A JSON value of a theme file, as the rules read it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Json<'a> {
    /// A string, with the index of the file's variable of that name.
    Str { text: &'a str, var: Option<usize> },
    /// A number, as JSON writes it.
    Num(&'a str),
    /// Any other value (null, a bool, an array, an object), as written.
    Other(&'a str),
}

/// A theme file: its name, its variables and colors in key order (each
/// color with the token its key names), and its export page, card and
/// info backgrounds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThemeFile<'a> {
    pub name: &'a str,
    pub vars: Vec<(&'a str, Json<'a>)>,
    pub colors: Vec<(&'a str, Option<u32>, Json<'a>)>,
    pub export: [Option<Json<'a>>; 3],
}

/// A file the sources reach: from the custom directory or not, its stem
/// when that is text, and its theme file (`None`: unreadable, or no theme
/// object).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Source<'a> {
    pub custom: bool,
    pub stem: Option<&'a str>,
    pub file: Option<ThemeFile<'a>>,
}

/// A token's value after variable resolution.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Value {
    /// The terminal default.
    #[default]
    Default,
    /// An xterm-256 index.
    Indexed(u8),
    /// `#rrggbb`.
    Rgb([u8; 3]),
}

/// The number of tokens.
pub const TOKENS: usize = 59;

/// A completed palette: a value per token, the color each token paints,
/// light or dark, the file's own `#rrggbb` background and its export page,
/// card and info backgrounds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Painted {
    pub values: [Value; TOKENS],
    pub paints: [[u8; 3]; TOKENS],
    pub light: bool,
    pub declared: Option<[u8; 3]>,
    pub export: [Option<[u8; 3]>; 3],
}

/// Why a value is no color.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Why {
    Circular(String),
    NotFound(String),
    BadHex(String),
    BadValue(String),
}

/// Why a theme file is invalid.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fault {
    /// A color key that names no token.
    Unknown(String),
    /// A color whose value is no color.
    InColor(String, Why),
    /// The required tokens the file does not write, in token order.
    Missing(Vec<u32>),
    /// An export background (0 page, 1 card, 2 info) whose value is no
    /// color.
    InExport(usize, Why),
}

impl Fault {
    /// The reason a user reads; `token` names a token.
    #[must_use]
    pub fn reason(&self, token: impl Fn(u32) -> String) -> String {
        match self {
            Fault::Unknown(key) => format!("unknown color token: {key}"),
            Fault::InColor(key, why) => format!("color \"{key}\": {}", why.reason()),
            Fault::Missing(tokens) => format!(
                "missing required color tokens: {}",
                tokens
                    .iter()
                    .map(|t| token(*t))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Fault::InExport(at, why) => {
                let key = ["pageBg", "cardBg", "infoBg"].get(*at).unwrap_or(&"?");
                format!("export \"{key}\": {}", why.reason())
            }
        }
    }
}

impl Why {
    fn reason(&self) -> String {
        match self {
            Why::Circular(name) => format!("Circular variable reference detected: {name}"),
            Why::NotFound(name) => format!("Variable reference not found: {name}"),
            Why::BadHex(text) => format!("Invalid hex color: {text}"),
            Why::BadValue(text) => format!("Invalid color value: {text}"),
        }
    }
}

/// A theme file read and completed: its palette, or why it is invalid.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Parsed {
    Rejected(Fault),
    Painted(Box<Painted>),
}

/// Why a name picks no theme.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cause {
    /// The file at this index did not load and blames the name.
    Failed(usize),
    NotFound,
}

/// How a file the sources reach read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Loaded,
    Invalid(Fault),
    NoTheme,
}

/// The theme a name picks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pick {
    /// The builtin at this index (0 eukhe, the default theme; 1 dark;
    /// 2 light).
    Builtin(usize),
    /// The file at this index, and its palette.
    File(usize, Box<Painted>),
}

/// What a name resolves to over the files the sources reach.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resolution {
    /// The theme picked.
    pub theme: Pick,
    /// The name warns: it picks no theme.
    pub warned: bool,
    /// Why it picks none (when it warns).
    pub cause: Option<Cause>,
    /// Each file whose name an earlier file took and whose palette differs
    /// from that file's, with that file.
    pub clashes: Vec<(usize, usize)>,
    /// The other files that did not load.
    pub broken: Vec<usize>,
    /// How each file read.
    pub outcomes: Vec<Outcome>,
}

/// The palette `file` completes to, or why it is invalid.
#[must_use]
pub fn load(file: &ThemeFile<'_>) -> Parsed {
    expect_core(Entry::Theme, load_call(file))
}

/// What `name` (empty: the default theme) resolves to over `sources`, in
/// load order (the registered files, then the custom directory's).
#[must_use]
pub fn resolve(name: &str, sources: &[Source<'_>]) -> Resolution {
    expect_core(Entry::Theme, resolve_call(name, sources))
}

/// The color each token of the shipped theme `index` (0 eukhe, 1 dark,
/// 2 light) paints.
#[must_use]
pub fn shipped(index: u32) -> Vec<[u8; 3]> {
    expect_core(Entry::Theme, shipped_call(index))
}

fn load_call(file: &ThemeFile<'_>) -> Result<Parsed, Error> {
    let mut w = Writer::new();
    w.tag(0);
    put_file(&mut w, file);
    let reply = call(Entry::Theme, &w.finish()?)?;
    let mut r = Reader::reply(&reply)?;
    let parsed = get_parsed(&mut r)?;
    r.end()?;
    Ok(parsed)
}

fn resolve_call(name: &str, sources: &[Source<'_>]) -> Result<Resolution, Error> {
    let mut w = Writer::new();
    w.tag(1).str(name).count(sources.len());
    for source in sources {
        w.bool(source.custom);
        match source.stem {
            Some(stem) => w.some().str(stem),
            None => w.none(),
        };
        match &source.file {
            Some(file) => {
                w.some();
                put_file(&mut w, file);
            }
            None => {
                w.none();
            }
        }
    }
    let reply = call(Entry::Theme, &w.finish()?)?;
    let mut r = Reader::reply(&reply)?;
    let theme = r.u32()?;
    let warned = r.bool()?;
    let cause = if r.maybe()? {
        Some(match r.tag_of(2, "a cause")? {
            0 => Cause::Failed(r.count()?),
            _ => Cause::NotFound,
        })
    } else {
        None
    };
    let clashes = (0..r.count()?)
        .map(|_| Ok((r.count()?, r.count()?)))
        .collect::<Result<Vec<_>, WireError>>()?;
    let broken = (0..r.count()?)
        .map(|_| r.count())
        .collect::<Result<Vec<_>, _>>()?;
    let outcomes = (0..r.count()?)
        .map(|_| {
            Ok(match r.tag_of(3, "an outcome")? {
                0 => Outcome::Loaded,
                1 => Outcome::Invalid(get_fault(&mut r)?),
                _ => Outcome::NoTheme,
            })
        })
        .collect::<Result<Vec<_>, WireError>>()?;
    let picked = if r.maybe()? {
        Some(get_parsed(&mut r)?)
    } else {
        None
    };
    r.end()?;
    let theme = match (theme.checked_sub(3), picked) {
        (None, None) => Pick::Builtin(usize::try_from(theme).unwrap_or(0)),
        (Some(at), Some(Parsed::Painted(palette))) => {
            Pick::File(usize::try_from(at).unwrap_or(usize::MAX), palette)
        }
        (None | Some(_), Some(Parsed::Rejected(_)) | None) | (None, Some(Parsed::Painted(_))) => {
            return Err(WireError::Malformed {
                at: 0,
                expected: "a builtin, or a file with its palette",
            }
            .into())
        }
    };
    Ok(Resolution {
        theme,
        warned,
        cause,
        clashes,
        broken,
        outcomes,
    })
}

fn shipped_call(index: u32) -> Result<Vec<[u8; 3]>, Error> {
    let reply = call(Entry::Theme, &Writer::new().tag(2).tag(index).finish()?)?;
    let mut r = Reader::reply(&reply)?;
    let colors = (0..r.count()?)
        .map(|_| get_rgb(&mut r))
        .collect::<Result<Vec<_>, _>>()?;
    r.end()?;
    Ok(colors)
}

fn put_json(w: &mut Writer, json: Json<'_>) {
    match json {
        Json::Str { text, var } => {
            w.tag(0).str(text);
            match var {
                Some(i) => w.some().count(i),
                None => w.none(),
            };
        }
        Json::Num(text) => {
            w.tag(1).str(text);
        }
        Json::Other(text) => {
            w.tag(2).str(text);
        }
    }
}

fn put_file(w: &mut Writer, file: &ThemeFile<'_>) {
    w.str(file.name).count(file.vars.len());
    for &(name, value) in &file.vars {
        w.str(name);
        put_json(w, value);
    }
    w.count(file.colors.len());
    for &(key, token, value) in &file.colors {
        w.str(key);
        match token {
            Some(t) => w.some().u32(t),
            None => w.none(),
        };
        put_json(w, value);
    }
    for value in file.export {
        match value {
            Some(json) => {
                w.some();
                put_json(w, json);
            }
            None => {
                w.none();
            }
        }
    }
}

fn get_mrgb(r: &mut Reader<'_>) -> Result<Option<[u8; 3]>, WireError> {
    Ok(if r.maybe()? { Some(get_rgb(r)?) } else { None })
}

fn get_why(r: &mut Reader<'_>) -> Result<Why, WireError> {
    let tag = r.tag_of(4, "why a value is no color")?;
    let text = r.str()?.to_string();
    Ok(match tag {
        0 => Why::Circular(text),
        1 => Why::NotFound(text),
        2 => Why::BadHex(text),
        _ => Why::BadValue(text),
    })
}

fn get_fault(r: &mut Reader<'_>) -> Result<Fault, WireError> {
    Ok(match r.tag_of(4, "why a file is invalid")? {
        0 => Fault::Unknown(r.str()?.to_string()),
        1 => Fault::InColor(r.str()?.to_string(), get_why(r)?),
        2 => Fault::Missing(
            (0..r.count()?)
                .map(|_| r.u32())
                .collect::<Result<Vec<_>, _>>()?,
        ),
        _ => {
            let at = usize::try_from(r.tag_of(3, "an export background")?).unwrap_or(0);
            Fault::InExport(at, get_why(r)?)
        }
    })
}

fn get_value(r: &mut Reader<'_>) -> Result<Value, WireError> {
    Ok(match r.tag_of(3, "a value")? {
        0 => Value::Default,
        1 => Value::Indexed(u8::try_from(r.u32()?).map_err(|_| WireError::Malformed {
            at: 0,
            expected: "an xterm-256 index",
        })?),
        _ => Value::Rgb(get_rgb(r)?),
    })
}

/// A value per token: a count of [`TOKENS`], then each value.
fn get_tokens<T: Copy + Default>(
    r: &mut Reader<'_>,
    item: fn(&mut Reader<'_>) -> Result<T, WireError>,
) -> Result<[T; TOKENS], WireError> {
    if r.count()? != TOKENS {
        return Err(WireError::Malformed {
            at: 0,
            expected: "a value per token",
        });
    }
    let mut out = [T::default(); TOKENS];
    for slot in &mut out {
        *slot = item(r)?;
    }
    Ok(out)
}

fn get_parsed(r: &mut Reader<'_>) -> Result<Parsed, WireError> {
    if r.tag_of(2, "a parse")? == 0 {
        return Ok(Parsed::Rejected(get_fault(r)?));
    }
    let values = get_tokens(r, get_value)?;
    let paints = get_tokens(r, get_rgb)?;
    let light = r.bool()?;
    let declared = get_mrgb(r)?;
    let export = [get_mrgb(r)?, get_mrgb(r)?, get_mrgb(r)?];
    Ok(Parsed::Painted(Box::new(Painted {
        values,
        paints,
        light,
        declared,
        export,
    })))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The core is reached: a file whose key names no token is rejected
    /// with that key; a name no file advertises is the default theme with
    /// a warning; the shipped eukhe theme paints 59 colors.
    #[test]
    fn the_core_answers() {
        let file = ThemeFile {
            name: "x",
            vars: Vec::new(),
            colors: vec![("zz", None, Json::Num("3"))],
            export: [None, None, None],
        };
        assert_eq!(load(&file), Parsed::Rejected(Fault::Unknown("zz".into())));
        assert_eq!(
            resolve("dusk", &[]),
            Resolution {
                theme: Pick::Builtin(0),
                warned: true,
                cause: Some(Cause::NotFound),
                clashes: Vec::new(),
                broken: Vec::new(),
                outcomes: Vec::new(),
            }
        );
        assert_eq!(shipped(0).len(), 59);
    }
}
