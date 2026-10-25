//! The package sources of `eukhe package` (`bend/package_source.bend`,
//! entry `bend/ffi_package_source.bend`; `laws/package_source.bend`): what a
//! source string is (an `npm:` spec, a git URL, a local path), the parts a
//! git or npm source names, why such a part is refused, and the texts. Rust
//! sends the text and reads the answer.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// The part of a source a refusal names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Part {
    GitHost,
    GitPath,
    GitRef,
    CloneUrl,
    NpmSpec,
    NpmName,
}

/// Why a part is refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Defect {
    Empty,
    EmptySegment,
    DotSegment,
    DrivePrefix,
    Backslash,
    ControlCharacter,
    LeadingDash,
    Slash,
}

/// A refused part and why.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Flaw {
    pub part: Part,
    pub defect: Defect,
}

/// An `npm:` source: the trimmed spec, its package name, whether it pins a
/// version.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Npm {
    pub spec: String,
    pub name: String,
    pub pinned: bool,
}

/// A git source: the clone URL, the host, the repository path, the ref,
/// whether a ref pins it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Git {
    pub repo: String,
    pub host: String,
    pub path: String,
    pub r#ref: Option<String>,
    pub pinned: bool,
}

/// A source's kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    Npm(Npm),
    Git(Git),
    /// The source string as given.
    Local(String),
}

/// The question tags of the entry.
const SOURCE: u32 = 0;
const GIT: u32 = 1;
const LOCAL: u32 = 2;
const NPM_SPEC: u32 = 3;
const PART: u32 = 4;
const DEFECT: u32 = 5;
const ERROR: u32 = 6;

/// A package source string's kind.
///
/// # Errors
///
/// The [`Flaw`] of an `npm:` spec or a git-shaped source with a part that
/// could escape its install root or be read as a command-line option.
pub fn source(text: &str) -> Result<Source, Flaw> {
    expect_core(Entry::PackageSource, source_call(text))
}

/// A source read as a git URL: `None` when it has no git shape.
///
/// # Errors
///
/// The [`Flaw`] of a git-shaped source with an unsafe part.
pub fn git(text: &str) -> Result<Option<Git>, Flaw> {
    expect_core(Entry::PackageSource, git_call(text))
}

/// True when the trimmed value has no `npm:`/`git:`/`github:`/`http:`/
/// `https:`/`ssh:` prefix.
#[must_use]
pub fn is_local(text: &str) -> bool {
    expect_core(Entry::PackageSource, local_call(text))
}

/// An npm spec's name and pinned version.
#[must_use]
pub fn npm_spec(text: &str) -> (String, Option<String>) {
    expect_core(Entry::PackageSource, npm_spec_call(text))
}

/// A part's name.
#[must_use]
pub fn part_text(part: Part) -> String {
    let mut writer = Writer::new();
    put_part(writer.tag(PART), part);
    expect_core(Entry::PackageSource, text_call(&mut writer))
}

/// A defect's words.
#[must_use]
pub fn defect_text(defect: Defect) -> String {
    let mut writer = Writer::new();
    put_defect(writer.tag(DEFECT), defect);
    expect_core(Entry::PackageSource, text_call(&mut writer))
}

/// The text of a refused source.
#[must_use]
pub fn error_text(input: &str, flaw: Flaw) -> String {
    let mut writer = Writer::new();
    put_defect(
        put_part(writer.tag(ERROR).str(input), flaw.part),
        flaw.defect,
    );
    expect_core(Entry::PackageSource, text_call(&mut writer))
}

fn put_part(writer: &mut Writer, part: Part) -> &mut Writer {
    writer.tag(match part {
        Part::GitHost => 0,
        Part::GitPath => 1,
        Part::GitRef => 2,
        Part::CloneUrl => 3,
        Part::NpmSpec => 4,
        Part::NpmName => 5,
    })
}

fn put_defect(writer: &mut Writer, defect: Defect) -> &mut Writer {
    writer.tag(match defect {
        Defect::Empty => 0,
        Defect::EmptySegment => 1,
        Defect::DotSegment => 2,
        Defect::DrivePrefix => 3,
        Defect::Backslash => 4,
        Defect::ControlCharacter => 5,
        Defect::LeadingDash => 6,
        Defect::Slash => 7,
    })
}

fn ask(tag: u32, text: &str) -> Result<String, Error> {
    Ok(call(
        Entry::PackageSource,
        &Writer::new().tag(tag).str(text).finish()?,
    )?)
}

fn text_call(writer: &mut Writer) -> Result<String, Error> {
    let reply = call(Entry::PackageSource, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let text = reader.str()?.to_string();
    reader.end()?;
    Ok(text)
}

fn source_call(text: &str) -> Result<Result<Source, Flaw>, Error> {
    let reply = ask(SOURCE, text)?;
    let mut reader = Reader::reply(&reply)?;
    let answer = if reader.tag_of(2, "a source answer")? == 0 {
        Ok(match reader.tag_of(3, "a source kind")? {
            0 => Source::Npm(Npm {
                spec: reader.str()?.to_string(),
                name: reader.str()?.to_string(),
                pinned: reader.bool()?,
            }),
            1 => Source::Git(read_git(&mut reader)?),
            // `tag_of` answers a tag below 3: this is 2.
            _ => Source::Local(reader.str()?.to_string()),
        })
    } else {
        Err(read_flaw(&mut reader)?)
    };
    reader.end()?;
    Ok(answer)
}

fn git_call(text: &str) -> Result<Result<Option<Git>, Flaw>, Error> {
    let reply = ask(GIT, text)?;
    let mut reader = Reader::reply(&reply)?;
    let answer = match reader.tag_of(3, "a git answer")? {
        0 => Ok(None),
        1 => Ok(Some(read_git(&mut reader)?)),
        // `tag_of` answers a tag below 3: this is 2.
        _ => Err(read_flaw(&mut reader)?),
    };
    reader.end()?;
    Ok(answer)
}

fn local_call(text: &str) -> Result<bool, Error> {
    let reply = ask(LOCAL, text)?;
    let mut reader = Reader::reply(&reply)?;
    let local = reader.bool()?;
    reader.end()?;
    Ok(local)
}

fn npm_spec_call(text: &str) -> Result<(String, Option<String>), Error> {
    let reply = ask(NPM_SPEC, text)?;
    let mut reader = Reader::reply(&reply)?;
    let name = reader.str()?.to_string();
    let version = maybe_str(&mut reader)?;
    reader.end()?;
    Ok((name, version))
}

fn read_git(reader: &mut Reader<'_>) -> Result<Git, WireError> {
    Ok(Git {
        repo: reader.str()?.to_string(),
        host: reader.str()?.to_string(),
        path: reader.str()?.to_string(),
        r#ref: maybe_str(reader)?,
        pinned: reader.bool()?,
    })
}

fn read_flaw(reader: &mut Reader<'_>) -> Result<Flaw, WireError> {
    let part = match reader.tag_of(6, "a source part")? {
        0 => Part::GitHost,
        1 => Part::GitPath,
        2 => Part::GitRef,
        3 => Part::CloneUrl,
        4 => Part::NpmSpec,
        // `tag_of` answers a tag below 6: this is 5.
        _ => Part::NpmName,
    };
    let defect = match reader.tag_of(8, "a source defect")? {
        0 => Defect::Empty,
        1 => Defect::EmptySegment,
        2 => Defect::DotSegment,
        3 => Defect::DrivePrefix,
        4 => Defect::Backslash,
        5 => Defect::ControlCharacter,
        6 => Defect::LeadingDash,
        // `tag_of` answers a tag below 8: this is 7.
        _ => Defect::Slash,
    };
    Ok(Flaw { part, defect })
}

fn maybe_str(reader: &mut Reader<'_>) -> Result<Option<String>, WireError> {
    Ok(if reader.maybe()? {
        Some(reader.str()?.to_string())
    } else {
        None
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The answers come from the compiled core: an `npm:` spec, a git
    /// shorthand with a ref, a refused path, a local path and a text.
    #[test]
    fn the_core_reads_package_sources() {
        assert_eq!(
            source("npm:@scope/pkg@1.2.3"),
            Ok(Source::Npm(Npm {
                spec: "@scope/pkg@1.2.3".to_string(),
                name: "@scope/pkg".to_string(),
                pinned: true,
            }))
        );
        assert_eq!(
            git("git:github.com/user/repo@v1"),
            Ok(Some(Git {
                repo: "https://github.com/user/repo".to_string(),
                host: "github.com".to_string(),
                path: "user/repo".to_string(),
                r#ref: Some("v1".to_string()),
                pinned: true,
            }))
        );
        assert_eq!(
            source("git:git@h.io:../x/y"),
            Err(Flaw {
                part: Part::GitPath,
                defect: Defect::DotSegment,
            })
        );
        assert_eq!(source("./pkg"), Ok(Source::Local("./pkg".to_string())));
        assert!(!is_local(" ssh:x"));
        assert_eq!(npm_spec("pkg@"), ("pkg@".to_string(), None));
        assert_eq!(
            error_text(
                "npm:-x",
                Flaw {
                    part: Part::NpmSpec,
                    defect: Defect::LeadingDash,
                }
            ),
            "Invalid package source npm:-x: npm spec starts with '-'"
        );
    }
}
