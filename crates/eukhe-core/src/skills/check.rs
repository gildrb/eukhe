//! The checks of a skill file's frontmatter and a prompt template's
//! description run as the compiled Bend core (`bend/skill_load.bend`
//! `check` and `summary`, entry `bend/ffi_skill_load.bend`; laws
//! `skill_ffi_answers` and `skill_ffi_example` in `laws/skill_load.bend`):
//! the skill's name, whether it loads and its messages (the Agent Skills
//! limits: a name of at most 64 bytes of a-z 0-9 '-', its dir's name, a
//! description of at most 1024 bytes that is not blank); a template's
//! description (the frontmatter's, else its body's first line). Rust reads
//! the file and parses the YAML.

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::{Entry, Error};

/// What the loader makes of a skill file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct SkillCheck {
    /// It loads: its description is not blank.
    pub(super) loaded: bool,
    /// Its name: the frontmatter's unless missing or empty, else its dir's.
    pub(super) name: String,
    /// Every message, the description's first.
    pub(super) messages: Vec<String>,
}

fn text(request: &mut Writer, value: Option<&str>) {
    match value {
        None => request.none(),
        Some(value) => request.some().str(value),
    };
}

/// The check of a skill file whose frontmatter has `name` and
/// `description` (each when it is a string), in a dir named `parent`.
///
/// # Errors
///
/// [`Error`] when a string does not fit the wire (more than
/// [`eukhe_bend::wire::STR_MAX`] chars), or from an inconsistent build.
pub(super) fn check_skill(
    name: Option<&str>,
    parent: &str,
    description: Option<&str>,
) -> Result<SkillCheck, Error> {
    let mut request = Writer::new();
    request.tag(0);
    text(&mut request, name);
    request.str(parent);
    text(&mut request, description);
    let reply = eukhe_bend::call(Entry::SkillLoad, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let loaded = reader.bool()?;
    let name = reader.str()?.to_string();
    let count = reader.count()?;
    let mut messages = Vec::with_capacity(count.min(8));
    for _ in 0..count {
        messages.push(reader.str()?.to_string());
    }
    reader.end()?;
    Ok(SkillCheck {
        loaded,
        name,
        messages,
    })
}

/// The description of a template whose frontmatter has `description`
/// (when it is a string), with this `body`.
///
/// # Errors
///
/// As [`check_skill`].
pub(super) fn template_description(description: Option<&str>, body: &str) -> Result<String, Error> {
    let mut request = Writer::new();
    request.tag(1);
    text(&mut request, description);
    request.str(body);
    let reply = eukhe_bend::call(Entry::SkillLoad, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let description = reader.str()?.to_string();
    reader.end()?;
    Ok(description)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The checks come from the compiled core: a name of another dir, with
    /// a hyphen at its end and past 64 bytes (65 bytes: 32 'é' and '-');
    /// a template's description from its body's first line.
    #[test]
    fn the_skill_checks_come_from_the_compiled_core() {
        let long = format!("{}-", "é".repeat(32));
        assert_eq!(
            (
                check_skill(Some(&long), "dir", Some("d")).expect("a check"),
                template_description(None, "\n  hi  \nnext").expect("a description"),
            ),
            (
                SkillCheck {
                    loaded: true,
                    name: long.clone(),
                    messages: vec![
                        format!("name \"{long}\" does not match parent directory \"dir\""),
                        "name exceeds 64 characters (65)".to_string(),
                        "name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)".to_string(),
                        "name must not start or end with a hyphen".to_string(),
                    ],
                },
                "hi".to_string(),
            )
        );
    }
}
