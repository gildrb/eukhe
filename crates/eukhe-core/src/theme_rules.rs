//! The theme rules eukhe-theme asks for ([`eukhe_theme::ThemeRules`]): the
//! compiled Bend core's (eukhe-bend `rules::theme`), mapped to and from
//! eukhe-theme's types. eukhe-theme depends on nothing, so the crates that
//! may call the core pass these in.

use eukhe_bend::rules::theme as core;
use eukhe_theme::{
    Cause, Choice, ColorValue, Mode, Outcome, Palette, PaletteParts, Picked, RawSource, RawTheme,
    RawValue, Rgb, ThemeRules, Token,
};

/// The compiled core's theme rules.
pub const THEME_RULES: ThemeRules = ThemeRules { load, resolve };

fn json(value: &RawValue) -> core::Json<'_> {
    match value {
        RawValue::Str { text, var } => core::Json::Str { text, var: *var },
        RawValue::Num(text) => core::Json::Num(text),
        RawValue::Other(text) => core::Json::Other(text),
    }
}

fn file(theme: &RawTheme) -> core::ThemeFile<'_> {
    core::ThemeFile {
        name: &theme.name,
        vars: theme
            .vars
            .iter()
            .map(|(name, v)| (name.as_str(), json(v)))
            .collect(),
        colors: theme
            .colors
            .iter()
            .map(|(key, token, v)| (key.as_str(), token.map(|t| t as u32), json(v)))
            .collect(),
        export: [
            theme.export[0].as_ref().map(json),
            theme.export[1].as_ref().map(json),
            theme.export[2].as_ref().map(json),
        ],
    }
}

fn palette(name: &str, painted: &core::Painted) -> Palette {
    let rgb = |c: Option<[u8; 3]>| c.map(Rgb::from_channels);
    Palette::new(PaletteParts {
        name: name.to_string(),
        colors: painted.values.map(|value| match value {
            core::Value::Default => ColorValue::Default,
            core::Value::Indexed(index) => ColorValue::Indexed(index),
            core::Value::Rgb(c) => ColorValue::Rgb(Rgb::from_channels(c)),
        }),
        paints: painted.paints.map(Rgb::from_channels),
        declared_background: rgb(painted.declared),
        export: painted.export.map(rgb),
        mode: if painted.light {
            Mode::Light
        } else {
            Mode::Dark
        },
    })
}

/// The reason a user reads for `fault`, tokens by their names.
fn reason(fault: &core::Fault) -> String {
    fault.reason(|t| {
        usize::try_from(t)
            .ok()
            .and_then(|at| Token::ALL.get(at))
            .map_or_else(|| t.to_string(), |token| token.name().to_string())
    })
}

fn load(theme: &RawTheme) -> Result<Palette, String> {
    match core::load(&file(theme)) {
        core::Parsed::Rejected(fault) => Err(reason(&fault)),
        core::Parsed::Painted(painted) => Ok(palette(&theme.name, &painted)),
    }
}

fn resolve(name: &str, sources: &[RawSource<'_>]) -> Picked {
    let files: Vec<core::Source<'_>> = sources
        .iter()
        .map(|source| core::Source {
            custom: source.custom,
            stem: source.stem,
            file: source.theme.map(file),
        })
        .collect();
    let resolution = core::resolve(name, &files);
    let theme = match resolution.theme {
        core::Pick::Builtin(at) => Choice::Builtin(at),
        core::Pick::File(at, painted) => {
            let name = sources
                .get(at)
                .and_then(|source| source.theme)
                .map_or("", |theme| theme.name.as_str());
            Choice::File(at, Box::new(palette(name, &painted)))
        }
    };
    Picked {
        theme,
        cause: resolution.cause.map(|cause| match cause {
            core::Cause::Failed(at) => Cause::Failed(at),
            core::Cause::NotFound => Cause::NotFound,
        }),
        clashes: resolution.clashes,
        broken: resolution.broken,
        outcomes: resolution
            .outcomes
            .iter()
            .map(|outcome| match outcome {
                core::Outcome::Loaded => Outcome::Loaded,
                core::Outcome::Invalid(fault) => Outcome::Invalid(reason(fault)),
                core::Outcome::NoTheme => Outcome::NoTheme,
            })
            .collect(),
    }
}

#[cfg(test)]
mod tests;
