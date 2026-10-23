//! The bridge between `eukhe-theme` (the theme validator, the name
//! resolver and the color math that the terminal UI and this export
//! share) and its Bend model (`bend/theme.bend`, `bend/color.bend`, whose
//! laws `PROOF.bend` proves, T1, `laws/theme.bend`): both run
//! the same scenarios and must print the same transcript, byte for byte
//! (`bend/bridge_theme.bend` documents the format).
//!
//! The scenarios hold:
//! - the shipped tables: the color every token of each bundled theme file
//!   paints must be the model's table (the tables the WCAG and 256-color
//!   laws are proved on are the JSON files);
//! - the linear channel table, every xterm-256 index, and edge and random
//!   color pairs (luminance, mode, quantization, both contrast ratios);
//! - name resolution over real files in a temp dir: registered and custom
//!   candidates, valid and invalid, shadowing the builtins, the empty name;
//! - theme files: edge and random colors, variables (chains, cycles,
//!   missing ones), malformed colors, missing tokens, export pages.
//!
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_theme::{
    ansi256, contrast_at_least, linear_channel, luminance, rgb_to_256, ContrastRatio,
    ExportSurface, Mode, Palette, Presence, Rgb, ThemeError, ThemeSources, Token,
    BUILTIN_THEME_NAMES,
};
use serde_json::{json, Map, Value};

const DUSK_APPLE: &str = include_str!("../../../eukhe-theme/tests/fixtures/dusk-apple-theme.json");

/// ` #rrggbb` for every token of `palette`.
fn paints(palette: &Palette) -> String {
    let mut out = String::new();
    for token in Token::ALL {
        write!(out, " {}", palette.rgb(token)).unwrap();
    }
    out
}

fn bit(value: bool) -> u8 {
    u8::from(value)
}

fn tables() -> Scenario {
    let mut transcript = String::new();
    for name in BUILTIN_THEME_NAMES {
        let palette = Palette::builtin(name).expect("builtin");
        writeln!(transcript, "table {name}{}", paints(&palette)).unwrap();
    }
    Scenario {
        name: "tables".to_string(),
        events: "tables\n".to_string(),
        transcript,
    }
}

fn colors(rng: &mut Rng) -> Scenario {
    let mut events = String::from("lin\n");
    let mut transcript = String::from("lin");
    for channel in 0..=255u8 {
        write!(transcript, " {}", linear_channel(channel)).unwrap();
    }
    transcript.push('\n');
    for index in 0..=255u8 {
        writeln!(events, "ansi {index}").unwrap();
        writeln!(transcript, "ansi {index} {}", ansi256(index)).unwrap();
    }
    let channel = |rng: &mut Rng| u8::try_from(rng.below(256)).expect("a channel");
    let mut pairs = vec![
        (Rgb::new(0, 0, 0), Rgb::new(255, 255, 255)),
        (Rgb::new(255, 255, 255), Rgb::new(255, 255, 255)),
        (Rgb::new(0x73, 0x73, 0x73), Rgb::new(0xf9, 0xf9, 0xf9)),
        (Rgb::new(0x76, 0x76, 0x7f), Rgb::new(0x05, 0x05, 0x06)),
        (Rgb::new(0xbc, 0xbc, 0xbc), Rgb::new(0x10, 0x10, 0x10)),
        (Rgb::new(13, 13, 13), Rgb::new(115, 115, 115)),
    ];
    pairs.extend((0..400).map(|_| {
        let a = Rgb::new(channel(rng), channel(rng), channel(rng));
        // Near-neutral colors reach the gray ramp.
        let b = if rng.chance(30) {
            let base = channel(rng).min(245);
            Rgb::new(
                base + u8::try_from(rng.below(10)).expect("small"),
                base,
                base + u8::try_from(rng.below(10)).expect("small"),
            )
        } else {
            Rgb::new(channel(rng), channel(rng), channel(rng))
        };
        (a, b)
    }));
    for (a, b) in pairs {
        writeln!(
            events,
            "color {} {} {} {} {} {}",
            a.r, a.g, a.b, b.r, b.g, b.b
        )
        .unwrap();
        writeln!(
            transcript,
            "color {} {} {} {} {}",
            luminance(a),
            bit(Mode::of_background(a) == Mode::Light),
            rgb_to_256(a),
            bit(contrast_at_least(a, b, ContrastRatio::TEXT)),
            bit(contrast_at_least(a, b, ContrastRatio::NON_TEXT)),
        )
        .unwrap();
        writeln!(events, "color {} {} {} 0 0 0", b.r, b.g, b.b).unwrap();
        writeln!(
            transcript,
            "color {} {} {} {} {}",
            luminance(b),
            bit(Mode::of_background(b) == Mode::Light),
            rgb_to_256(b),
            bit(contrast_at_least(b, Rgb::new(0, 0, 0), ContrastRatio::TEXT)),
            bit(contrast_at_least(
                b,
                Rgb::new(0, 0, 0),
                ContrastRatio::NON_TEXT
            )),
        )
        .unwrap();
    }
    Scenario {
        name: "colors".to_string(),
        events,
        transcript,
    }
}

/// One candidate theme file of a resolution scenario.
#[derive(Clone, Copy, Debug)]
struct Cand {
    registered: bool,
    name: &'static str,
    valid: bool,
    id: u8,
}

/// The names the scenarios draw from: the builtins and two others.
const NAMES: [&str; 5] = ["eukhe", "dark", "light", "dusk", "mist"];

/// The theme file of `cand`: dusk-apple renamed, its accent `#0100<id>`;
/// an invalid one misses `bashMode`.
fn cand_file(cand: Cand) -> String {
    let mut value: Value = serde_json::from_str(DUSK_APPLE).expect("fixture");
    value["name"] = Value::from(cand.name);
    let colors = value["colors"].as_object_mut().expect("colors");
    colors.insert(
        "accent".to_string(),
        Value::from(format!("#0100{:02x}", cand.id)),
    );
    if !cand.valid {
        colors.remove("bashMode");
    }
    value.to_string()
}

/// What `name` resolves to over `cands` on the real resolver: the
/// candidate id (0..2 for the builtins), whether it warned, the cause of
/// the warning (`-` none, `n` not found, else the failed file's id), the
/// clashes (`,id>winner` each) and the other failed files (`,id` each).
fn resolve_line(dir: &Path, name: &str, cands: &[Cand]) -> String {
    let custom_dir = dir.join("custom");
    std::fs::create_dir_all(&custom_dir).expect("custom dir");
    let mut registered = Vec::new();
    let mut paths: Vec<(String, u8)> = Vec::new();
    for (at, cand) in cands.iter().enumerate() {
        let path = if cand.registered {
            let path = dir.join(format!("registered-{at}.json"));
            registered.push(path.clone());
            path
        } else {
            // The custom directory loads in path order: keep the
            // candidates' order.
            custom_dir.join(format!("custom-{at:02}.json"))
        };
        std::fs::write(&path, cand_file(*cand)).expect("write theme");
        paths.push((path.display().to_string(), cand.id));
    }
    let id_in = |text: &str| {
        paths
            .iter()
            .find(|(path, _)| text.contains(path.as_str()))
            .map_or_else(|| panic!("a candidate path in {text}"), |(_, id)| *id)
    };
    let resolved = ThemeSources {
        registered,
        custom_dir: Some(custom_dir),
        diagnostics: Vec::new(),
    }
    .resolve(name);
    let id = BUILTIN_THEME_NAMES
        .iter()
        .position(|builtin| Palette::builtin(builtin).as_ref() == Some(&resolved.palette))
        .map_or_else(
            || u32::from(resolved.palette.rgb(Token::Accent).b),
            |at| u32::try_from(at).expect("small"),
        );
    let unavailable = format!("Theme \"{name}\" unavailable, using \"eukhe\": ");
    let (mut cause, mut clashes, mut broken) = ("-".to_string(), String::new(), String::new());
    for warning in &resolved.warnings {
        if let Some(reason) = warning.strip_prefix(&unavailable) {
            cause = if reason.starts_with("Theme not found:") {
                "n".to_string()
            } else {
                id_in(reason).to_string()
            };
        } else if let Some((clash, winner)) = warning
            .split_once(" collision: ")
            .and_then(|(_, rest)| rest.split_once(" (using "))
        {
            write!(clashes, ",{}>{}", id_in(clash), id_in(winner)).unwrap();
        } else {
            write!(broken, ",{}", id_in(warning)).unwrap();
        }
    }
    let warned = cause != "-";
    format!("resolve {id} {} {cause} {clashes} {broken}\n", bit(warned))
}

fn resolutions(rng: &mut Rng) -> Vec<Scenario> {
    let cand = |registered: bool, name: &'static str, valid: bool, id: u8| Cand {
        registered,
        name,
        valid,
        id,
    };
    let mut plans: Vec<(&'static str, Vec<Cand>)> = vec![
        ("", vec![cand(true, "dark", true, 5)]),
        ("dark", vec![cand(true, "dark", true, 5)]),
        ("dark", vec![cand(false, "dark", true, 5)]),
        ("dusk", vec![cand(true, "dusk", false, 5)]),
        (
            "dusk",
            vec![cand(true, "dusk", false, 5), cand(false, "dusk", true, 6)],
        ),
        (
            "dusk",
            vec![cand(false, "dusk", true, 5), cand(true, "dusk", true, 6)],
        ),
        ("mist", Vec::new()),
    ];
    for _ in 0..40 {
        let name = rng.pick(&NAMES).expect("a name");
        let count = rng.below(5);
        let cands = (0..count)
            .map(|at| Cand {
                registered: rng.chance(50),
                name: rng.pick(&NAMES).expect("a name"),
                valid: rng.chance(75),
                id: 3 + u8::try_from(at).expect("small"),
            })
            .collect();
        plans.push((if rng.chance(10) { "" } else { name }, cands));
    }
    plans
        .into_iter()
        .enumerate()
        .map(|(at, (name, cands))| {
            let dir = tempfile::tempdir().expect("temp dir");
            let mut events = format!("resolve {}", if name.is_empty() { "-" } else { name });
            for cand in &cands {
                write!(
                    events,
                    " {}:{}:{}:{}",
                    if cand.registered { 'R' } else { 'C' },
                    cand.name,
                    bit(cand.valid),
                    cand.id
                )
                .unwrap();
            }
            events.push('\n');
            Scenario {
                name: format!("resolve {at}"),
                transcript: resolve_line(dir.path(), name, &cands),
                events,
            }
        })
        .collect()
}

/// A raw value of a theme file: its scenario word and its JSON. A
/// reference names one of the `vars` variables, or (rarely) a missing one;
/// a few values are no color (an index past 255, a sign, a fraction, a
/// short hex, null, a bool).
fn raw(rng: &mut Rng, vars: u64) -> (String, Value) {
    let roll = rng.below(100);
    if roll < 97 && (roll >= 75 && vars > 0) {
        let at = if rng.chance(95) {
            rng.below(vars)
        } else {
            vars
        };
        let name = format!("v{at}");
        (format!("r{name}"), Value::from(name))
    } else if roll < 15 {
        ("d".to_string(), Value::from(""))
    } else if roll < 28 {
        let index = rng.below(260);
        (format!("n{index}"), Value::from(index))
    } else if roll < 29 {
        ("n-1".to_string(), Value::from(-1))
    } else if roll < 30 {
        ("n1.5".to_string(), Value::from(1.5))
    } else if roll < 97 {
        let hex = format!("{:06x}", rng.below(0x0100_0000));
        (format!("h{hex}"), Value::from(format!("#{hex}")))
    } else if roll < 98 {
        ("habc".to_string(), Value::from("#abc"))
    } else if roll < 99 {
        ("onull".to_string(), Value::Null)
    } else {
        ("otrue".to_string(), Value::from(true))
    }
}

/// The scenario words of a theme's colors (`C:key:raw`), in key order: the
/// order the file reads them in.
fn color_words(line: &mut String, colors: &BTreeMap<String, String>) {
    for (key, word) in colors {
        write!(line, " C:{key}:{word}").unwrap();
    }
}

/// One theme file of a file scenario: its scenario line and its JSON. One
/// file in ten misses a required token, one in twenty has an unknown key.
fn random_file(rng: &mut Rng) -> (String, Value) {
    let mut line = String::from("file");
    let var_count = rng.below(5);
    let mut vars = Map::new();
    for at in 0..var_count {
        let (word, value) = raw(rng, var_count);
        write!(line, " V:v{at}:{word}").unwrap();
        vars.insert(format!("v{at}"), value);
    }
    let dropped = if rng.chance(10) {
        rng.pick(&Token::ALL)
            .filter(|token| token.presence() == Presence::Required)
    } else {
        None
    };
    let mut colors = Map::new();
    let mut words = BTreeMap::new();
    for token in Token::ALL {
        let present = match token.presence() {
            Presence::Required => Some(token) != dropped,
            Presence::Optional => rng.chance(50),
        };
        if present {
            let (word, value) = raw(rng, var_count);
            words.insert(token.name().to_string(), word);
            colors.insert(token.name().to_string(), value);
        }
    }
    if rng.chance(5) {
        let key = rng.pick(&["bogus", "Accent", "zz"]).expect("a key");
        words.insert(key.to_string(), "d".to_string());
        colors.insert(key.to_string(), Value::from(""));
    }
    color_words(&mut line, &words);
    let mut export = Map::new();
    for (letter, key) in [('P', "pageBg"), ('K', "cardBg"), ('I', "infoBg")] {
        if rng.chance(50) {
            let (word, value) = raw(rng, var_count);
            // An export key set to null is no key (serde reads it as None).
            if !value.is_null() {
                write!(line, " {letter}:{word}").unwrap();
            }
            export.insert(key.to_string(), value);
        }
    }
    let mut file = json!({ "name": "f", "vars": vars, "colors": colors });
    if !export.is_empty() {
        file["export"] = Value::Object(export);
    }
    (line, file)
}

/// A theme file with every token: dusk-apple's colors as hex, the given
/// background, and no export page.
fn edge_file(background: Option<&str>, drop: Option<Token>) -> (String, Value) {
    let dusk = Palette::parse(DUSK_APPLE).expect("fixture");
    let mut line = String::from("file");
    let mut colors = Map::new();
    let mut words = BTreeMap::new();
    for token in Token::ALL {
        if Some(token) == drop {
            continue;
        }
        let value = match (token, background) {
            (Token::Background, Some(hex)) => hex.to_string(),
            (Token::Background | Token::Foreground, _) => continue,
            _ => dusk.rgb(token).to_string(),
        };
        words.insert(token.name().to_string(), format!("h{}", &value[1..]));
        colors.insert(token.name().to_string(), Value::from(value));
    }
    color_words(&mut line, &words);
    (line, json!({ "name": "f", "colors": colors }))
}

/// `#rrggbb`, or `-` for none.
fn optional(color: Option<Rgb>) -> String {
    color.map_or_else(|| "-".to_string(), |rgb| rgb.to_string())
}

fn files(rng: &mut Rng) -> Scenario {
    let mut cases = vec![
        edge_file(None, None),
        edge_file(Some("#fafafa"), None),
        edge_file(Some("#101010"), None),
        edge_file(None, Some(Token::BashMode)),
        edge_file(None, Some(Token::MdBody)),
    ];
    cases.extend((0..400).map(|_| random_file(rng)));
    let mut events = String::new();
    let mut transcript = String::new();
    for (line, file) in cases {
        events.push_str(&line);
        events.push('\n');
        match Palette::parse(&file.to_string()) {
            Ok(palette) => writeln!(
                transcript,
                "file ok {}{} {} {} {} {}",
                bit(palette.mode() == Mode::Light),
                paints(&palette),
                optional(palette.declared_background()),
                optional(palette.export_surface(ExportSurface::Page)),
                optional(palette.export_surface(ExportSurface::Card)),
                optional(palette.export_surface(ExportSurface::Info)),
            )
            .unwrap(),
            Err(ThemeError::Invalid { reason, .. }) => {
                writeln!(transcript, "file invalid {reason}").unwrap();
            }
            Err(ThemeError::Parse(error)) => panic!("a generated file is a theme object: {error}"),
        }
    }
    Scenario {
        name: "files".to_string(),
        events,
        transcript,
    }
}

#[test]
fn the_rust_themes_equal_the_bend_model() {
    let mut rng = Rng(0x7e3e_c0de_5eed_0001);
    let mut scenarios = vec![tables(), colors(&mut rng), files(&mut rng)];
    scenarios.extend(resolutions(&mut rng));
    compare("bend/bridge_theme.bend", scenarios);
}
