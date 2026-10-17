//! The bridge between the tool surface and its Bend model (`bend/tools.bend`
//! sections 1 and 2, whose laws `PROOF.bend` proves; docs/harness.md S7):
//! both run the same scenarios and must print the same transcript, byte for
//! byte.
//!
//! A scenario is a list of ops (`bend/bridge_tools.bend` documents the
//! format): new sessions with a roster, tools that join and quit, requests,
//! and tool schemas to build. The Rust side drives a real registry with its
//! roster fixed, a [`ToolSurface`] and [`tool_contract::build`]: a tool that
//! joins is also offered to the registry (which must refuse to change the
//! roster) and joins the surface; a tool that quits also tries to take the
//! roster's extension away; a request resolves the agent's tools as the
//! Harness does. After each op it prints the roster, what `dyn` reaches, the
//! requests sent and whether each sent the roster; a schema prints the
//! parameters and version the harness sends and whether building it again
//! changes nothing. The Bend side builds `bend/bridge_tools.bend` into a
//! native binary and prints the same from the model `run`/`step`/`dyn_call`
//! and `build`.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;
use std::sync::Arc;

use eukhe_ai::typebox::Type;
use eukhe_durable::harness::agent::{resolve_agent, resolve_settings};
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{
    Extension, RegistryReader, ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::pi_ai::ToolSchema;
use serde_json::{json, Map, Value};

use super::ToolSurface;
use crate::durable::tool_contract;

/// The tools `dyn` reach is printed for: `t0` to `t5`.
const TOOLS: u64 = 6;

fn tool(id: u64) -> Arc<ToolRegistration> {
    let mut tool = ToolRegistration::new(
        format!("t{id}"),
        format!("tool {id}"),
        Type::object([("x", Type::string())]),
        |_, _, _| async { Ok(ToolExecutionResult::default()) },
    );
    tool.parameters = tool_contract::build(&tool.parameters);
    Arc::new(tool)
}

fn ids(names: impl Iterator<Item = String>) -> String {
    names
        .map(|name| name[1..].to_owned())
        .collect::<Vec<_>>()
        .join(",")
}

/// The scenario file as it runs on the Rust side: its ops, for the model,
/// and the transcript the Rust code printed.
struct Run {
    registry: Registry,
    surface: ToolSurface,
    sent: Vec<Vec<String>>,
    events: String,
    transcript: String,
}

impl Run {
    /// The tools a request would send now, as the Harness resolves them.
    fn roster(&self) -> Vec<String> {
        resolve_agent(
            None,
            &self.registry.snapshot(),
            &resolve_settings(None),
            &|_| {},
        )
        .tools
        .iter()
        .map(|tool| tool.name.clone())
        .collect()
    }

    fn print(&mut self) {
        let roster = self.roster();
        let reach: String = (0..TOOLS)
            .map(|id| match self.surface.tool(&format!("t{id}")) {
                Some(_) => '1',
                None => '0',
            })
            .collect();
        let same = self.sent.iter().all(|sent| *sent == roster);
        let _ = writeln!(
            self.transcript,
            "r={} d={reach} n={} eq={}",
            ids(roster.into_iter()),
            self.sent.len(),
            u8::from(same)
        );
    }

    fn new_session(&mut self, roster: &[u64]) {
        let _ = writeln!(
            self.events,
            "{}",
            std::iter::once(0)
                .chain(roster.iter().copied())
                .map(|id| id.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        );
        self.registry = create_registry();
        self.registry
            .install(Arc::new(Extension {
                tools: roster.iter().map(|&id| tool(id)).collect(),
                ..Extension::named("roster")
            }))
            .expect("the roster installs");
        self.registry.fix_roster();
        self.surface = ToolSurface::default();
        self.sent.clear();
        self.print();
    }

    fn join(&mut self, id: u64) {
        let _ = writeln!(self.events, "1 {id}");
        // The registry refuses a tool that would change the roster.
        let _refused = self.registry.install(Arc::new(Extension {
            tools: vec![tool(id)],
            ..Extension::named("late")
        }));
        self.surface.join(tool(id));
        self.print();
    }

    fn quit(&mut self, id: u64) {
        let _ = writeln!(self.events, "2 {id}");
        let _refused = self.registry.uninstall(&Extension::named("roster"));
        self.surface.quit(&format!("t{id}"));
        self.print();
    }

    fn turn(&mut self) {
        let _ = writeln!(self.events, "3");
        let roster = self.roster();
        self.sent.push(roster);
        self.print();
    }

    fn schema(&mut self, version: u64, params: &[u64]) {
        let _ = writeln!(
            self.events,
            "{}",
            [4, version]
                .into_iter()
                .chain(params.iter().copied())
                .map(|id| id.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        );
        let mut properties = Map::new();
        for &id in params {
            let name = if id == 0 {
                "i".to_owned()
            } else {
                format!("p{id}")
            };
            properties.insert(name, json!({ "type": "string" }));
        }
        let mut declared = json!({ "type": "object", "properties": properties });
        if version > 0 {
            declared["title"] = Value::from(format!("v{version}"));
        }
        let built = tool_contract::build(&ToolSchema::from(declared));
        let names: Vec<String> = built["properties"]
            .as_object()
            .expect("built properties")
            .keys()
            .map(|name| match name.as_str() {
                "i" => "0".to_owned(),
                other => other[1..].to_owned(),
            })
            .collect();
        let _ = writeln!(
            self.transcript,
            "b={} v={} idem={}",
            names.join(","),
            built["title"].as_str().expect("a version")[1..].to_owned(),
            u8::from(tool_contract::build(&built) == built)
        );
    }
}

/// `count` distinct ids below `TOOLS`, in a random order.
fn distinct(rng: &mut Rng, count: u64) -> Vec<u64> {
    let mut left: Vec<u64> = (0..TOOLS).collect();
    let mut picked = Vec::new();
    for _ in 0..count.min(TOOLS) {
        let len = u64::try_from(left.len()).unwrap_or(1);
        let at = usize::try_from(rng.below(len)).unwrap_or(0);
        picked.push(left.remove(at));
    }
    picked
}

/// Every scenario, in one file: each starts a new session.
fn scenarios() -> Run {
    let mut run = Run {
        registry: create_registry(),
        surface: ToolSurface::default(),
        sent: Vec::new(),
        events: String::new(),
        transcript: String::new(),
    };
    let mut rng = Rng(0x5eed_7001_5ca1_ab1e);
    for _ in 0..300 {
        let roster = rng.range(0, 4);
        let roster = distinct(&mut rng, roster);
        run.new_session(&roster);
        for _ in 0..rng.range(5, 40) {
            match rng.below(100) {
                0..=34 => run.join(rng.below(TOOLS)),
                35..=59 => run.quit(rng.below(TOOLS)),
                60..=84 => run.turn(),
                _ => {
                    let version = rng.below(4);
                    let count = rng.range(0, 4);
                    let params = distinct(&mut rng, count);
                    run.schema(version, &params);
                }
            }
        }
    }
    run
}

#[test]
fn the_rust_tool_surface_equals_the_bend_model() {
    let run = scenarios();
    compare(
        "bend/bridge_tools.bend",
        [Scenario {
            name: "every scenario".to_owned(),
            events: run.events,
            transcript: run.transcript,
        }],
    );
}
