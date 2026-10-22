//! The bridge between the Rust cvars and their Bend model
//! (`bend/cvar.bend`, whose laws `PROOF.bend` proves, section S4 of
//! `docs/control.md`): both run the same scenarios and must print the same
//! transcript, byte for byte.
//!
//! A scenario is a list of events (`bend/bridge_cvar.bend` documents the
//! format). Model cvar `n` is Rust cvar `c<n>`, alias `n` is `a<n>`, key
//! `n` is `k<n>`; a Nat is a [`CvarType::Nat`] with JSON numbers, a Bool a
//! [`CvarType::Bool`] with JSON bools. Six kinds of scenario:
//!
//! - registry: declaration lists with duplicate ids and defaults of the
//!   wrong type; [`Registry::new`] accepts exactly when the model's
//!   `registry` keeps every declaration, and names the first one it drops.
//! - value: config sets and families of agents with profiles and sets
//!   (of the wrong type, of Global cvars, of undeclared ids); the value of
//!   every id for each agent down the family ([`Cvars::value_of`]).
//! - toggle: toggles of the last agent of a family ([`Cvars::execute`] on
//!   [`Target::Sets`]), against the model's `toggle`, which flips the
//!   value the agent has with its inherited values. Rust refuses a toggle
//!   of a Global cvar where the model adds a set no agent layer admits, so
//!   the transcript prints the value after each toggle, which both define
//!   the same way.
//! - written: the sets an agent writes ([`Flag::Persist`]) and replicates
//!   ([`Flag::Replicate`]) ([`Sets::written`]).
//! - expand: alias tables with cycles and runs of aliases they do not hold
//!   ([`expand`]); the model's `CGone` is a run of a name the table does
//!   not hold.
//! - press: key binds, some keys bound twice, and presses of bound and
//!   unbound keys ([`Binds::press`]).
//!
//! A registry borrows `&'static [Decl]`, and [`Cvars`] a `&'static`
//! registry: the scenarios are planned once into [`PLANNED`], their
//! registries built once into [`REGISTRIES`], and then run.
//!
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::sync::LazyLock;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::cvar::{expand, render_list, Aliases, Binds, Command, ExpandError};
use serde_json::Value;

use super::{
    AgentLayer, CvarScope, CvarType, Cvars, Decl, Flag, Init, Registry, RegistryError, Set, Sets,
    Target,
};

/// A rule of the model the scenarios reach.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// The registry rejects a second declaration of an id.
    Duplicate,
    /// The registry rejects a default of the wrong type.
    BadDefault,
    /// A set of a Global cvar in an agent layer, of its type and of
    /// another value, is ignored.
    GlobalIgnored,
    /// The last set of a cvar in a layer has the wrong type and is
    /// ignored.
    WrongTypeIgnored,
    /// An agent's own set wins over its profile's set of another value.
    SetOverProfile,
    /// An expansion nests deeper than the table: a cycle.
    Cycle,
    /// A run of an alias the table does not hold.
    Unknown,
    /// A pressed key is bound twice, to different commands.
    FirstBind,
    /// A pressed key is not bound.
    Unbound,
    /// A subagent toggles a cvar whose value its family decides: the
    /// value over the family differs from the value over the agent alone.
    ToggleInherited,
}

/// The rules the scenarios reached.
type Reached = BTreeSet<Case>;

/// The Rust id of model cvar `n`: the ids `0..DECLARED` may be declared,
/// the others never are.
const IDS: [&str; 8] = ["c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7"];
const DECLARED: u64 = 6;
const UNDECLARED: u64 = 7;

fn id(n: u64) -> &'static str {
    IDS[usize::try_from(n).unwrap()]
}

/// The type of a model cvar.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ty {
    Nat,
    Bool,
}

impl Ty {
    fn random(rng: &mut Rng) -> Ty {
        if rng.chance(50) {
            Ty::Nat
        } else {
            Ty::Bool
        }
    }

    fn other(self) -> Ty {
        match self {
            Ty::Nat => Ty::Bool,
            Ty::Bool => Ty::Nat,
        }
    }
}

/// A value of the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Val {
    Nat(u64),
    Bool(bool),
}

impl Val {
    /// A value of type `ty`, from a few, so that sets repeat values.
    fn of(rng: &mut Rng, ty: Ty) -> Val {
        match ty {
            Ty::Nat => Val::Nat(rng.below(4)),
            Ty::Bool => Val::Bool(rng.chance(50)),
        }
    }

    fn ty(self) -> Ty {
        match self {
            Val::Nat(_) => Ty::Nat,
            Val::Bool(_) => Ty::Bool,
        }
    }

    /// The value as an event word.
    fn word(self) -> String {
        match self {
            Val::Nat(n) => format!("n{n}"),
            Val::Bool(true) => "t".to_string(),
            Val::Bool(false) => "f".to_string(),
        }
    }

    fn json(self) -> Value {
        match self {
            Val::Nat(n) => Value::from(n),
            Val::Bool(b) => Value::Bool(b),
        }
    }
}

/// A model declaration.
#[derive(Clone, Copy, Debug)]
struct Spec {
    id: u64,
    ty: Ty,
    scope: CvarScope,
    persist: bool,
    replicate: bool,
    init: Val,
}

impl Spec {
    /// A declaration of `id` with a default of its type.
    fn random(rng: &mut Rng, id: u64) -> Spec {
        let ty = Ty::random(rng);
        Spec {
            id,
            ty,
            scope: if rng.chance(30) {
                CvarScope::Global
            } else {
                CvarScope::Local
            },
            persist: rng.chance(50),
            replicate: rng.chance(50),
            init: Val::of(rng, ty),
        }
    }

    fn event(&self) -> String {
        let ty = match self.ty {
            Ty::Nat => "n",
            Ty::Bool => "b",
        };
        let scope = match self.scope {
            CvarScope::Global => "g",
            CvarScope::Local => "l",
        };
        format!(
            "d {} {ty} {scope} {} {} {}\n",
            self.id,
            u8::from(self.persist),
            u8::from(self.replicate),
            self.init.word()
        )
    }

    fn decl(&self) -> Decl {
        Decl {
            id: id(self.id),
            ty: match self.ty {
                Ty::Nat => CvarType::Nat,
                Ty::Bool => CvarType::Bool,
            },
            scope: self.scope,
            persist: self.persist,
            replicate: self.replicate,
            init: match self.init {
                Val::Nat(n) => Init::Nat(n),
                Val::Bool(b) => Init::Bool(b),
            },
        }
    }
}

/// A set of the model.
#[derive(Clone, Copy, Debug)]
struct Bind {
    id: u64,
    val: Val,
}

impl Bind {
    /// A set: mostly of a declared cvar, mostly of its type.
    fn random(rng: &mut Rng, specs: &[Spec]) -> Bind {
        let declared: Vec<u64> = specs.iter().map(|spec| spec.id).collect();
        let cvar = match rng.pick(&declared) {
            Some(cvar) if rng.chance(85) => cvar,
            Some(_) | None => rng.range(DECLARED, UNDECLARED),
        };
        let val = match specs.iter().find(|spec| spec.id == cvar) {
            Some(spec) if rng.chance(75) => Val::of(rng, spec.ty),
            Some(spec) => Val::of(rng, spec.ty.other()),
            None => {
                let ty = Ty::random(rng);
                Val::of(rng, ty)
            }
        };
        Bind { id: cvar, val }
    }
}

/// Up to `high` random sets.
fn random_binds(rng: &mut Rng, specs: &[Spec], high: u64) -> Vec<Bind> {
    (0..rng.below(high + 1))
        .map(|_| Bind::random(rng, specs))
        .collect()
}

fn sets(binds: &[Bind]) -> Sets {
    Sets(
        binds
            .iter()
            .map(|bind| Set {
                id: id(bind.id).to_string(),
                value: bind.val.json(),
            })
            .collect(),
    )
}

/// An agent of the model: its profile and its own sets.
#[derive(Clone, Debug)]
struct Agent {
    profile: Vec<Bind>,
    sets: Vec<Bind>,
}

impl Agent {
    fn random(rng: &mut Rng, specs: &[Spec]) -> Agent {
        Agent {
            profile: random_binds(rng, specs, 3),
            sets: random_binds(rng, specs, 3),
        }
    }

    fn layer(&self) -> AgentLayer {
        AgentLayer {
            profile: sets(&self.profile),
            sets: sets(&self.sets),
        }
    }
}

/// A command of the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Cmd {
    Set(u64, Val),
    Toggle(u64),
    /// A run of alias `n`, which the table may hold.
    Run(u64),
    /// A run of alias `n`, which the table does not hold.
    Gone(u64),
}

impl Cmd {
    /// A command over cvars `0..4` and aliases `0..6` (runs) or `6..9`
    /// (gone: no table holds them).
    fn random(rng: &mut Rng) -> Cmd {
        match rng.below(10) {
            0..=2 => {
                let ty = Ty::random(rng);
                Cmd::Set(rng.below(4), Val::of(rng, ty))
            }
            3..=4 => Cmd::Toggle(rng.below(4)),
            5..=8 => Cmd::Run(rng.below(6)),
            _ => Cmd::Gone(rng.range(6, 8)),
        }
    }

    fn word(self) -> String {
        match self {
            Cmd::Set(cvar, val) => format!("s:{cvar}:{}", val.word()),
            Cmd::Toggle(cvar) => format!("t:{cvar}"),
            Cmd::Run(name) => format!("r:{name}"),
            Cmd::Gone(name) => format!("g:{name}"),
        }
    }

    fn command(self) -> Command {
        match self {
            Cmd::Set(cvar, val) => Command::Set {
                id: id(cvar).to_string(),
                value: val.json().to_string(),
            },
            Cmd::Toggle(cvar) => Command::Toggle {
                id: id(cvar).to_string(),
            },
            Cmd::Run(name) | Cmd::Gone(name) => Command::Run {
                alias: format!("a{name}"),
            },
        }
    }
}

fn random_cmds(rng: &mut Rng, low: u64, high: u64) -> Vec<Cmd> {
    (0..rng.range(low, high))
        .map(|_| Cmd::random(rng))
        .collect()
}

/// An alias table of up to four distinct names among `0..6`, bodies of up
/// to three commands.
fn random_aliases(rng: &mut Rng) -> Vec<(u64, Vec<Cmd>)> {
    let mut names: Vec<u64> = (0..6).collect();
    let mut aliases = Vec::new();
    for _ in 0..rng.below(5) {
        let Some(name) = rng.pick(&names) else {
            break;
        };
        names.retain(|other| *other != name);
        aliases.push((name, random_cmds(rng, 0, 3)));
    }
    aliases
}

fn words(cmds: &[Cmd]) -> String {
    cmds.iter().fold(String::new(), |mut out, cmd| {
        let _ = write!(out, " {}", cmd.word());
        out
    })
}

fn commands(cmds: &[Cmd]) -> Vec<Command> {
    cmds.iter().map(|cmd| cmd.command()).collect()
}

/// What one scenario does.
enum Plan {
    /// Declarations, the registry after each.
    Registry { specs: Vec<Spec> },
    /// Config sets and a family; the values for each agent down it.
    Value {
        specs: Vec<Spec>,
        config: Vec<Bind>,
        family: Vec<Agent>,
    },
    /// Toggles of the last agent of a family (root first).
    Toggle {
        specs: Vec<Spec>,
        config: Vec<Bind>,
        family: Vec<Agent>,
        toggles: Vec<u64>,
    },
    /// An agent's sets; the ones it writes and replicates.
    Written { specs: Vec<Spec>, own: Vec<Bind> },
    /// Expansions of command lists with an alias table.
    Expand {
        aliases: Vec<(u64, Vec<Cmd>)>,
        lists: Vec<Vec<Cmd>>,
    },
    /// Key binds and presses.
    Press {
        aliases: Vec<(u64, Vec<Cmd>)>,
        binds: Vec<(u64, Vec<Cmd>)>,
        keys: Vec<u64>,
    },
}

impl Plan {
    /// Scenario `at`: the kinds take turns.
    fn random(rng: &mut Rng, at: u64) -> Plan {
        match at % 6 {
            0 => Plan::Registry {
                specs: (0..rng.range(1, 6))
                    .map(|_| {
                        let cvar = rng.below(DECLARED);
                        let mut spec = Spec::random(rng, cvar);
                        if rng.chance(12) {
                            spec.init = Val::of(rng, spec.ty.other());
                        }
                        spec
                    })
                    .collect(),
            },
            1 => {
                let specs = registry_specs(rng);
                let config = random_binds(rng, &specs, 4);
                let family = (0..rng.range(1, 4))
                    .map(|_| Agent::random(rng, &specs))
                    .collect();
                Plan::Value {
                    specs,
                    config,
                    family,
                }
            }
            2 => {
                let specs = registry_specs(rng);
                let config = random_binds(rng, &specs, 3);
                let family = (0..rng.range(1, 4))
                    .map(|_| Agent::random(rng, &specs))
                    .collect();
                let bools: Vec<u64> = specs
                    .iter()
                    .filter(|spec| spec.ty == Ty::Bool)
                    .map(|spec| spec.id)
                    .collect();
                let toggles = (0..rng.range(1, 4))
                    .map(|_| match rng.pick(&bools) {
                        Some(cvar) if rng.chance(75) => cvar,
                        Some(_) | None => rng.below(UNDECLARED + 1),
                    })
                    .collect();
                Plan::Toggle {
                    specs,
                    config,
                    family,
                    toggles,
                }
            }
            3 => {
                let specs = registry_specs(rng);
                let own = random_binds(rng, &specs, 6);
                Plan::Written { specs, own }
            }
            4 => Plan::Expand {
                aliases: random_aliases(rng),
                lists: (0..rng.range(1, 4))
                    .map(|_| random_cmds(rng, 1, 4))
                    .collect(),
            },
            _ => Plan::Press {
                aliases: random_aliases(rng),
                binds: (0..rng.range(1, 5))
                    .map(|_| (rng.below(4), random_cmds(rng, 0, 3)))
                    .collect(),
                keys: (0..rng.range(1, 4)).map(|_| rng.below(5)).collect(),
            },
        }
    }

    fn specs(&self) -> &[Spec] {
        match self {
            Plan::Registry { specs }
            | Plan::Value { specs, .. }
            | Plan::Toggle { specs, .. }
            | Plan::Written { specs, .. } => specs,
            Plan::Expand { .. } | Plan::Press { .. } => &[],
        }
    }
}

/// Declarations of distinct ids with defaults of their type.
fn registry_specs(rng: &mut Rng) -> Vec<Spec> {
    let mut specs = Vec::new();
    for cvar in 0..DECLARED {
        if rng.chance(60) {
            specs.push(Spec::random(rng, cvar));
        }
    }
    specs
}

/// A scenario and its declarations, as the registry borrows them.
struct Planned {
    plan: Plan,
    decls: Vec<Decl>,
}

/// Every scenario.
static PLANNED: LazyLock<Vec<Planned>> = LazyLock::new(|| {
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    (0..300)
        .map(|at| {
            let plan = Plan::random(&mut rng, at);
            let decls = plan.specs().iter().map(Spec::decl).collect();
            Planned { plan, decls }
        })
        .collect()
});

/// The registry of each scenario's declarations.
static REGISTRIES: LazyLock<Vec<Result<Registry, RegistryError>>> = LazyLock::new(|| {
    PLANNED
        .iter()
        .map(|planned| Registry::new(&planned.decls))
        .collect()
});

/// An expansion as the transcript prints it.
fn outcome(expanded: &Result<Vec<Command>, ExpandError>, reached: &mut Reached) -> String {
    match expanded {
        Ok(commands) => format!("[{}]", render_list(commands)),
        Err(ExpandError::Cycle { alias }) => {
            reached.insert(Case::Cycle);
            format!("cycle {alias}")
        }
        Err(ExpandError::Unknown { alias }) => {
            reached.insert(Case::Unknown);
            format!("unknown {alias}")
        }
    }
}

/// A value as the transcript prints it.
fn shown(value: Option<&Value>) -> String {
    value.map_or_else(|| "none".to_string(), Value::to_string)
}

/// One scenario as it runs on the Rust code: its events, for the model,
/// and the transcript the Rust code printed.
#[derive(Default)]
struct Run {
    events: String,
    transcript: String,
}

impl Run {
    fn declare(&mut self, specs: &[Spec]) {
        for spec in specs {
            self.events.push_str(&spec.event());
        }
    }

    /// The sets `binds` in the layer `letter` (c, p or s).
    fn binds(&mut self, letter: char, binds: &[Bind]) {
        for bind in binds {
            let _ = writeln!(self.events, "{letter} {} {}", bind.id, bind.val.word());
        }
    }

    fn aliases(&mut self, aliases: &[(u64, Vec<Cmd>)]) -> Aliases {
        let mut table = Aliases::default();
        for (name, body) in aliases {
            let _ = writeln!(self.events, "l {name}{}", words(body));
            table.define(format!("a{name}"), commands(body));
        }
        table
    }

    /// The registry after each declaration of `decls`.
    fn registry(&mut self, specs: &[Spec], decls: &'static [Decl], reached: &mut Reached) {
        for (at, spec) in specs.iter().enumerate() {
            self.events.push_str(&spec.event());
            self.events.push_str("g\n");
            let verdict = match Registry::new(&decls[..=at]) {
                Ok(_) => "accept".to_string(),
                Err(RegistryError::Duplicate { id }) => {
                    reached.insert(Case::Duplicate);
                    format!("reject dup {id}")
                }
                Err(RegistryError::BadDefault { id }) => {
                    reached.insert(Case::BadDefault);
                    format!("reject bad {id}")
                }
            };
            let _ = writeln!(self.transcript, "registry {verdict}");
        }
    }

    /// The value of every id for each agent down the family.
    fn value(
        &mut self,
        specs: &[Spec],
        registry: &'static Registry,
        config: &[Bind],
        family: &[Agent],
        reached: &mut Reached,
    ) {
        self.declare(specs);
        self.binds('c', config);
        for (at, agent) in family.iter().enumerate() {
            if at > 0 {
                self.events.push_str("a\n");
            }
            self.binds('p', &agent.profile);
            self.binds('s', &agent.sets);
            let chain = &family[..=at];
            let mut cvars = Cvars::new(registry, sets(config));
            cvars.set_family(chain.iter().map(Agent::layer).collect());
            for cvar in 0..=UNDECLARED {
                let _ = writeln!(self.events, "v {cvar}");
                let value = cvars.value_of(id(cvar));
                let _ = writeln!(
                    self.transcript,
                    "value {} {}",
                    id(cvar),
                    shown(value.as_ref())
                );
                if let (Some(spec), Some(value)) =
                    (specs.iter().find(|spec| spec.id == cvar), value)
                {
                    note_value(spec, config, chain, &value, reached);
                }
            }
        }
    }

    /// Toggles of the last agent of a family; the value after each.
    fn toggle(
        &mut self,
        specs: &[Spec],
        registry: &'static Registry,
        config: &[Bind],
        family: &[Agent],
        toggles: &[u64],
        reached: &mut Reached,
    ) {
        self.declare(specs);
        self.binds('c', config);
        for (at, agent) in family.iter().enumerate() {
            if at > 0 {
                self.events.push_str("a\n");
            }
            self.binds('p', &agent.profile);
            self.binds('s', &agent.sets);
        }
        let mut cvars = Cvars::new(registry, sets(config));
        cvars.set_family(family.iter().map(Agent::layer).collect());
        for cvar in toggles {
            let _ = writeln!(self.events, "t {cvar}");
            let mut alone = Cvars::new(registry, sets(config));
            alone.set_family(vec![cvars.agent().clone()]);
            if family.len() > 1 && alone.value_of(id(*cvar)) != cvars.value_of(id(*cvar)) {
                reached.insert(Case::ToggleInherited);
            }
            cvars.execute(
                Target::Sets,
                &[Command::Toggle {
                    id: id(*cvar).to_string(),
                }],
                &mut Aliases::default(),
                &mut Binds::default(),
            );
            let value = cvars.value_of(id(*cvar));
            let _ = writeln!(
                self.transcript,
                "toggle {} {}",
                id(*cvar),
                shown(value.as_ref())
            );
        }
    }

    /// The sets an agent writes and replicates.
    fn written(&mut self, specs: &[Spec], registry: &'static Registry, own: &[Bind]) {
        self.declare(specs);
        self.binds('s', own);
        let own = sets(own);
        for (flag, letter, name) in [
            (Flag::Persist, 'p', "persist"),
            (Flag::Replicate, 'r', "replicate"),
        ] {
            let _ = writeln!(self.events, "w {letter}");
            let _ = write!(self.transcript, "written {name}");
            for set in own.written(registry, flag).0 {
                let _ = write!(self.transcript, " {}={}", set.id, set.value);
            }
            self.transcript.push('\n');
        }
    }

    fn expand(&mut self, aliases: &[(u64, Vec<Cmd>)], lists: &[Vec<Cmd>], reached: &mut Reached) {
        let table = self.aliases(aliases);
        for cmds in lists {
            let _ = writeln!(self.events, "x{}", words(cmds));
            let expanded = expand(&commands(cmds), &table);
            let _ = writeln!(self.transcript, "expand {}", outcome(&expanded, reached));
        }
    }

    fn press(
        &mut self,
        aliases: &[(u64, Vec<Cmd>)],
        binds: &[(u64, Vec<Cmd>)],
        keys: &[u64],
        reached: &mut Reached,
    ) {
        let table = self.aliases(aliases);
        let mut bound = Binds::default();
        for (key, body) in binds {
            let _ = writeln!(self.events, "b {key}{}", words(body));
            bound.push(format!("k{key}"), commands(body));
        }
        for key in keys {
            let _ = writeln!(self.events, "k {key}");
            let bodies: Vec<&Vec<Cmd>> = binds
                .iter()
                .filter(|(bound, _)| bound == key)
                .map(|(_, body)| body)
                .collect();
            match bodies.as_slice() {
                [] => {
                    reached.insert(Case::Unbound);
                }
                [first, rest @ ..] => {
                    if rest.iter().any(|body| body != first) {
                        reached.insert(Case::FirstBind);
                    }
                }
            }
            let pressed = bound.press(&format!("k{key}"), &table);
            let _ = writeln!(
                self.transcript,
                "press k{key} {}",
                outcome(&pressed, reached)
            );
        }
    }
}

/// Note the rules the value `value` of `spec`'s cvar reached.
fn note_value(
    spec: &Spec,
    config: &[Bind],
    family: &[Agent],
    value: &Value,
    reached: &mut Reached,
) {
    let typed_last = |layer: &[Bind]| {
        layer
            .iter()
            .rev()
            .find(|bind| bind.id == spec.id && bind.val.ty() == spec.ty)
            .map(|bind| bind.val)
    };
    let layers = std::iter::once(config).chain(
        family
            .iter()
            .flat_map(|agent| [agent.profile.as_slice(), agent.sets.as_slice()]),
    );
    for layer in layers {
        if layer
            .iter()
            .rev()
            .find(|bind| bind.id == spec.id)
            .is_some_and(|bind| bind.val.ty() != spec.ty)
        {
            reached.insert(Case::WrongTypeIgnored);
        }
    }
    for agent in family {
        let (profile, own) = (typed_last(&agent.profile), typed_last(&agent.sets));
        match spec.scope {
            CvarScope::Global => {
                if [profile, own]
                    .into_iter()
                    .flatten()
                    .any(|val| val.json() != *value)
                {
                    reached.insert(Case::GlobalIgnored);
                }
            }
            CvarScope::Local => {
                if profile.is_some() && own.is_some() && profile != own {
                    reached.insert(Case::SetOverProfile);
                }
            }
        }
    }
}

#[test]
fn the_rust_cvars_equal_the_bend_model() {
    let mut reached = Reached::new();
    let scenarios: Vec<Scenario> = PLANNED
        .iter()
        .zip(REGISTRIES.iter())
        .enumerate()
        .map(|(at, (planned, registry))| {
            let mut run = Run::default();
            let kind = match &planned.plan {
                Plan::Registry { specs } => {
                    run.registry(specs, &planned.decls, &mut reached);
                    "registry"
                }
                Plan::Value {
                    specs,
                    config,
                    family,
                } => {
                    run.value(
                        specs,
                        registry.as_ref().unwrap(),
                        config,
                        family,
                        &mut reached,
                    );
                    "value"
                }
                Plan::Toggle {
                    specs,
                    config,
                    family,
                    toggles,
                } => {
                    run.toggle(
                        specs,
                        registry.as_ref().unwrap(),
                        config,
                        family,
                        toggles,
                        &mut reached,
                    );
                    "toggle"
                }
                Plan::Written { specs, own } => {
                    run.written(specs, registry.as_ref().unwrap(), own);
                    "written"
                }
                Plan::Expand { aliases, lists } => {
                    run.expand(aliases, lists, &mut reached);
                    "expand"
                }
                Plan::Press {
                    aliases,
                    binds,
                    keys,
                } => {
                    run.press(aliases, binds, keys, &mut reached);
                    "press"
                }
            };
            Scenario {
                name: format!("{kind} {at}"),
                events: run.events,
                transcript: run.transcript,
            }
        })
        .collect();
    compare("bend/bridge_cvar.bend", scenarios);
    // The scenarios reach every rule of the model.
    assert_eq!(
        reached,
        Reached::from([
            Case::Duplicate,
            Case::BadDefault,
            Case::GlobalIgnored,
            Case::WrongTypeIgnored,
            Case::SetOverProfile,
            Case::Cycle,
            Case::Unknown,
            Case::FirstBind,
            Case::Unbound,
            Case::ToggleInherited,
        ])
    );
}
