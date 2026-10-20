//! The bridge between the path policy (`eukhe_types::path_policy`), the
//! document tools' gate ([`DocumentsGate`]) and their Bend model
//! (`bend/path_policy.bend`, whose laws `laws/path_policy.bend` states as
//! `Pg.*`; docs/tools.md S7): both run the same scenarios and must print
//! the same transcript, byte for byte.
//!
//! Each scenario builds a tree in a temp dir: directories and files named
//! `n0` to `n5`, and symlinks with targets from `/` and from the link's
//! directory (with `..`), dangling targets and loops included. Model name
//! `k` below [`TOP`] is `n<k>`; name `TOP + i` is the `i`-th distinct
//! component of the canonical temp dir's own path, so a `..` above the
//! temp dir goes to the same place in both. `bend/bridge_path_policy.bend`
//! documents the scenario format and the transcript. A scenario has:
//!
//! - a policy: workspace roots, protected `Tree`, `Dir` and `Named`
//!   rules, and secret entries ([`PathPolicy::new`]);
//! - queries: for each path, its resolution ([`resolve`]: whether its
//!   links looped, and its real path), its class ([`PathPolicy::class`]),
//!   whether it holds a secret ([`PathPolicy::holds_secret`]), and for a
//!   read, a list, a search and a write, each with its own auto set and
//!   answer, whether [`DocumentsGate::check`] of the resolution let it
//!   run and whether it asked the approval sink (the model's `Pp.runs`
//!   and `Pp.asks`);
//! - a store trace: agent writes through [`Documents::write`] with the
//!   gate and answers that are never yes: whether the gate asked, and the
//!   path the question named; then the content of every protected or
//!   secret file (the model's `Pp.guarded` of `Pp.run`: law
//!   `Pg.config_needs_yes`).
//!
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::{BTreeSet, VecDeque};
use std::fmt::Write as _;
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::AtomicU64;
use std::sync::{Arc, Mutex};

use eukhe_docs::{Access, AccessGate as _, Documents};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::path_policy::{resolve, PathClass, PathPolicy, PathRule};
use eukhe_types::shell::{AutoSet, ShellApprovalRequest, ShellEffect, ShellVerdict};
use futures::FutureExt as _;

use super::{DocumentsGate, ShellApprovalSink};

/// The number of scenarios.
const SCENARIOS: u64 = 200;
/// Model names `0..NAMES` are the tree's names `n0` to `n5`.
const NAMES: u64 = 6;
/// Model name `TOP + i` is the `i`-th distinct component of the temp dir.
const TOP: u64 = 100;
/// The accesses of a query, in transcript order.
const ACCESSES: [Access; 4] = [Access::Read, Access::List, Access::Search, Access::Write];

/// A rule of the model the scenarios reach.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// A query's links looped.
    Looped,
    /// A query's links looped, and a `..` after the loop left the link.
    LoopedLeft,
    /// A query of each class.
    Inside,
    Outside,
    Protected,
    Secret,
    /// A query holds a secret that it is not under.
    HoldsBelow,
    /// The gate asked about a write of the store trace.
    WriteAsked,
    /// A write of the store trace ran without a question.
    WriteRan,
    /// A protected or secret file was there after the store trace.
    Guarded,
}

/// One segment of a path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Seg {
    Name(u64),
    Up,
    Here,
}

impl Seg {
    fn token(self) -> String {
        match self {
            Seg::Name(name) => format!("n{name}"),
            Seg::Up => "u".to_owned(),
            Seg::Here => "h".to_owned(),
        }
    }
}

/// The user's answer to a question.
#[derive(Clone, Copy, Debug)]
enum Answer {
    Yes,
    No,
    /// No one answered.
    Gone,
}

impl Answer {
    fn token(self) -> &'static str {
        match self {
            Answer::Yes => "y",
            Answer::No => "n",
            Answer::Gone => "g",
        }
    }

    fn verdict(self) -> Option<ShellVerdict> {
        match self {
            Answer::Yes => Some(ShellVerdict::Approve),
            Answer::No => Some(ShellVerdict::Deny),
            Answer::Gone => None,
        }
    }
}

/// The canonical temp dir of a scenario and the names of its components.
struct Top {
    dir: PathBuf,
    /// The distinct components of `dir`, in first-seen order.
    names: Vec<String>,
    /// `dir` as model names, from `/`.
    at: Vec<u64>,
}

impl Top {
    fn new(dir: PathBuf) -> Self {
        let mut names: Vec<String> = Vec::new();
        let mut at = Vec::new();
        for component in dir.components() {
            if let Component::Normal(name) = component {
                let name = name.to_str().unwrap().to_owned();
                let index = names
                    .iter()
                    .position(|seen| *seen == name)
                    .unwrap_or_else(|| {
                        names.push(name);
                        names.len() - 1
                    });
                at.push(TOP + u64::try_from(index).unwrap());
            }
        }
        Self { dir, names, at }
    }

    fn name(&self, name: u64) -> String {
        if name < TOP {
            format!("n{name}")
        } else {
            self.names[usize::try_from(name - TOP).unwrap()].clone()
        }
    }

    /// The text of `segs` as a relative path (`.` for none).
    fn relative(&self, segs: &[Seg]) -> String {
        if segs.is_empty() {
            return ".".to_owned();
        }
        segs.iter()
            .map(|seg| match seg {
                Seg::Name(name) => self.name(*name),
                Seg::Up => "..".to_owned(),
                Seg::Here => ".".to_owned(),
            })
            .collect::<Vec<_>>()
            .join("/")
    }

    /// The absolute path of `segs` (from `/`).
    fn path(&self, segs: &[Seg]) -> PathBuf {
        PathBuf::from(format!("/{}", self.relative(segs)))
    }

    /// The location `at` (model names, from `/`).
    fn location(&self, at: &[u64]) -> PathBuf {
        at.iter()
            .fold(PathBuf::from("/"), |path, name| path.join(self.name(*name)))
    }

    /// `path` as transcript names: ` nK` each.
    fn shown(&self, path: &Path) -> String {
        path.components()
            .filter_map(|component| match component {
                Component::RootDir => None,
                Component::Prefix(_) => Some(" ?prefix".to_owned()),
                Component::CurDir => Some(" ?.".to_owned()),
                Component::ParentDir => Some(" ?..".to_owned()),
                Component::Normal(name) => {
                    let name = name.to_str().unwrap();
                    let tree = name
                        .strip_prefix('n')
                        .and_then(|index| index.parse::<u64>().ok())
                        .filter(|index| *index < NAMES);
                    let top = self.names.iter().position(|seen| seen == name);
                    Some(match (tree, top) {
                        (Some(index), _) => format!(" n{index}"),
                        (None, Some(index)) => format!(" n{}", TOP + u64::try_from(index).unwrap()),
                        (None, None) => format!(" ?{name}"),
                    })
                }
            })
            .collect()
    }
}

/// A symlink at `at` to `to`, from `/` (`absolute`) or from its directory.
struct Link {
    at: Vec<u64>,
    absolute: bool,
    to: Vec<Seg>,
}

enum Rule {
    Tree(Vec<Seg>),
    Dir(Vec<Seg>),
    Named(u64),
}

/// An access of a query: its auto set (effect codes) and the answer.
struct Check {
    auto: Vec<u8>,
    answer: Answer,
}

struct Query {
    checks: Vec<Check>,
    path: Vec<Seg>,
}

struct Put {
    answer: Answer,
    value: u64,
    path: Vec<Seg>,
}

/// One scenario, over the temp dir's model names.
struct Plan {
    dirs: Vec<Vec<u64>>,
    /// Each file's location and value.
    files: Vec<(Vec<u64>, u64)>,
    links: Vec<Link>,
    roots: Vec<Vec<Seg>>,
    rules: Vec<Rule>,
    secret: Vec<Vec<Seg>>,
    queries: Vec<Query>,
    auto: Vec<u8>,
    puts: Vec<Put>,
}

fn names(at: &[u64]) -> Vec<Seg> {
    at.iter().copied().map(Seg::Name).collect()
}

fn tail(rng: &mut Rng, count: u64) -> Vec<Seg> {
    (0..count)
        .map(|_| match rng.below(20) {
            0..=11 => Seg::Name(rng.below(NAMES)),
            12..=17 => Seg::Up,
            18.. => Seg::Here,
        })
        .collect()
}

fn auto(rng: &mut Rng, write: u64) -> Vec<u8> {
    ShellEffect::ALL
        .into_iter()
        .filter(|effect| match effect {
            ShellEffect::Write => rng.chance(write),
            ShellEffect::Read | ShellEffect::Exec | ShellEffect::Net => rng.chance(60),
            ShellEffect::Outside | ShellEffect::Protected | ShellEffect::Secret => rng.chance(20),
        })
        .map(ShellEffect::code)
        .collect()
}

impl Plan {
    fn new(rng: &mut Rng, top: &[u64]) -> Self {
        let mut plan = Plan {
            dirs: vec![top.to_vec()],
            files: Vec::new(),
            links: Vec::new(),
            roots: Vec::new(),
            rules: Vec::new(),
            secret: Vec::new(),
            queries: Vec::new(),
            auto: Vec::new(),
            puts: Vec::new(),
        };
        let mut taken: BTreeSet<Vec<u64>> = BTreeSet::new();
        let mut free = |rng: &mut Rng, dirs: &[Vec<u64>]| {
            let dir = rng.below(dirs.len() as u64);
            let mut at = dirs[usize::try_from(dir).unwrap()].clone();
            at.push(rng.below(NAMES));
            taken.insert(at.clone()).then_some(at)
        };
        for _ in 0..rng.range(1, 4) {
            plan.dirs.extend(free(rng, &plan.dirs.clone()));
        }
        for value in 1..=rng.range(1, 4) {
            if let Some(at) = free(rng, &plan.dirs) {
                plan.files.push((at, value));
            }
        }
        for _ in 0..rng.range(1, 5) {
            let Some(at) = free(rng, &plan.dirs) else {
                continue;
            };
            let link = match rng.below(10) {
                // A loop to itself.
                0 | 1 => Link {
                    to: vec![Seg::Name(*at.last().unwrap())],
                    at,
                    absolute: false,
                },
                // From `/`: the temp dir, or a location of the tree.
                2..=5 => {
                    let mut to = match rng.below(3) {
                        0 => names(top),
                        1.. => names(&plan.spot(rng, top)),
                    };
                    let count = rng.below(3);
                    to.extend(tail(rng, count));
                    Link {
                        at,
                        absolute: true,
                        to,
                    }
                }
                6.. => {
                    let count = rng.range(1, 3);
                    Link {
                        at,
                        absolute: false,
                        to: tail(rng, count),
                    }
                }
            };
            plan.links.push(link);
        }
        let roots = rng.pick(&[0, 1, 1, 1, 2]).unwrap();
        for _ in 0..roots {
            let root = if rng.chance(60) {
                names(top)
            } else {
                plan.path(rng, top)
            };
            plan.roots.push(root);
        }
        for _ in 0..rng.below(4) {
            let rule = match rng.below(3) {
                0 => Rule::Tree(plan.path(rng, top)),
                1 => Rule::Dir(plan.path(rng, top)),
                2.. if rng.chance(10) => Rule::Named(*top.last().unwrap()),
                2.. => Rule::Named(rng.below(NAMES)),
            };
            plan.rules.push(rule);
        }
        for _ in 0..rng.below(3) {
            let entry = plan.path(rng, top);
            plan.secret.push(entry);
        }
        for _ in 0..6 {
            let checks = ACCESSES
                .iter()
                .map(|_| Check {
                    auto: auto(rng, 60),
                    answer: rng.pick(&[Answer::Yes, Answer::No, Answer::Gone]).unwrap(),
                })
                .collect();
            let path = plan.path(rng, top);
            plan.queries.push(Query { checks, path });
        }
        plan.auto = auto(rng, 80);
        for value in 1000..1006 {
            let path = if !plan.files.is_empty() && rng.chance(40) {
                let file = rng.below(plan.files.len() as u64);
                let mut path = names(&plan.files[usize::try_from(file).unwrap()].0);
                let count = rng.below(2);
                path.extend(tail(rng, count));
                path
            } else {
                plan.path(rng, top)
            };
            let answer = rng.pick(&[Answer::No, Answer::Gone]).unwrap();
            plan.puts.push(Put {
                answer,
                value,
                path,
            });
        }
        plan
    }

    /// A location: the temp dir or one of its ancestors, a directory, a
    /// file or a link.
    fn spot(&self, rng: &mut Rng, top: &[u64]) -> Vec<u64> {
        let links: Vec<&[u64]> = self.links.iter().map(|link| link.at.as_slice()).collect();
        let files: Vec<&[u64]> = self.files.iter().map(|file| file.0.as_slice()).collect();
        let dirs: Vec<&[u64]> = self.dirs.iter().map(Vec::as_slice).collect();
        let picked = match rng.below(10) {
            0 => {
                let depth = rng.below(top.len() as u64);
                Some(&top[..usize::try_from(depth).unwrap()])
            }
            1 | 2 => rng.pick(&links),
            3 | 4 => rng.pick(&files),
            5.. => rng.pick(&dirs),
        };
        picked.unwrap_or(top).to_vec()
    }

    /// A path from `/`: a location, sometimes through a `..` above the
    /// temp dir and back, then a few more segments.
    fn path(&self, rng: &mut Rng, top: &[u64]) -> Vec<Seg> {
        let spot = self.spot(rng, top);
        let mut path = match spot.strip_prefix(top) {
            Some(below) if rng.chance(15) => {
                let mut path = names(top);
                path.extend([Seg::Up, Seg::Name(*top.last().unwrap())]);
                path.extend(names(below));
                path
            }
            Some(_) | None => names(&spot),
        };
        let count = rng.below(3);
        path.extend(tail(rng, count));
        path
    }

    /// The scenario's events (`bend/bridge_path_policy.bend`).
    fn events(&self) -> String {
        let segs = |segs: &[Seg]| {
            segs.iter().fold(String::new(), |mut shown, seg| {
                write!(shown, " {}", seg.token()).unwrap();
                shown
            })
        };
        let auto = |auto: &[u8]| format!("a{}", auto.iter().map(u8::to_string).collect::<String>());
        let mut events = String::new();
        for link in &self.links {
            let absolute = u8::from(link.absolute);
            writeln!(
                events,
                "k {absolute}{} ;{}",
                segs(&names(&link.at)),
                segs(&link.to)
            )
            .unwrap();
        }
        for root in &self.roots {
            writeln!(events, "r{}", segs(root)).unwrap();
        }
        for rule in &self.rules {
            match rule {
                Rule::Tree(path) => writeln!(events, "t{}", segs(path)).unwrap(),
                Rule::Dir(path) => writeln!(events, "d{}", segs(path)).unwrap(),
                Rule::Named(name) => writeln!(events, "m n{name}").unwrap(),
            }
        }
        for entry in &self.secret {
            writeln!(events, "s{}", segs(entry)).unwrap();
        }
        for (at, value) in &self.files {
            writeln!(events, "c {value}{}", segs(&names(at))).unwrap();
        }
        for query in &self.queries {
            events.push('q');
            for check in &query.checks {
                write!(events, " {} {}", auto(&check.auto), check.answer.token()).unwrap();
            }
            writeln!(events, "{}", segs(&query.path)).unwrap();
        }
        writeln!(events, "x {}", auto(&self.auto)).unwrap();
        for put in &self.puts {
            writeln!(
                events,
                "w {} {}{}",
                put.answer.token(),
                put.value,
                segs(&put.path)
            )
            .unwrap();
        }
        events
    }
}

/// The real gate over `policy` with the auto set `auto`; its sink answers
/// `answer` and keeps each question in `asked`.
fn gate(
    policy: &PathPolicy,
    auto: &[u8],
    answer: Answer,
    asked: &Arc<Mutex<VecDeque<String>>>,
    runtime: &tokio::runtime::Handle,
) -> DocumentsGate {
    let log = Arc::clone(asked);
    let sink: ShellApprovalSink = Arc::new(move |request: ShellApprovalRequest| {
        log.lock().unwrap().push_back(request.command);
        async move { answer.verdict() }.boxed()
    });
    DocumentsGate {
        policy: policy.clone(),
        auto: AutoSet::new(auto.iter().map(|code| ShellEffect::ALL[usize::from(*code)])),
        sink: Some(sink),
        call: "bridge".to_owned(),
        asked: AtomicU64::new(0),
        runtime: runtime.clone(),
    }
}

/// The regular files under `dir`, links not followed, in name order.
fn files_under(dir: &Path, found: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    entries.sort();
    for entry in entries {
        let kind = std::fs::symlink_metadata(&entry).unwrap().file_type();
        if kind.is_dir() {
            files_under(&entry, found);
        } else if kind.is_file() {
            found.push(entry);
        }
    }
}

/// Build the plan's tree, run it, and print the transcript.
fn run(
    plan: &Plan,
    top: &Top,
    runtime: &tokio::runtime::Handle,
    reached: &mut BTreeSet<Case>,
) -> String {
    for dir in &plan.dirs {
        std::fs::create_dir_all(top.location(dir)).unwrap();
    }
    for (at, value) in &plan.files {
        std::fs::write(top.location(at), value.to_string()).unwrap();
    }
    for link in &plan.links {
        let target = if link.absolute {
            top.path(&link.to)
        } else {
            PathBuf::from(top.relative(&link.to))
        };
        std::os::unix::fs::symlink(target, top.location(&link.at)).unwrap();
    }
    let rules = plan
        .rules
        .iter()
        .map(|rule| match rule {
            Rule::Tree(path) => PathRule::Tree(top.path(path)),
            Rule::Dir(path) => PathRule::Dir(top.path(path)),
            Rule::Named(name) => PathRule::Named(top.name(*name).into()),
        })
        .collect();
    let policy = PathPolicy::new(
        plan.roots.iter().map(|root| top.path(root)).collect(),
        rules,
        plan.secret.iter().map(|entry| top.path(entry)).collect(),
    );
    let mut transcript = String::new();
    for query in &plan.queries {
        let absolute = top.path(&query.path);
        let real = resolve(&absolute);
        let looped = real.looped();
        let class = policy.class(&absolute);
        let holds = policy.holds_secret(&absolute);
        let (case, shown) = match class {
            PathClass::Inside => (Case::Inside, 'i'),
            PathClass::Outside => (Case::Outside, 'o'),
            PathClass::Protected => (Case::Protected, 'p'),
            PathClass::Secret => (Case::Secret, 's'),
        };
        reached.insert(case);
        if looped {
            reached.insert(Case::Looped);
            if !resolve(real.path()).looped() {
                reached.insert(Case::LoopedLeft);
            }
        }
        if holds && class != PathClass::Secret {
            reached.insert(Case::HoldsBelow);
        }
        write!(
            transcript,
            "q {} {shown} {}",
            u8::from(looped),
            u8::from(holds)
        )
        .unwrap();
        for (access, check) in ACCESSES.into_iter().zip(&query.checks) {
            let asked = Arc::new(Mutex::new(VecDeque::new()));
            let gate = gate(&policy, &check.auto, check.answer, &asked, runtime);
            let ran = gate.check(access, &real, "bridge").is_ok();
            let asked = !asked.lock().unwrap().is_empty();
            write!(transcript, " {}{}", u8::from(ran), u8::from(asked)).unwrap();
        }
        writeln!(transcript, "{}", top.shown(real.path())).unwrap();
    }
    let locks = tempfile::tempdir().unwrap();
    let documents = Documents::new(locks.path().to_path_buf(), None);
    for put in &plan.puts {
        let asked = Arc::new(Mutex::new(VecDeque::new()));
        let gate = gate(&policy, &plan.auto, put.answer, &asked, runtime);
        let path = top.path(&put.path);
        // A refused or failed write changes nothing; the files after the
        // trace show what the writes did.
        let written = documents.write(
            &top.dir,
            path.to_str().unwrap(),
            &put.value.to_string(),
            &gate,
        );
        let question = asked.lock().unwrap().pop_front();
        if let Some(command) = question {
            reached.insert(Case::WriteAsked);
            let real = command.strip_prefix("write ").unwrap_or(&command);
            writeln!(transcript, "w 1{}", top.shown(Path::new(real))).unwrap();
        } else {
            if written.is_ok() {
                reached.insert(Case::WriteRan);
            }
            writeln!(transcript, "w 0").unwrap();
        }
    }
    let guarded = |path: &Path| match policy.class(path) {
        PathClass::Protected | PathClass::Secret => true,
        PathClass::Inside | PathClass::Outside => false,
    };
    let planted: Vec<PathBuf> = plan.files.iter().map(|(at, _)| top.location(at)).collect();
    let mut found = Vec::new();
    files_under(&top.dir, &mut found);
    let created = found.into_iter().filter(|file| !planted.contains(file));
    for file in planted.iter().cloned().chain(created) {
        if guarded(&file) {
            reached.insert(Case::Guarded);
            let value = std::fs::read_to_string(&file).unwrap();
            writeln!(transcript, "g {value}{}", top.shown(&file)).unwrap();
        }
    }
    transcript
}

#[test]
fn path_policy_and_gate_match_the_model() {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap();
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let mut reached = BTreeSet::new();
    let mut scenarios = Vec::new();
    let mut dirs = Vec::new();
    for n in 0..SCENARIOS {
        let dir = tempfile::tempdir().unwrap();
        let top = Top::new(dir.path().canonicalize().unwrap());
        let plan = Plan::new(&mut rng, &top.at);
        let transcript = run(&plan, &top, runtime.handle(), &mut reached);
        scenarios.push(Scenario {
            name: format!("{n}"),
            events: plan.events(),
            transcript,
        });
        dirs.push(dir);
    }
    compare("bend/bridge_path_policy.bend", scenarios);
    assert_eq!(
        reached,
        BTreeSet::from([
            Case::Looped,
            Case::LoopedLeft,
            Case::Inside,
            Case::Outside,
            Case::Protected,
            Case::Secret,
            Case::HoldsBelow,
            Case::WriteAsked,
            Case::WriteRan,
            Case::Guarded,
        ])
    );
}
