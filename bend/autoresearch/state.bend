# autoresearch/state: what autoresearch knows (port of oh-my-pi
# autoresearch state.ts and the runs of storage.ts): the experiment's
# configuration, its segment, the mode, the runs that ended (logged or
# abandoned, oldest first) and the pending run; the events that change it
# (autoresearch/step.bend); the metrics a snapshot shows: the segment's
# baseline (its first kept run that is not flagged), best (its last such
# run: each keep must beat every one before it) and how many runs it
# logged. Pure: no IO, no @unsafe.

import Base
import ./dec.bend as D
import ./line.bend as L

# which way the metric improves
type Dir is Data:
  Lower{}
  Higher{}

# what a logged run became
type Status is Data:
  Keep{}
  Discard{}
  Crash{}
  Checks{}

# whether the loop runs
type Mode is Data:
  On{}
  Off{}

# the experiment: name, goal, the primary metric's name and unit, its
# direction, the secondary metrics' names, the paths in scope and off
# limits, and the most runs a segment logs
type Cfg is Data:
  Cfg{name: String, goal: String, metric: String, unit: String, dir: Dir, secondary: List<&2, String>, scope: List<&2, String>, off: List<&2, String>, max: Maybe<&2, Nat>}

# a run: its id, segment, status (none: abandoned, or pending), primary
# metric, the other metrics it printed, whether it passed (exit 0, no
# timeout), finished and is flagged, and its description
type Row is Data:
  Row{id: Nat, seg: Nat, status: Maybe<&2, Status>, metric: Maybe<&2, D.Dec>, metrics: List<&2, L.Kv>, passed: Bool, finished: Bool, flagged: Bool, desc: String}

# the pending run: its id, the metrics its output printed so far (last
# value per name), and, once it finished, whether it passed
type Pend is Data:
  Pend{id: Nat, kvs: List<&2, L.Kv>, fin: Maybe<&2, Bool>}

# autoresearch's state
type St is Data:
  St{cfg: Maybe<&2, Cfg>, seg: Nat, mode: Mode, runs: List<&2, Row>, pend: Maybe<&2, Pend>}

# an event: autoresearch.init() (the configuration; a new segment; the
# harness exists), a run starts (its id), a line of its output, it ends
# (exit code: sign and size; timed out), autoresearch.log() (status,
# description, justification, how many changed paths leave the scope), a
# run flagged (id, reason), the mode set
type Ev is Data:
  Init{cfg: Cfg, fresh: Bool, harness: Bool}
  Begin{run: Nat}
  Line{text: String}
  Finish{neg: Bool, code: Nat, timeout: Bool}
  Log{status: Status, desc: String, why: Maybe<&2, String>, devs: Nat}
  Flag{run: Nat, reason: String}
  SetMode{mode: Mode}

# what the host does after an accepted event: nothing, commit the run's
# changes, or restore the tree to HEAD
type Eff is Data:
  Nothing{}
  Commit{}
  Reset{}

# a step: the state after an accepted event, its effect, and whether the
# segment reached its cap (the mode is then Off); or a refusal, which
# keeps the state
type Res is Data:
  Took{st: St, eff: Eff, stop: Bool}
  Refuse{text: String}

# no experiment, no run
def St.empty() -> St:
  St{None{}, 0n, Off{}, Nil{}, None{}}

def Cfg.metric(c: Cfg) -> String:
  match c:
    case Cfg{name, goal, metric, unit, dir, sec, scope, off, max}:
      metric

def Cfg.dir(c: Cfg) -> Dir:
  match c:
    case Cfg{name, goal, metric, unit, dir, sec, scope, off, max}:
      dir

def Cfg.max(c: Cfg) -> Maybe<&2, Nat>:
  match c:
    case Cfg{name, goal, metric, unit, dir, sec, scope, off, max}:
      max

def Pend.kvs(p: Pend) -> List<&2, L.Kv>:
  match p:
    case Pend{id, kvs, fin}:
      kvs

def Pend.fin(p: Pend) -> Maybe<&2, Bool>:
  match p:
    case Pend{id, kvs, fin}:
      fin

# Metrics of a run
# ----------------

def lookup.at(hit: Bool, v: D.Dec, r: Maybe<&2, D.Dec>) -> Maybe<&2, D.Dec>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      r

# the value of name x in kvs
def lookup(kvs: List<&2, L.Kv>, +x: String) -> Maybe<&2, D.Dec>:
  match kvs:
    case Nil{}:
      None{}
    case L.Kv{+k, v} <> t:
      lookup.at(String.eq(k, x), v, lookup(t, x))

def others.at(hit: Bool, k: String, v: D.Dec, r: List<&2, L.Kv>) -> List<&2, L.Kv>:
  match hit:
    case True{}:
      r
    case False{}:
      L.Kv{k, v} <> r

# kvs less name x
def others(kvs: List<&2, L.Kv>, +x: String) -> List<&2, L.Kv>:
  match kvs:
    case Nil{}:
      Nil{}
    case L.Kv{+k, v} <> t:
      others.at(String.eq(k, x), k, v, others(t, x))

def put.at(hit: Bool, k: String, v: D.Dec, t: List<&2, L.Kv>, n: String, d: D.Dec, r: List<&2, L.Kv>) -> List<&2, L.Kv>:
  match hit:
    case True{}:
      L.Kv{n, d} <> t
    case False{}:
      L.Kv{k, v} <> r

# kvs with name n worth d: in place, or last when new
def put(kvs: List<&2, L.Kv>, +n: String, +d: D.Dec) -> List<&2, L.Kv>:
  match kvs:
    case Nil{}:
      [L.Kv{n, d}]
    case L.Kv{+k, v} <> +t:
      put.at(String.eq(k, n), k, v, t, n, d, put(t, n, d))

# Rows
# ----

def primary(c: Maybe<&2, Cfg>) -> String:
  match c:
    case None{}:
      ""
    case Some{Cfg{name, goal, metric, unit, dir, sec, scope, off, max}}:
      metric

def passed(f: Maybe<&2, Bool>) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{p}:
      p

def finished(f: Maybe<&2, Bool>) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{p}:
      True{}

# the row of pending run p in segment seg, given its status and
# description (the metric is always the parsed one)
def row(+m: String, seg: Nat, p: Pend, st: Maybe<&2, Status>, desc: String) -> Row:
  match p:
    case Pend{id, +kvs, +fin}:
      Row{id, seg, st, lookup(kvs, m), others(kvs, m), passed(fin), finished(fin), False{}, desc}

# the rows the pending run leaves when it is abandoned: none, or one
def abandon(+m: String, seg: Nat, p: Maybe<&2, Pend>) -> List<&2, Row>:
  match p:
    case None{}:
      Nil{}
    case Some{q}:
      [row(m, seg, q, None{}, "")]

# rs, then r
def snoc(rs: List<&2, Row>, r: List<&2, Row>) -> List<&2, Row>:
  match rs:
    case Nil{}:
      r
    case x <> t:
      x <> snoc(t, r)

def rlen(rs: List<&2, Row>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case x <> t:
      1n+rlen(t)

def pcount(p: Maybe<&2, Pend>) -> Nat:
  match p:
    case None{}:
      0n
    case Some{q}:
      1n

# how many runs started
def St.started(s: St) -> Nat:
  match s:
    case St{c, seg, mode, runs, pend}:
      Nat.add(rlen(runs), pcount(pend))

# Segment metrics
# ---------------

def kept.st(st: Maybe<&2, Status>) -> Bool:
  match st:
    case None{}:
      False{}
    case Some{k}:
      match k:
        case Keep{}:
          True{}
        case Discard{}:
          False{}
        case Crash{}:
          False{}
        case Checks{}:
          False{}

def kept.of(ok: Bool, m: Maybe<&2, D.Dec>) -> Maybe<&2, D.Dec>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

# the metric of r when it is a kept run of segment seg that is not
# flagged
def kept(r: Row, +seg: Nat) -> Maybe<&2, D.Dec>:
  match r:
    case Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      kept.of(Bool.and(Nat.is_eq(sg, seg), Bool.and(kept.st(st), Bool.not(fl))), m)

def first.at(m: Maybe<&2, D.Dec>, r: Maybe<&2, D.Dec>) -> Maybe<&2, D.Dec>:
  match m:
    case None{}:
      r
    case Some{x}:
      Some{x}

# the first kept metric of the segment
def first(rs: List<&2, Row>, +seg: Nat) -> Maybe<&2, D.Dec>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      first.at(kept(r, seg), first(t, seg))

def last.at(m: Maybe<&2, D.Dec>, r: Maybe<&2, D.Dec>) -> Maybe<&2, D.Dec>:
  match r:
    case None{}:
      m
    case Some{x}:
      Some{x}

# the last kept metric of the segment
def last(rs: List<&2, Row>, +seg: Nat) -> Maybe<&2, D.Dec>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      last.at(kept(r, seg), last(t, seg))

def one(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def has(st: Maybe<&2, Status>) -> Bool:
  match st:
    case None{}:
      False{}
    case Some{k}:
      True{}

def logged.at(r: Row, +seg: Nat) -> Nat:
  match r:
    case Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      one(Bool.and(Nat.is_eq(sg, seg), has(st)))

# how many runs of the segment were logged (flagged ones too)
def logged(rs: List<&2, Row>, +seg: Nat) -> Nat:
  match rs:
    case Nil{}:
      0n
    case r <> t:
      Nat.add(logged.at(r, seg), logged(t, seg))

def St.baseline(s: St) -> Maybe<&2, D.Dec>:
  match s:
    case St{c, +seg, mode, runs, pend}:
      first(runs, seg)

def St.best(s: St) -> Maybe<&2, D.Dec>:
  match s:
    case St{c, +seg, mode, runs, pend}:
      last(runs, seg)

def St.logged(s: St) -> Nat:
  match s:
    case St{c, +seg, mode, runs, pend}:
      logged(runs, seg)

# Order
# -----

# a is better than b in direction dir
def better(dir: Dir, a: D.Dec, b: D.Dec) -> Bool:
  match dir:
    case Lower{}:
      Cmp.is_lt(D.Dec.cmp(a, b))
    case Higher{}:
      Cmp.is_gt(D.Dec.cmp(a, b))

def beats.at(+dir: Dir, +m: D.Dec, k: Maybe<&2, D.Dec>) -> Bool:
  match k:
    case None{}:
      True{}
    case Some{x}:
      better(dir, m, x)

# m is better than every kept metric of the segment
def beats(+dir: Dir, +m: D.Dec, rs: List<&2, Row>, +seg: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(beats.at(dir, m, kept(r, seg)), beats(dir, m, t, seg))
