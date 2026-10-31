# autoresearch (spec): one event on autoresearch's state, restated from
# the requirements (R1-R10, R13-R15) with the refusal texts of
# bend/autoresearch/step.bend, which are part of the contract. Each event
# is a transition: what it needs (the first unmet need, in the order
# written below, answers its refusal; a refusal keeps the state), else
# the state it leaves, the effect the host runs and whether the segment
# reached its cap. The METRIC parser (~parse), the order of metrics
# (~cmp) and the printer of a metric (~show) are parameters: the laws
# pass the shipped ones, which metric_line_reads / metric_line_sound,
# metric_order_exact and metric_print_round_trip pin on their own. A
# spec: the shipped code never calls it.

import Base
import ../../bend/autoresearch/dec.bend as D
import ../../bend/autoresearch/line.bend as L
import ../../bend/autoresearch/state.bend as S
import ./metric_line.bend as SL
import ./segment.bend as SG

# Refusals
# --------

def no_cfg() -> String:
  "autoresearch: no experiment yet; call autoresearch.init() first"

def no_harness() -> String:
  "autoresearch.init: build the benchmark harness first (a script that exits 0 and prints METRIC <name>=<value>), run it once, then call autoresearch.init() again"

def bad_name() -> String:
  "autoresearch.init: the metric's name must be letters, digits, `_`, `.` or `-`: it names the METRIC <name>=<value> line"

def bad_cap() -> String:
  "autoresearch.init: max_iterations must be at least 1"

def new_kind() -> String:
  "autoresearch.init: a new metric or direction needs new_segment=True: the runs so far measure something else"

def not_next(n: Nat) -> String:
  String.append("autoresearch.run: the next run is ", Nat.show(n))

def idle() -> String:
  "autoresearch: no run is in progress"

def nothing_to_log() -> String:
  "autoresearch.log: no run to log; call autoresearch.run() first"

def still_running() -> String:
  "autoresearch.log: the run has not finished"

def failed_keep() -> String:
  "autoresearch.log: the run failed (a non-zero exit or a timeout), so it cannot be kept; log crash or discard"

def no_metric(n: String) -> String:
  String.append("autoresearch.log: the run printed no METRIC ", String.append(n, "=<value> line, so it cannot be kept; fix the harness, or log discard"))

def dir_word(d: S.Dir) -> String:
  match d:
    case S.Lower{}:
      "lower"
    case S.Higher{}:
      "higher"

def best_word(~show: D.Dec -> String, b: Maybe<&2, D.Dec>) -> String:
  match b:
    case None{}:
      "none"
    case Some{x}:
      show(x)

def not_better(~show: D.Dec -> String, m: D.Dec, b: Maybe<&2, D.Dec>, d: S.Dir) -> String:
  String.append("autoresearch.log: ", String.append(show(m), String.append(" is not better than the best kept ", String.append(best_word(~show, b), String.append(" (", String.append(dir_word(d), " is better); log discard"))))))

def unjustified() -> String:
  "autoresearch.log: the run changed files outside the scope; a keep needs a justification"

def passed_crash() -> String:
  "autoresearch.log: the run passed; log keep, discard or checks_failed"

def failed_checks() -> String:
  "autoresearch.log: the run failed; log crash or discard"

def no_reason() -> String:
  "autoresearch.flag: a flag needs a reason"

def not_logged(n: Nat) -> String:
  String.append("autoresearch.flag: there is no logged run ", Nat.show(n))

# Configurations
# --------------

def cfg_metric(c: S.Cfg) -> String:
  match c:
    case S.Cfg{name, goal, metric, unit, dir, sec, scope, off, max}:
      metric

def cfg_dir(c: S.Cfg) -> S.Dir:
  match c:
    case S.Cfg{name, goal, metric, unit, dir, sec, scope, off, max}:
      dir

def cfg_max(c: S.Cfg) -> Maybe<&2, Nat>:
  match c:
    case S.Cfg{name, goal, metric, unit, dir, sec, scope, off, max}:
      max

# the primary metric's name; none before the first init
def primary(c: Maybe<&2, S.Cfg>) -> String:
  match c:
    case None{}:
      ""
    case Some{k}:
      cfg_metric(k)

# a name a METRIC line can carry: one or more of A-Z a-z 0-9 _ . -
def name_ok(+n: String) -> Bool:
  Bool.and(SL.nonempty(n), SL.all_name(n))

# a cap, if any, of at least 1 run
def cap_ok(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{k}:
      match k:
        case 0n:
          False{}
        case 1n+j:
          True{}

def same_dir(a: S.Dir, b: S.Dir) -> Bool:
  match a b:
    case S.Lower{} S.Lower{}:
      True{}
    case S.Lower{} S.Higher{}:
      False{}
    case S.Higher{} S.Lower{}:
      False{}
    case S.Higher{} S.Higher{}:
      True{}

def at_cap.max(m: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{k}:
      Nat.is_le(k, n)

# the segment logged n runs and the configuration caps it at n or fewer
def at_cap(c: Maybe<&2, S.Cfg>, +n: Nat) -> Bool:
  match c:
    case None{}:
      False{}
    case Some{k}:
      at_cap.max(cfg_max(k), n)

# Runs
# ----

def kv_value.at(hit: Bool, v: D.Dec, later: Maybe<&2, D.Dec>) -> Maybe<&2, D.Dec>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      later

# the value the run printed for name x (R2 keeps one per name)
def kv_value(kvs: List<&2, L.Kv>, +x: String) -> Maybe<&2, D.Dec>:
  match kvs:
    case Nil{}:
      None{}
    case L.Kv{+k, v} <> t:
      kv_value.at(String.eq(k, x), v, kv_value(t, x))

def kv_drop.at(hit: Bool, k: String, v: D.Dec, later: List<&2, L.Kv>) -> List<&2, L.Kv>:
  match hit:
    case True{}:
      later
    case False{}:
      L.Kv{k, v} <> later

# the run's metrics other than x
def kv_drop(kvs: List<&2, L.Kv>, +x: String) -> List<&2, L.Kv>:
  match kvs:
    case Nil{}:
      Nil{}
    case L.Kv{+k, v} <> t:
      kv_drop.at(String.eq(k, x), k, v, kv_drop(t, x))

def kv_set.at(hit: Bool, k: String, v: D.Dec, t: List<&2, L.Kv>, n: String, d: D.Dec, later: List<&2, L.Kv>) -> List<&2, L.Kv>:
  match hit:
    case True{}:
      L.Kv{n, d} <> t
    case False{}:
      L.Kv{k, v} <> later

# R2: name n now worth d (the last value wins): its entry replaced where
# it stands, or a new entry at the end
def kv_set(kvs: List<&2, L.Kv>, +n: String, +d: D.Dec) -> List<&2, L.Kv>:
  match kvs:
    case Nil{}:
      [L.Kv{n, d}]
    case L.Kv{+k, v} <> +t:
      kv_set.at(String.eq(k, n), k, v, t, n, d, kv_set(t, n, d))

def fin_passed(f: Maybe<&2, Bool>) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{p}:
      p

def fin_done(f: Maybe<&2, Bool>) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{p}:
      True{}

# the row the pending run p becomes in segment seg, under primary metric
# m: its id, status and description; its primary metric apart from the
# others; whether it passed and finished; not flagged
def row_of(+m: String, seg: Nat, p: S.Pend, st: Maybe<&2, S.Status>, desc: String) -> S.Row:
  match p:
    case S.Pend{id, +kvs, +fin}:
      S.Row{id, seg, st, kv_value(kvs, m), kv_drop(kvs, m), fin_passed(fin), fin_done(fin), False{}, desc}

# R1, R7: the pending run, if any, ends abandoned: a row with no status
def gone(+m: String, seg: Nat, pend: Maybe<&2, S.Pend>) -> List<&2, S.Row>:
  match pend:
    case None{}:
      Nil{}
    case Some{p}:
      [row_of(m, seg, p, None{}, "")]

def count(rs: List<&2, S.Row>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case r <> t:
      1n+count(t)

def pend_count(pend: Maybe<&2, S.Pend>) -> Nat:
  match pend:
    case None{}:
      0n
    case Some{p}:
      1n

# the id of the next run: one more than the runs started so far
def next_id(runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> Nat:
  1n+Nat.add(count(runs), pend_count(pend))

def last_kept.or(k: Maybe<&2, D.Dec>, later: Maybe<&2, D.Dec>) -> Maybe<&2, D.Dec>:
  match later:
    case None{}:
      k
    case Some{x}:
      Some{x}

# the newest kept metric of the segment that is not flagged (each keep
# beats every one before it: the best, which a refused keep names)
def last_kept(rs: List<&2, S.Row>, +seg: Nat) -> Maybe<&2, D.Dec>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      last_kept.or(SG.kept(r, seg), last_kept(t, seg))

def has_status(st: Maybe<&2, S.Status>) -> Bool:
  match st:
    case None{}:
      False{}
    case Some{k}:
      True{}

# r is the logged run n (abandoned runs are not logged)
def logged_as(r: S.Row, +n: Nat) -> Bool:
  match r:
    case S.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      Bool.and(Nat.is_eq(id, n), has_status(st))

# some run of rs is the logged run n
def has_logged(rs: List<&2, S.Row>, +n: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +r <> t:
      Bool.or(logged_as(r, n), has_logged(t, n))

def flagged(r: S.Row) -> S.Row:
  match r:
    case S.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      S.Row{id, sg, st, m, ms, ps, fn, True{}, desc}

def mark.at(hit: Bool, r: S.Row, t: List<&2, S.Row>, later: List<&2, S.Row>) -> List<&2, S.Row>:
  match hit:
    case True{}:
      flagged(r) <> t
    case False{}:
      r <> later

# R8: the first row that is the logged run n, flagged; the others as
# they are
def mark(rs: List<&2, S.Row>, +n: Nat) -> List<&2, S.Row>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> +t:
      mark.at(logged_as(r, n), r, t, mark(t, n))

def why_given(w: Maybe<&2, String>) -> Bool:
  match w:
    case None{}:
      False{}
    case Some{t}:
      SL.nonempty(t)

def took(s: S.St) -> S.Res:
  S.Took{s, S.Nothing{}, False{}}

# Init (R7)
# ---------

# an accepted init: configuration c, segment seg2, mode On, the pending
# run abandoned under the old metric m and segment seg
def opened(c: S.Cfg, seg2: Nat, +m: String, +seg: Nat, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  took(S.St{Some{c}, seg2, S.On{}, List.append(&2, S.Row, runs, gone(m, seg, pend)), None{}})

# a first init or a new segment: it needs the harness
def init.fresh(harness: Bool, c: S.Cfg, seg2: Nat, +m: String, +seg: Nat, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match harness:
    case False{}:
      S.Refuse{no_harness()}
    case True{}:
      opened(c, seg2, m, seg, runs, pend)

# the same segment: the metric and direction must stay
def init.same(kind: Bool, c: S.Cfg, +m: String, +seg: Nat, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match kind:
    case False{}:
      S.Refuse{new_kind()}
    case True{}:
      opened(c, seg, m, seg, runs, pend)

def init.after(old: Maybe<&2, S.Cfg>, +c: S.Cfg, fresh: Bool, harness: Bool, +seg: Nat, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match old:
    case None{}:
      init.fresh(harness, c, seg, "", seg, runs, pend)
    case Some{+o}:
      match fresh:
        case True{}:
          init.fresh(harness, c, 1n+seg, cfg_metric(o), seg, runs, pend)
        case False{}:
          init.same(Bool.and(String.eq(cfg_metric(o), cfg_metric(c)), same_dir(cfg_dir(o), cfg_dir(c))), c, cfg_metric(o), seg, runs, pend)

# the configuration first: a METRIC name, then a cap of at least 1
def init.checked(name: Bool, cap: Bool, old: Maybe<&2, S.Cfg>, c: S.Cfg, fresh: Bool, harness: Bool, seg: Nat, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match name:
    case False{}:
      S.Refuse{bad_name()}
    case True{}:
      match cap:
        case False{}:
          S.Refuse{bad_cap()}
        case True{}:
          init.after(old, c, fresh, harness, seg, runs, pend)

def init(s: S.St, +c: S.Cfg, fresh: Bool, harness: Bool) -> S.Res:
  match s:
    case S.St{old, seg, mode, runs, pend}:
      init.checked(name_ok(cfg_metric(c)), cap_ok(cfg_max(c)), old, c, fresh, harness, seg, runs, pend)

# A run starts (R1)
# -----------------

# run n starts, the only pending one, with no metrics; the pending run
# before it, if any, ends abandoned
def start(ok: Bool, +n: Nat, +c: S.Cfg, +seg: Nat, mode: S.Mode, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match ok:
    case False{}:
      S.Refuse{not_next(n)}
    case True{}:
      took(S.St{Some{c}, seg, mode, List.append(&2, S.Row, runs, gone(cfg_metric(c), seg, pend)), Some{S.Pend{n, Nil{}, None{}}}})

def begin(s: S.St, +run: Nat) -> S.Res:
  match s:
    case S.St{cfg, seg, mode, +runs, +pend}:
      match cfg:
        case None{}:
          S.Refuse{no_cfg()}
        case Some{+c}:
          +n = next_id(runs, pend)
          start(Nat.is_eq(run, n), n, c, seg, mode, runs, pend)

# Output (R2) and the end of a run (R3)
# -------------------------------------

def output.kv(m: Maybe<&2, L.Kv>, kvs: List<&2, L.Kv>) -> List<&2, L.Kv>:
  match m:
    case None{}:
      kvs
    case Some{L.Kv{n, d}}:
      kv_set(kvs, n, d)

# a line of a running run's output: a METRIC line sets that metric
def output(~parse: String -> Maybe<&2, L.Kv>, s: S.St, text: String) -> S.Res:
  match s:
    case S.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          S.Refuse{idle()}
        case Some{S.Pend{id, kvs, fin}}:
          match fin:
            case Some{p}:
              S.Refuse{idle()}
            case None{}:
              took(S.St{cfg, seg, mode, runs, Some{S.Pend{id, output.kv(parse(text), kvs), None{}}}})

# a running run ends: it passed when it exits 0 (not negative) in time
def ended(s: S.St, neg: Bool, code: Nat, timeout: Bool) -> S.Res:
  match s:
    case S.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          S.Refuse{idle()}
        case Some{S.Pend{id, kvs, fin}}:
          match fin:
            case Some{p}:
              S.Refuse{idle()}
            case None{}:
              took(S.St{cfg, seg, mode, runs, Some{S.Pend{id, kvs, Some{Bool.and(Bool.not(neg), Bool.and(Nat.is_eq(code, 0n), Bool.not(timeout)))}}}})

# Logs (R4, R5, R6, R9, R14, R15)
# -------------------------------

def mode_after(stop: Bool, mode: S.Mode) -> S.Mode:
  match stop:
    case True{}:
      S.Off{}
    case False{}:
      mode

# the run logged: its row appended (status st, the parsed metric), no
# run pending, the effect; once the segment's logged runs (flagged ones
# too) reach the cap the step stops and the mode is Off
def logged.with(+stop: Bool, cfg: Maybe<&2, S.Cfg>, seg: Nat, mode: S.Mode, runs2: List<&2, S.Row>, eff: S.Eff) -> S.Res:
  S.Took{S.St{cfg, seg, mode_after(stop, mode), runs2, None{}}, eff, stop}

def logged(+cfg: Maybe<&2, S.Cfg>, +seg: Nat, mode: S.Mode, runs: List<&2, S.Row>, p: S.Pend, st: S.Status, desc: String, eff: S.Eff) -> S.Res:
  +runs2 = List.append(&2, S.Row, runs, [row_of(primary(cfg), seg, p, Some{st}, desc)])
  logged.with(at_cap(cfg, SG.logged_count(runs2, seg)), cfg, seg, mode, runs2, eff)

# a keep that beats the segment: a run that left the scope needs a
# justification
def keep.scope(ok: Bool, +cfg: Maybe<&2, S.Cfg>, +seg: Nat, mode: S.Mode, runs: List<&2, S.Row>, p: S.Pend, desc: String) -> S.Res:
  match ok:
    case False{}:
      S.Refuse{unjustified()}
    case True{}:
      logged(cfg, seg, mode, runs, p, S.Keep{}, desc, S.Commit{})

# R5, R14: strictly better than every kept run of the segment that is
# not flagged (none kept: the baseline)
def keep.better(~show: D.Dec -> String, ok: Bool, +x: D.Dec, +dir: S.Dir, why: Maybe<&2, String>, devs: Nat, +cfg: Maybe<&2, S.Cfg>, +seg: Nat, mode: S.Mode, +runs: List<&2, S.Row>, p: S.Pend, desc: String) -> S.Res:
  match ok:
    case False{}:
      S.Refuse{not_better(~show, x, last_kept(runs, seg), dir)}
    case True{}:
      keep.scope(Bool.or(Nat.is_eq(devs, 0n), why_given(why)), cfg, seg, mode, runs, p, desc)

# R5: the run printed the primary metric
def keep.metric(~cmp: D.Dec -> D.Dec -> Cmp, ~show: D.Dec -> String, m: Maybe<&2, D.Dec>, +c: S.Cfg, why: Maybe<&2, String>, devs: Nat, +seg: Nat, mode: S.Mode, +runs: List<&2, S.Row>, p: S.Pend, desc: String) -> S.Res:
  match m:
    case None{}:
      S.Refuse{no_metric(cfg_metric(c))}
    case Some{+x}:
      keep.better(~show, SG.all_beaten(~cmp, cfg_dir(c), x, runs, seg), x, cfg_dir(c), why, devs, Some{c}, seg, mode, runs, p, desc)

# R5: a run that passed, of an experiment
def keep(~cmp: D.Dec -> D.Dec -> Cmp, ~show: D.Dec -> String, passed: Bool, cfg: Maybe<&2, S.Cfg>, why: Maybe<&2, String>, devs: Nat, +seg: Nat, mode: S.Mode, +runs: List<&2, S.Row>, id: Nat, +kvs: List<&2, L.Kv>, desc: String) -> S.Res:
  match passed:
    case False{}:
      S.Refuse{failed_keep()}
    case True{}:
      match cfg:
        case None{}:
          S.Refuse{no_cfg()}
        case Some{+c}:
          keep.metric(~cmp, ~show, kv_value(kvs, cfg_metric(c)), c, why, devs, seg, mode, runs, S.Pend{id, kvs, Some{True{}}}, desc)

# R6: what each status needs of a finished run
def log.of(~cmp: D.Dec -> D.Dec -> Cmp, ~show: D.Dec -> String, st: S.Status, +passed: Bool, desc: String, why: Maybe<&2, String>, devs: Nat, +cfg: Maybe<&2, S.Cfg>, +seg: Nat, mode: S.Mode, +runs: List<&2, S.Row>, +id: Nat, +kvs: List<&2, L.Kv>) -> S.Res:
  match st:
    case S.Keep{}:
      keep(~cmp, ~show, passed, cfg, why, devs, seg, mode, runs, id, kvs, desc)
    case S.Discard{}:
      logged(cfg, seg, mode, runs, S.Pend{id, kvs, Some{passed}}, S.Discard{}, desc, S.Reset{})
    case S.Crash{}:
      match passed:
        case True{}:
          S.Refuse{passed_crash()}
        case False{}:
          logged(cfg, seg, mode, runs, S.Pend{id, kvs, Some{False{}}}, S.Crash{}, desc, S.Reset{})
    case S.Checks{}:
      match passed:
        case False{}:
          S.Refuse{failed_checks()}
        case True{}:
          logged(cfg, seg, mode, runs, S.Pend{id, kvs, Some{True{}}}, S.Checks{}, desc, S.Reset{})

# R4: a log needs a pending run that finished
def log(~cmp: D.Dec -> D.Dec -> Cmp, ~show: D.Dec -> String, s: S.St, st: S.Status, desc: String, why: Maybe<&2, String>, devs: Nat) -> S.Res:
  match s:
    case S.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          S.Refuse{nothing_to_log()}
        case Some{S.Pend{id, kvs, fin}}:
          match fin:
            case None{}:
              S.Refuse{still_running()}
            case Some{passed}:
              log.of(~cmp, ~show, st, passed, desc, why, devs, cfg, seg, mode, runs, id, kvs)

# Flags (R8) and the mode
# -----------------------

def flag.found(found: Bool, +n: Nat, cfg: Maybe<&2, S.Cfg>, seg: Nat, mode: S.Mode, marked: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match found:
    case False{}:
      S.Refuse{not_logged(n)}
    case True{}:
      took(S.St{cfg, seg, mode, marked, pend})

# a flag needs a reason and a logged run n; it flags that run only
def flag.why(ok: Bool, s: S.St, +n: Nat) -> S.Res:
  match ok:
    case False{}:
      S.Refuse{no_reason()}
    case True{}:
      match s:
        case S.St{cfg, seg, mode, +runs, pend}:
          flag.found(has_logged(runs, n), n, cfg, seg, mode, mark(runs, n), pend)

def flag(s: S.St, +n: Nat, reason: String) -> S.Res:
  flag.why(SL.nonempty(reason), s, n)

def set_mode(s: S.St, m: S.Mode) -> S.Res:
  match s:
    case S.St{cfg, seg, mode, runs, pend}:
      took(S.St{cfg, seg, m, runs, pend})

# The step
# --------

# one event on state s
def step(~cmp: D.Dec -> D.Dec -> Cmp, ~parse: String -> Maybe<&2, L.Kv>, ~show: D.Dec -> String, s: S.St, e: S.Ev) -> S.Res:
  match e:
    case S.Init{c, fresh, harness}:
      init(s, c, fresh, harness)
    case S.Begin{n}:
      begin(s, n)
    case S.Line{text}:
      output(~parse, s, text)
    case S.Finish{neg, code, timeout}:
      ended(s, neg, code, timeout)
    case S.Log{st, desc, why, devs}:
      log(~cmp, ~show, s, st, desc, why, devs)
    case S.Flag{n, reason}:
      flag(s, n, reason)
    case S.SetMode{m}:
      set_mode(s, m)
