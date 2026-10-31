# autoresearch/step: one event on autoresearch's state (port of oh-my-pi
# autoresearch tools init-experiment.ts, run-experiment.ts,
# log-experiment.ts): the state after it, the effect the host runs and
# whether the segment reached its cap; or a refusal that tells the model
# what to do instead (a refusal answers no state: the host keeps the old
# one). The rules:
#
# - init: a first init, or one with a new segment, needs the harness; the
#   metric's name must be a METRIC line's name; a cap is at least 1; on
#   the same segment the metric and its direction stay. Every init
#   abandons the pending run and sets the mode On.
# - a run starts with the next id (1, 2, ...), abandoning the pending one.
# - its output's METRIC lines set its metrics (the last value per name);
#   other lines change nothing; it finishes once, passed when it exits 0
#   and did not time out.
# - a log needs a finished pending run. keep: it passed, printed the
#   primary metric, and the metric is better than every kept run of the
#   segment that is not flagged (the first keep is the baseline); a keep
#   that left the scope needs a justification. crash: it did not pass.
#   checks_failed: it passed. discard: always. The logged metric is the
#   parsed one. Keep commits, the others reset. Once the segment logged
#   its cap of runs the step stops: the mode is Off.
# - a flag needs a logged run and a reason; flags stay.
#
# Pure: no IO, no @unsafe.

import Base
import ./dec.bend as D
import ./line.bend as L
import ./state.bend as S

def took(s: S.St) -> S.Res:
  S.Took{s, S.Nothing{}, False{}}

# Texts
# -----

def t_no_cfg() -> String:
  "autoresearch: no experiment yet; call autoresearch.init() first"

def t_harness() -> String:
  "autoresearch.init: build the benchmark harness first (a script that exits 0 and prints METRIC <name>=<value>), run it once, then call autoresearch.init() again"

def t_name() -> String:
  "autoresearch.init: the metric's name must be letters, digits, `_`, `.` or `-`: it names the METRIC <name>=<value> line"

def t_cap() -> String:
  "autoresearch.init: max_iterations must be at least 1"

def t_same() -> String:
  "autoresearch.init: a new metric or direction needs new_segment=True: the runs so far measure something else"

def t_next(n: Nat) -> String:
  String.append("autoresearch.run: the next run is ", Nat.show(n))

def t_idle() -> String:
  "autoresearch: no run is in progress"

def t_no_run() -> String:
  "autoresearch.log: no run to log; call autoresearch.run() first"

def t_running() -> String:
  "autoresearch.log: the run has not finished"

def t_failed_keep() -> String:
  "autoresearch.log: the run failed (a non-zero exit or a timeout), so it cannot be kept; log crash or discard"

def t_no_metric(n: String) -> String:
  String.append("autoresearch.log: the run printed no METRIC ", String.append(n, "=<value> line, so it cannot be kept; fix the harness, or log discard"))

def t_dir(d: S.Dir) -> String:
  match d:
    case S.Lower{}:
      "lower"
    case S.Higher{}:
      "higher"

def t_best(b: Maybe<&2, D.Dec>) -> String:
  match b:
    case None{}:
      "none"
    case Some{x}:
      D.show(x)

def t_worse(m: D.Dec, b: Maybe<&2, D.Dec>, d: S.Dir) -> String:
  String.append("autoresearch.log: ", String.append(D.show(m), String.append(" is not better than the best kept ", String.append(t_best(b), String.append(" (", String.append(t_dir(d), " is better); log discard"))))))

def t_justify() -> String:
  "autoresearch.log: the run changed files outside the scope; a keep needs a justification"

def t_passed() -> String:
  "autoresearch.log: the run passed; log keep, discard or checks_failed"

def t_failed() -> String:
  "autoresearch.log: the run failed; log crash or discard"

def t_reason() -> String:
  "autoresearch.flag: a flag needs a reason"

def t_not_logged(n: Nat) -> String:
  String.append("autoresearch.flag: there is no logged run ", Nat.show(n))

# Init
# ----

def name_ok.go(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(L.name_char(L.code(c)), name_ok.go(t))

# a METRIC line's name: at least one name char
def name_ok(+s: String) -> Bool:
  Bool.and(L.some(s), name_ok.go(s))

def cap_ok(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{n}:
      Nat.is_ne(n, 0n)

def init.err.max(ok: Bool) -> Maybe<&2, String>:
  match ok:
    case True{}:
      None{}
    case False{}:
      Some{t_cap()}

def init.err.name(ok: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, String>:
  match ok:
    case False{}:
      Some{t_name()}
    case True{}:
      init.err.max(cap_ok(m))

# what is wrong with a configuration, if anything
def init.err(+c: S.Cfg) -> Maybe<&2, String>:
  init.err.name(name_ok(S.Cfg.metric(c)), S.Cfg.max(c))

def dir_eq(a: S.Dir, b: S.Dir) -> Bool:
  match a b:
    case S.Lower{} S.Lower{}:
      True{}
    case S.Lower{} S.Higher{}:
      False{}
    case S.Higher{} S.Lower{}:
      False{}
    case S.Higher{} S.Higher{}:
      True{}

# the new configuration keeps the old one's metric and direction
def same(+o: S.Cfg, +c: S.Cfg) -> Bool:
  Bool.and(String.eq(S.Cfg.metric(o), S.Cfg.metric(c)), dir_eq(S.Cfg.dir(o), S.Cfg.dir(c)))

# the state an accepted init leaves: the configuration, segment seg2,
# mode On, the pending run abandoned (under the old metric and segment)
def init.set(c: S.Cfg, seg2: Nat, +m: String, +seg: Nat, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  took(S.St{Some{c}, seg2, S.On{}, S.snoc(runs, S.abandon(m, seg, pend)), None{}})

def init.need(harness: Bool, c: S.Cfg, seg2: Nat, +m: String, +seg: Nat, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match harness:
    case True{}:
      init.set(c, seg2, m, seg, runs, pend)
    case False{}:
      S.Refuse{t_harness()}

def init.keep(ok: Bool, c: S.Cfg, +m: String, +seg: Nat, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match ok:
    case True{}:
      init.set(c, seg, m, seg, runs, pend)
    case False{}:
      S.Refuse{t_same()}

def init.old(old: Maybe<&2, S.Cfg>, +c: S.Cfg, fresh: Bool, harness: Bool, +seg: Nat, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match old:
    case None{}:
      init.need(harness, c, seg, "", seg, runs, pend)
    case Some{+o}:
      match fresh:
        case True{}:
          init.need(harness, c, 1n+seg, S.Cfg.metric(o), seg, runs, pend)
        case False{}:
          init.keep(same(o, c), c, S.Cfg.metric(o), seg, runs, pend)

def init.check(e: Maybe<&2, String>, old: Maybe<&2, S.Cfg>, c: S.Cfg, fresh: Bool, harness: Bool, seg: Nat, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match e:
    case Some{t}:
      S.Refuse{t}
    case None{}:
      init.old(old, c, fresh, harness, seg, runs, pend)

def init(s: S.St, +c: S.Cfg, fresh: Bool, harness: Bool) -> S.Res:
  match s:
    case S.St{old, seg, mode, runs, pend}:
      init.check(init.err(c), old, c, fresh, harness, seg, runs, pend)

# A run starts
# ------------

def begin.at(ok: Bool, +n: Nat, +c: S.Cfg, +seg: Nat, mode: S.Mode, runs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match ok:
    case True{}:
      took(S.St{Some{c}, seg, mode, S.snoc(runs, S.abandon(S.Cfg.metric(c), seg, pend)), Some{S.Pend{n, Nil{}, None{}}}})
    case False{}:
      S.Refuse{t_next(n)}

def begin(s: S.St, +run: Nat) -> S.Res:
  match s:
    case S.St{cfg, seg, mode, +runs, +pend}:
      match cfg:
        case None{}:
          S.Refuse{t_no_cfg()}
        case Some{+c}:
          +n = {1n+Nat.add(S.rlen(runs), S.pcount(pend)) : Nat}
          begin.at(Nat.is_eq(run, n), n, c, seg, mode, runs, pend)

# Its output
# ----------

def line.got(m: Maybe<&2, L.Kv>, cfg: Maybe<&2, S.Cfg>, seg: Nat, mode: S.Mode, runs: List<&2, S.Row>, id: Nat, kvs: List<&2, L.Kv>) -> S.Res:
  match m:
    case None{}:
      took(S.St{cfg, seg, mode, runs, Some{S.Pend{id, kvs, None{}}}})
    case Some{L.Kv{n, d}}:
      took(S.St{cfg, seg, mode, runs, Some{S.Pend{id, S.put(kvs, n, d), None{}}}})

def line(s: S.St, text: String) -> S.Res:
  match s:
    case S.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          S.Refuse{t_idle()}
        case Some{S.Pend{id, kvs, fin}}:
          match fin:
            case Some{p}:
              S.Refuse{t_idle()}
            case None{}:
              line.got(L.metric(text), cfg, seg, mode, runs, id, kvs)

# a run that exits with code `code` (negative when neg), timed out or not,
# passed when it exits 0 in time
def ok_exit(neg: Bool, code: Nat, timeout: Bool) -> Bool:
  Bool.and(Bool.not(neg), Bool.and(Nat.is_eq(code, 0n), Bool.not(timeout)))

def finish(s: S.St, neg: Bool, code: Nat, timeout: Bool) -> S.Res:
  match s:
    case S.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          S.Refuse{t_idle()}
        case Some{S.Pend{id, kvs, fin}}:
          match fin:
            case Some{p}:
              S.Refuse{t_idle()}
            case None{}:
              took(S.St{cfg, seg, mode, runs, Some{S.Pend{id, kvs, Some{ok_exit(neg, code, timeout)}}}})

# A log
# -----

def capped.max(m: Maybe<&2, Nat>, n: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{k}:
      Nat.is_le(k, n)

# the segment reached its cap after n logged runs
def capped(c: Maybe<&2, S.Cfg>, n: Nat) -> Bool:
  match c:
    case None{}:
      False{}
    case Some{k}:
      capped.max(S.Cfg.max(k), n)

def log.mode(stop: Bool, mode: S.Mode) -> S.Mode:
  match stop:
    case True{}:
      S.Off{}
    case False{}:
      mode

def log.end(+stop: Bool, cfg: Maybe<&2, S.Cfg>, seg: Nat, mode: S.Mode, runs: List<&2, S.Row>, eff: S.Eff) -> S.Res:
  S.Took{S.St{cfg, seg, log.mode(stop, mode), runs, None{}}, eff, stop}

# the run logged with status st: its row appended, no pending run, the
# effect, and the stop once the segment logged its cap
def log.done(+cfg: Maybe<&2, S.Cfg>, +seg: Nat, mode: S.Mode, runs: List<&2, S.Row>, p: S.Pend, st: S.Status, desc: String, eff: S.Eff) -> S.Res:
  +runs2 = S.snoc(runs, [S.row(S.primary(cfg), seg, p, Some{st}, desc)])
  log.end(capped(cfg, S.logged(runs2, seg)), cfg, seg, mode, runs2, eff)

def justified(w: Maybe<&2, String>) -> Bool:
  match w:
    case None{}:
      False{}
    case Some{t}:
      L.some(t)

def keep.why(ok: Bool, +cfg: Maybe<&2, S.Cfg>, +seg: Nat, mode: S.Mode, runs: List<&2, S.Row>, p: S.Pend, desc: String) -> S.Res:
  match ok:
    case True{}:
      log.done(cfg, seg, mode, runs, p, S.Keep{}, desc, S.Commit{})
    case False{}:
      S.Refuse{t_justify()}

def keep.beats(ok: Bool, +m: D.Dec, +dir: S.Dir, why: Maybe<&2, String>, devs: Nat, +cfg: Maybe<&2, S.Cfg>, +seg: Nat, mode: S.Mode, +runs: List<&2, S.Row>, p: S.Pend, desc: String) -> S.Res:
  match ok:
    case True{}:
      keep.why(Bool.or(Nat.is_eq(devs, 0n), justified(why)), cfg, seg, mode, runs, p, desc)
    case False{}:
      S.Refuse{t_worse(m, S.last(runs, seg), dir)}

def keep.metric(m: Maybe<&2, D.Dec>, +c: S.Cfg, why: Maybe<&2, String>, devs: Nat, +seg: Nat, mode: S.Mode, +runs: List<&2, S.Row>, p: S.Pend, desc: String) -> S.Res:
  match m:
    case None{}:
      S.Refuse{t_no_metric(S.Cfg.metric(c))}
    case Some{+x}:
      keep.beats(S.beats(S.Cfg.dir(c), x, runs, seg), x, S.Cfg.dir(c), why, devs, Some{c}, seg, mode, runs, p, desc)

def keep.cfg(cfg: Maybe<&2, S.Cfg>, why: Maybe<&2, String>, devs: Nat, +seg: Nat, mode: S.Mode, +runs: List<&2, S.Row>, +p: S.Pend, desc: String) -> S.Res:
  match cfg:
    case None{}:
      S.Refuse{t_no_cfg()}
    case Some{+c}:
      keep.metric(S.lookup(S.Pend.kvs(p), S.Cfg.metric(c)), c, why, devs, seg, mode, runs, p, desc)

def keep(passed: Bool, cfg: Maybe<&2, S.Cfg>, why: Maybe<&2, String>, devs: Nat, +seg: Nat, mode: S.Mode, +runs: List<&2, S.Row>, +p: S.Pend, desc: String) -> S.Res:
  match passed:
    case True{}:
      keep.cfg(cfg, why, devs, seg, mode, runs, p, desc)
    case False{}:
      S.Refuse{t_failed_keep()}

def log.need(ok: Bool, text: String, +cfg: Maybe<&2, S.Cfg>, +seg: Nat, mode: S.Mode, runs: List<&2, S.Row>, p: S.Pend, st: S.Status, desc: String) -> S.Res:
  match ok:
    case True{}:
      log.done(cfg, seg, mode, runs, p, st, desc, S.Reset{})
    case False{}:
      S.Refuse{text}

def log.status(st: S.Status, passed: Bool, desc: String, why: Maybe<&2, String>, devs: Nat, +cfg: Maybe<&2, S.Cfg>, +seg: Nat, mode: S.Mode, +runs: List<&2, S.Row>, +p: S.Pend) -> S.Res:
  match st:
    case S.Keep{}:
      keep(passed, cfg, why, devs, seg, mode, runs, p, desc)
    case S.Discard{}:
      log.done(cfg, seg, mode, runs, p, S.Discard{}, desc, S.Reset{})
    case S.Crash{}:
      log.need(Bool.not(passed), t_passed(), cfg, seg, mode, runs, p, S.Crash{}, desc)
    case S.Checks{}:
      log.need(passed, t_failed(), cfg, seg, mode, runs, p, S.Checks{}, desc)

def log.fin(fin: Maybe<&2, Bool>, st: S.Status, desc: String, why: Maybe<&2, String>, devs: Nat, cfg: Maybe<&2, S.Cfg>, seg: Nat, mode: S.Mode, runs: List<&2, S.Row>, p: S.Pend) -> S.Res:
  match fin:
    case None{}:
      S.Refuse{t_running()}
    case Some{passed}:
      log.status(st, passed, desc, why, devs, cfg, seg, mode, runs, p)

def log(s: S.St, st: S.Status, desc: String, why: Maybe<&2, String>, devs: Nat) -> S.Res:
  match s:
    case S.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          S.Refuse{t_no_run()}
        case Some{+p}:
          log.fin(S.Pend.fin(p), st, desc, why, devs, cfg, seg, mode, runs, p)

# A flag
# ------

def flag.set(r: S.Row) -> S.Row:
  match r:
    case S.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      S.Row{id, sg, st, m, ms, ps, fn, True{}, desc}

# r is the logged run n
def flag.hit(r: S.Row, +n: Nat) -> Bool:
  match r:
    case S.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      Bool.and(Nat.is_eq(id, n), S.has(st))

def flag.at(hit: Bool, r: S.Row, t: List<&2, S.Row>, rest: List<&2, S.Row> & Bool) -> List<&2, S.Row> & Bool:
  match hit:
    case True{}:
      (flag.set(r) <> t, True{})
    case False{}:
      (rs, found) = rest
      (r <> rs, found)

# the rows with the first logged run n flagged, and whether there is one
def flag.rows(rs: List<&2, S.Row>, +n: Nat) -> List<&2, S.Row> & Bool:
  match rs:
    case Nil{}:
      (Nil{}, False{})
    case +r <> +t:
      flag.at(flag.hit(r, n), r, t, flag.rows(t, n))

def flag.end(found: Bool, n: Nat, cfg: Maybe<&2, S.Cfg>, seg: Nat, mode: S.Mode, rs: List<&2, S.Row>, pend: Maybe<&2, S.Pend>) -> S.Res:
  match found:
    case True{}:
      took(S.St{cfg, seg, mode, rs, pend})
    case False{}:
      S.Refuse{t_not_logged(n)}

def flag.found(r: List<&2, S.Row> & Bool, +n: Nat, cfg: Maybe<&2, S.Cfg>, seg: Nat, mode: S.Mode, pend: Maybe<&2, S.Pend>) -> S.Res:
  (rs, found) = r
  flag.end(found, n, cfg, seg, mode, rs, pend)

def flag.reason(ok: Bool, s: S.St, +n: Nat) -> S.Res:
  match ok:
    case True{}:
      match s:
        case S.St{cfg, seg, mode, runs, pend}:
          flag.found(flag.rows(runs, n), n, cfg, seg, mode, pend)
    case False{}:
      S.Refuse{t_reason()}

def flag(s: S.St, +n: Nat, reason: String) -> S.Res:
  flag.reason(L.some(reason), s, n)

# The step
# --------

def set_mode(s: S.St, m: S.Mode) -> S.Res:
  match s:
    case S.St{cfg, seg, mode, runs, pend}:
      took(S.St{cfg, seg, m, runs, pend})

# one event on state s
def step(s: S.St, e: S.Ev) -> S.Res:
  match e:
    case S.Init{c, fresh, harness}:
      init(s, c, fresh, harness)
    case S.Begin{n}:
      begin(s, n)
    case S.Line{text}:
      line(s, text)
    case S.Finish{neg, code, timeout}:
      finish(s, neg, code, timeout)
    case S.Log{st, desc, why, devs}:
      log(s, st, desc, why, devs)
    case S.Flag{n, reason}:
      flag(s, n, reason)
    case S.SetMode{m}:
      set_mode(s, m)
