# ffi_autoresearch: the stepper of the compiled Bend core for
# autoresearch (Rust: crates/eukhe-bend/src/rules/autoresearch.rs, `Lab`;
# host: eukhe-core's autoresearch tools). Its state is autoresearch's
# state (bend/autoresearch/state.bend), kept in the Bend heap. The host
# sends each event as it happens (autoresearch.init(), a run's start,
# each line of its output, its end, autoresearch.log(), a flag, the
# mode) and reads what to do; it asks for a snapshot when it shows the
# state. The codec is the wire format of bend/wire.bend
# (crates/eukhe-bend/WIRE.md):
#
#   open    (nothing)                                     reply: T
#   step    Q                                             reply: per Q
#   Q       0 Cfg, new segment: Bool, harness: Bool       Res
#           1 run: Nat (a run starts)                     Res
#           2 text: String (a line of its output)         Res
#           3 negative: Bool, code: Nat, timed out: Bool  Res
#           4 Status, description: String,
#             justification: Maybe String, deviations: Nat Res
#           5 run: Nat, reason: String (a flag)           Res
#           6 Mode                                        Res
#           7 (a snapshot)                                Snap
#   Cfg     name, goal, metric, unit: String, Dir, secondary, scope,
#           off limits: List String, max iterations: Maybe Nat
#   Dir     0 lower | 1 higher       Mode    0 on | 1 off
#   Status  0 keep | 1 discard | 2 crash | 3 checks_failed
#   Res     0 Eff, stopped: Bool | 1 refusal: String
#   Eff     0 nothing | 1 commit | 2 reset
#   Snap    Maybe Cfg, segment: Nat, Mode, List Row, pending: Maybe Nat,
#           baseline: Maybe Dec, best: Maybe Dec, logged: Nat,
#           confidence (tenths): Maybe Nat
#   Row     id, segment: Nat, Maybe Status, abandoned, finished: Bool,
#           metric: Maybe Dec, metrics: List (String, Dec), passed,
#           flagged: Bool, description: String
#   Dec     negative: Bool, digits: List Nat, scale: Nat
#
# A refusal keeps the state. A malformed request (or one with input left
# over) keeps the state and answers `E autoresearch: malformed request`;
# an open with input opens the refused state and answers `E autoresearch:
# malformed open`; the refused state answers every step `E autoresearch:
# the open was refused`. laws/autoresearch.bend pins the entry. Pure: no
# IO, no @unsafe.

import Base
import ./wire.bend as W
import ./autoresearch/dec.bend as D
import ./autoresearch/line.bend as L
import ./autoresearch/state.bend as S
import ./autoresearch/step.bend as P
import ./autoresearch/stats.bend as T

# a request: an event or the snapshot
type Q is Data:
  QEv{e: S.Ev}
  QSnap{}

# Decoders
# --------

def get_maybe.some(-A: Data, r: W.Dec<A>) -> W.Dec<Maybe<&2, A>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_strs(s: String) -> W.Dec<List<&2, String>>:
  W.get_list(~String, ~W.get_str, s)

def get_mstr.tag(n: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match n:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_maybe.some(String, W.get_str(s))
    case 2n+p:
      W.Bad{}

# a Maybe String
def get_mstr(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{n, s}:
      get_mstr.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(n: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match n:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_maybe.some(Nat, W.get_nat(s))
    case 2n+p:
      W.Bad{}

# a Maybe Nat
def get_mnat(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      get_mnat.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_dir(r: W.Dec<Nat>) -> W.Dec<S.Dir>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{S.Lower{}, s}
        case 1n:
          W.Got{S.Higher{}, s}
        case 2n+p:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_mode(r: W.Dec<Nat>) -> W.Dec<S.Mode>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{S.On{}, s}
        case 1n:
          W.Got{S.Off{}, s}
        case 2n+p:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_status(r: W.Dec<Nat>) -> W.Dec<S.Status>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{S.Keep{}, s}
        case 1n:
          W.Got{S.Discard{}, s}
        case 2n:
          W.Got{S.Crash{}, s}
        case 3n:
          W.Got{S.Checks{}, s}
        case 4n+p:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_cfg.max(a: String, b: String, c: String, d: String, e: S.Dir, f: List<&2, String>, g: List<&2, String>, h: List<&2, String>, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<S.Cfg>:
  match r:
    case W.Got{m, s}:
      W.Got{S.Cfg{a, b, c, d, e, f, g, h, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_cfg.off(a: String, b: String, c: String, d: String, e: S.Dir, f: List<&2, String>, g: List<&2, String>, r: W.Dec<List<&2, String>>) -> W.Dec<S.Cfg>:
  match r:
    case W.Got{h, s}:
      get_cfg.max(a, b, c, d, e, f, g, h, get_mnat(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_cfg.scope(a: String, b: String, c: String, d: String, e: S.Dir, f: List<&2, String>, r: W.Dec<List<&2, String>>) -> W.Dec<S.Cfg>:
  match r:
    case W.Got{g, s}:
      get_cfg.off(a, b, c, d, e, f, g, get_strs(s))
    case W.Bad{}:
      W.Bad{}

def get_cfg.sec(a: String, b: String, c: String, d: String, e: S.Dir, r: W.Dec<List<&2, String>>) -> W.Dec<S.Cfg>:
  match r:
    case W.Got{f, s}:
      get_cfg.scope(a, b, c, d, e, f, get_strs(s))
    case W.Bad{}:
      W.Bad{}

def get_cfg.dir(a: String, b: String, c: String, d: String, r: W.Dec<S.Dir>) -> W.Dec<S.Cfg>:
  match r:
    case W.Got{e, s}:
      get_cfg.sec(a, b, c, d, e, get_strs(s))
    case W.Bad{}:
      W.Bad{}

def get_cfg.unit(a: String, b: String, c: String, r: W.Dec<String>) -> W.Dec<S.Cfg>:
  match r:
    case W.Got{d, s}:
      get_cfg.dir(a, b, c, d, get_dir(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_cfg.metric(a: String, b: String, r: W.Dec<String>) -> W.Dec<S.Cfg>:
  match r:
    case W.Got{c, s}:
      get_cfg.unit(a, b, c, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_cfg.goal(a: String, r: W.Dec<String>) -> W.Dec<S.Cfg>:
  match r:
    case W.Got{b, s}:
      get_cfg.metric(a, b, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_cfg.name(r: W.Dec<String>) -> W.Dec<S.Cfg>:
  match r:
    case W.Got{a, s}:
      get_cfg.goal(a, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

# a configuration
def get_cfg(s: String) -> W.Dec<S.Cfg>:
  get_cfg.name(W.get_str(s))

def get_init.harness(c: S.Cfg, f: Bool, r: W.Dec<Bool>) -> W.Dec<Q>:
  match r:
    case W.Got{h, s}:
      W.Got{QEv{S.Init{c, f, h}}, s}
    case W.Bad{}:
      W.Bad{}

def get_init.fresh(c: S.Cfg, r: W.Dec<Bool>) -> W.Dec<Q>:
  match r:
    case W.Got{f, s}:
      get_init.harness(c, f, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_init(r: W.Dec<S.Cfg>) -> W.Dec<Q>:
  match r:
    case W.Got{c, s}:
      get_init.fresh(c, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_begin(r: W.Dec<Nat>) -> W.Dec<Q>:
  match r:
    case W.Got{n, s}:
      W.Got{QEv{S.Begin{n}}, s}
    case W.Bad{}:
      W.Bad{}

def get_line(r: W.Dec<String>) -> W.Dec<Q>:
  match r:
    case W.Got{t, s}:
      W.Got{QEv{S.Line{t}}, s}
    case W.Bad{}:
      W.Bad{}

def get_finish.timeout(neg: Bool, code: Nat, r: W.Dec<Bool>) -> W.Dec<Q>:
  match r:
    case W.Got{to, s}:
      W.Got{QEv{S.Finish{neg, code, to}}, s}
    case W.Bad{}:
      W.Bad{}

def get_finish.code(neg: Bool, r: W.Dec<Nat>) -> W.Dec<Q>:
  match r:
    case W.Got{code, s}:
      get_finish.timeout(neg, code, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_finish(r: W.Dec<Bool>) -> W.Dec<Q>:
  match r:
    case W.Got{neg, s}:
      get_finish.code(neg, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_log.devs(st: S.Status, desc: String, why: Maybe<&2, String>, r: W.Dec<Nat>) -> W.Dec<Q>:
  match r:
    case W.Got{n, s}:
      W.Got{QEv{S.Log{st, desc, why, n}}, s}
    case W.Bad{}:
      W.Bad{}

def get_log.why(st: S.Status, desc: String, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Q>:
  match r:
    case W.Got{why, s}:
      get_log.devs(st, desc, why, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_log.desc(st: S.Status, r: W.Dec<String>) -> W.Dec<Q>:
  match r:
    case W.Got{desc, s}:
      get_log.why(st, desc, get_mstr(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_log(r: W.Dec<S.Status>) -> W.Dec<Q>:
  match r:
    case W.Got{st, s}:
      get_log.desc(st, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_flag.reason(n: Nat, r: W.Dec<String>) -> W.Dec<Q>:
  match r:
    case W.Got{t, s}:
      W.Got{QEv{S.Flag{n, t}}, s}
    case W.Bad{}:
      W.Bad{}

def get_flag(r: W.Dec<Nat>) -> W.Dec<Q>:
  match r:
    case W.Got{n, s}:
      get_flag.reason(n, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_set_mode(r: W.Dec<S.Mode>) -> W.Dec<Q>:
  match r:
    case W.Got{m, s}:
      W.Got{QEv{S.SetMode{m}}, s}
    case W.Bad{}:
      W.Bad{}

def get_q.tag(n: Nat, s: String) -> W.Dec<Q>:
  match n:
    case 0n:
      get_init(get_cfg(s))
    case 1n:
      get_begin(W.get_nat(s))
    case 2n:
      get_line(W.get_str(s))
    case 3n:
      get_finish(W.get_bool(s))
    case 4n:
      get_log(get_status(W.get_nat(s)))
    case 5n:
      get_flag(W.get_nat(s))
    case 6n:
      get_set_mode(get_mode(W.get_nat(s)))
    case 7n:
      W.Got{QSnap{}, s}
    case 8n+p:
      W.Bad{}

def get_q.go(r: W.Dec<Nat>) -> W.Dec<Q>:
  match r:
    case W.Got{n, s}:
      get_q.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_q(s: String) -> W.Dec<Q>:
  get_q.go(W.get_nat(s))

# Encoders
# --------

def put_strs(xs: List<&2, String>, rest: String) -> String:
  W.put_list(~String, ~W.put_str, xs, rest)

def put_dir(d: S.Dir, rest: String) -> String:
  match d:
    case S.Lower{}:
      W.put_nat(0n, rest)
    case S.Higher{}:
      W.put_nat(1n, rest)

def put_mode(m: S.Mode, rest: String) -> String:
  match m:
    case S.On{}:
      W.put_nat(0n, rest)
    case S.Off{}:
      W.put_nat(1n, rest)

def put_status(t: S.Status, rest: String) -> String:
  match t:
    case S.Keep{}:
      W.put_nat(0n, rest)
    case S.Discard{}:
      W.put_nat(1n, rest)
    case S.Crash{}:
      W.put_nat(2n, rest)
    case S.Checks{}:
      W.put_nat(3n, rest)

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_mstatus(m: Maybe<&2, S.Status>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{t}:
      W.put_nat(1n, put_status(t, rest))

def put_cfg(c: S.Cfg, rest: String) -> String:
  match c:
    case S.Cfg{a, b, m, u, d, sec, scope, off, max}:
      W.put_str(a, W.put_str(b, W.put_str(m, W.put_str(u, put_dir(d, put_strs(sec, put_strs(scope, put_strs(off, put_mnat(max, rest)))))))))

def put_mcfg(m: Maybe<&2, S.Cfg>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{c}:
      W.put_nat(1n, put_cfg(c, rest))

def put_ds(ds: List<&2, Nat>, rest: String) -> String:
  W.put_list(~Nat, ~W.put_nat, ds, rest)

def put_dec(d: D.Dec, rest: String) -> String:
  match d:
    case D.Dec{neg, ds, scale}:
      W.put_bool(neg, put_ds(ds, W.put_nat(scale, rest)))

def put_mdec(m: Maybe<&2, D.Dec>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{d}:
      W.put_nat(1n, put_dec(d, rest))

def put_kv(kv: L.Kv, rest: String) -> String:
  match kv:
    case L.Kv{n, v}:
      W.put_str(n, put_dec(v, rest))

def put_kvs(kvs: List<&2, L.Kv>, rest: String) -> String:
  W.put_list(~L.Kv, ~put_kv, kvs, rest)

# a row, abandoned or not
def put_row(ab: Bool, r: S.Row, rest: String) -> String:
  match r:
    case S.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      W.put_nat(id, W.put_nat(sg, put_mstatus(st, W.put_bool(ab, W.put_bool(fn, put_mdec(m, put_kvs(ms, W.put_bool(ps, W.put_bool(fl, W.put_str(desc, rest))))))))))

# a row that ended: abandoned when it has no status
def put_ended(r: S.Row, rest: String) -> String:
  match r:
    case S.Row{id, sg, +st, m, ms, ps, fn, fl, desc}:
      put_row(Bool.not(S.has(st)), S.Row{id, sg, st, m, ms, ps, fn, fl, desc}, rest)

def put_rows.go(rs: List<&2, S.Row>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case r <> t:
      put_ended(r, put_rows.go(t, rest))

# the rows: those that ended, then the pending one
def put_rows(+m: String, +seg: Nat, +rs: List<&2, S.Row>, p: Maybe<&2, S.Pend>, rest: String) -> String:
  match p:
    case None{}:
      W.put_nat(S.rlen(rs), put_rows.go(rs, rest))
    case Some{q}:
      W.put_nat(1n+S.rlen(rs), put_rows.go(rs, put_row(False{}, S.row(m, seg, q, None{}, ""), rest)))

def pending(p: Maybe<&2, S.Pend>) -> Maybe<&2, Nat>:
  match p:
    case None{}:
      None{}
    case Some{S.Pend{id, kvs, fin}}:
      Some{id}

# a snapshot of state s
def put_snap(+s: S.St) -> String:
  match s:
    case S.St{+c, +seg, mode, +runs, +pend}:
      put_mcfg(c, W.put_nat(seg, put_mode(mode, put_rows(S.primary(c), seg, runs, pend, put_mnat(pending(pend), put_mdec(S.first(runs, seg), put_mdec(S.last(runs, seg), W.put_nat(S.logged(runs, seg), put_mnat(T.St.confidence(S.St{c, seg, mode, runs, pend}), "")))))))))

def put_eff(e: S.Eff, rest: String) -> String:
  match e:
    case S.Nothing{}:
      W.put_nat(0n, rest)
    case S.Commit{}:
      W.put_nat(1n, rest)
    case S.Reset{}:
      W.put_nat(2n, rest)

# The stepper
# -----------

# autoresearch's state, or a refused open
type St is Data:
  Live{s: S.St}
  Refused{}

# an event's answer: the state after it and the reply
def answer(r: S.Res, s: S.St) -> St & String:
  match r:
    case S.Took{s2, e, stop}:
      (Live{s2}, W.put_nat(0n, put_eff(e, W.put_bool(stop, ""))))
    case S.Refuse{t}:
      (Live{s}, W.put_nat(1n, W.put_str(t, "")))

# one request, whole
def serve(+s: S.St, q: Q) -> St & String:
  match q:
    case QEv{e}:
      answer(P.step(s, e), s)
    case QSnap{}:
      (Live{s}, put_snap(s))

def fail() -> String:
  W.err("autoresearch: malformed request")

def step.end(whole: Bool, +s: S.St, q: Q) -> St & String:
  match whole:
    case True{}:
      serve(s, q)
    case False{}:
      (Live{s}, fail())

def step.q(+s: S.St, d: W.Dec<Q>) -> St & String:
  match d:
    case W.Got{q, rest}:
      step.end(W.end(rest), s, q)
    case W.Bad{}:
      (Live{s}, fail())

# step: one request; the reply says what to do, or shows the state
def step(st: St, input: String) -> St & String:
  match st:
    case Live{s}:
      step.q(s, get_q(input))
    case Refused{}:
      (Refused{}, W.err("autoresearch: the open was refused"))

def open.end(whole: Bool) -> St & String:
  match whole:
    case True{}:
      (Live{S.St.empty()}, W.put_bool(True{}, ""))
    case False{}:
      (Refused{}, W.err("autoresearch: malformed open"))

# open: no experiment, no run (the host replays its log through step)
def open(input: String) -> St & String:
  open.end(W.end(input))
