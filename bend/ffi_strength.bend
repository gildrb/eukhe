# ffi_strength: the compiled Bend core's entry for the strength of the
# checks (bend/strength.bend). Rust `eukhe_bend::rules::strength` calls it
# through `eukhe_bend::call` from eukhe-core durable/acceptance (the
# verifier's step after verify ended a claim, the label, the strength of
# each check) and eukhe-cli print_runtime (the exit code of a headless
# run).
#
# Request (crates/eukhe-bend/WIRE.md): a tag, then its fields.
#   0 settle:   verify's label, the state now (Nat), the gauges
#   1 label:    verify's label, the state now, the gauges
#   2 exit:     the run's own exit code (Nat), the state now, the slots
#               (bend/ffi_verify.bend's spelling), the gauges
#   3 record:   who, the index (Nat), the mark, the gauges
#   4 strength: the state now, one gauge
# Verify's label: 0 verified, 1 failed, 2 unverified, 3 passed. Who: 0 the
# owner, 1 the worker, 2 the verifier. A gauge: the bar (0 exempt, 1
# waived, 2 needs then the percent, a Nat), then the mark (0 unmeasured,
# 1 measured then the breaks caught, run and planned and the state, four
# Nats). The gauges: List<Gauge>.
# Reply: settle: 0 measure then the index, or 1 end then the label;
# label: the label (0 verified, 1 failed, 2 unverified, 3 passed, 4 not
# certified); exit: the code (Nat); record: admitted (Bool), then the
# gauges; strength: 0 strong, 1 weak, 2 unshown, 3 free.
# Any other input (an unknown tag, a malformed field, input left after the
# request) answers the error form "strength: malformed request", never a
# default. laws/strength.bend (section entry) states this file's laws.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./verify.bend as V
import ./ffi_verify.bend as FV
import ./strength.bend as St

# A request of the entry
type Req is Data:
  QSettle{l: V.Label, now: Nat, gs: List<&2, St.Gauge>}
  QLabel{l: V.Label, now: Nat, gs: List<&2, St.Gauge>}
  QExit{base: Nat, now: Nat, slots: List<&2, V.Slot>, gs: List<&2, St.Gauge>}
  QRecord{who: V.Actor, i: Nat, m: St.Mark, gs: List<&2, St.Gauge>}
  QStrength{now: Nat, g: St.Gauge}

# Decoders
# --------

def get_vlabel(r: W.Dec<Nat>) -> W.Dec<V.Label>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{V.Verified{}, s}
        case 1n:
          W.Got{V.Failed{}, s}
        case 2n:
          W.Got{V.Unverified{}, s}
        case 3n:
          W.Got{V.Passed{}, s}
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_bar.pct(r: W.Dec<Nat>) -> W.Dec<St.Bar>:
  match r:
    case W.Got{pct, s}:
      W.Got{St.Needs{pct}, s}
    case W.Bad{}:
      W.Bad{}

def get_bar(r: W.Dec<Nat>) -> W.Dec<St.Bar>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{St.Exempt{}, s}
        case 1n:
          W.Got{St.Waived{}, s}
        case 2n:
          get_bar.pct(W.get_nat(s))
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_mark.at(c: Nat, n: Nat, p: Nat, r: W.Dec<Nat>) -> W.Dec<St.Mark>:
  match r:
    case W.Got{at, s}:
      W.Got{St.Measured{c, n, p, at}, s}
    case W.Bad{}:
      W.Bad{}

def get_mark.planned(c: Nat, n: Nat, r: W.Dec<Nat>) -> W.Dec<St.Mark>:
  match r:
    case W.Got{p, s}:
      get_mark.at(c, n, p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_mark.ran(c: Nat, r: W.Dec<Nat>) -> W.Dec<St.Mark>:
  match r:
    case W.Got{n, s}:
      get_mark.planned(c, n, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_mark.caught(r: W.Dec<Nat>) -> W.Dec<St.Mark>:
  match r:
    case W.Got{c, s}:
      get_mark.ran(c, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_mark(r: W.Dec<Nat>) -> W.Dec<St.Mark>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{St.Unmeasured{}, s}
        case 1n:
          get_mark.caught(W.get_nat(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_gauge.mark(b: St.Bar, r: W.Dec<St.Mark>) -> W.Dec<St.Gauge>:
  match r:
    case W.Got{m, s}:
      W.Got{St.Gauge{b, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_gauge.bar(r: W.Dec<St.Bar>) -> W.Dec<St.Gauge>:
  match r:
    case W.Got{b, s}:
      get_gauge.mark(b, get_mark(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# the gauge at the start of s
def get_gauge(s: String) -> W.Dec<St.Gauge>:
  get_gauge.bar(get_bar(W.get_nat(s)))

# the gauges at the start of s
def get_gauges(s: String) -> W.Dec<List<&2, St.Gauge>>:
  W.get_list(~St.Gauge, ~get_gauge, s)

def get_req.settle_gs(l: V.Label, now: Nat, r: W.Dec<List<&2, St.Gauge>>) -> W.Dec<Req>:
  match r:
    case W.Got{gs, s}:
      W.Got{QSettle{l, now, gs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.settle_now(l: V.Label, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_req.settle_gs(l, now, get_gauges(s))
    case W.Bad{}:
      W.Bad{}

def get_req.settle(r: W.Dec<V.Label>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      get_req.settle_now(l, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.label_gs(l: V.Label, now: Nat, r: W.Dec<List<&2, St.Gauge>>) -> W.Dec<Req>:
  match r:
    case W.Got{gs, s}:
      W.Got{QLabel{l, now, gs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.label_now(l: V.Label, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_req.label_gs(l, now, get_gauges(s))
    case W.Bad{}:
      W.Bad{}

def get_req.label(r: W.Dec<V.Label>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      get_req.label_now(l, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.exit_gs(base: Nat, now: Nat, slots: List<&2, V.Slot>, r: W.Dec<List<&2, St.Gauge>>) -> W.Dec<Req>:
  match r:
    case W.Got{gs, s}:
      W.Got{QExit{base, now, slots, gs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.exit_slots(base: Nat, now: Nat, r: W.Dec<List<&2, V.Slot>>) -> W.Dec<Req>:
  match r:
    case W.Got{slots, s}:
      get_req.exit_gs(base, now, slots, get_gauges(s))
    case W.Bad{}:
      W.Bad{}

def get_req.exit_now(base: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_req.exit_slots(base, now, FV.get_slots(s))
    case W.Bad{}:
      W.Bad{}

def get_req.exit(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{base, s}:
      get_req.exit_now(base, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.record_gs(who: V.Actor, i: Nat, m: St.Mark, r: W.Dec<List<&2, St.Gauge>>) -> W.Dec<Req>:
  match r:
    case W.Got{gs, s}:
      W.Got{QRecord{who, i, m, gs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.record_mark(who: V.Actor, i: Nat, r: W.Dec<St.Mark>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      get_req.record_gs(who, i, m, get_gauges(s))
    case W.Bad{}:
      W.Bad{}

def get_req.record_i(who: V.Actor, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{i, s}:
      get_req.record_mark(who, i, get_mark(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.record(r: W.Dec<V.Actor>) -> W.Dec<Req>:
  match r:
    case W.Got{who, s}:
      get_req.record_i(who, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.strength_g(now: Nat, r: W.Dec<St.Gauge>) -> W.Dec<Req>:
  match r:
    case W.Got{g, s}:
      W.Got{QStrength{now, g}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.strength(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_req.strength_g(now, get_gauge(s))
    case W.Bad{}:
      W.Bad{}

# the request whose tag r read
def get_req(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_req.settle(get_vlabel(W.get_nat(s)))
        case 1n:
          get_req.label(get_vlabel(W.get_nat(s)))
        case 2n:
          get_req.exit(W.get_nat(s))
        case 3n:
          get_req.record(FV.get_actor(W.get_nat(s)))
        case 4n:
          get_req.strength(W.get_nat(s))
        case 5n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# Encoders
# --------

def put_bar(b: St.Bar, rest: String) -> String:
  match b:
    case St.Exempt{}:
      W.put_nat(0n, rest)
    case St.Waived{}:
      W.put_nat(1n, rest)
    case St.Needs{pct}:
      W.put_nat(2n, W.put_nat(pct, rest))

def put_mark(m: St.Mark, rest: String) -> String:
  match m:
    case St.Unmeasured{}:
      W.put_nat(0n, rest)
    case St.Measured{c, n, p, at}:
      W.put_nat(1n, W.put_nat(c, W.put_nat(n, W.put_nat(p, W.put_nat(at, rest)))))

def put_gauge(g: St.Gauge, rest: String) -> String:
  match g:
    case St.Gauge{b, m}:
      put_bar(b, put_mark(m, rest))

def put_label(l: St.Label, rest: String) -> String:
  match l:
    case St.Verified{}:
      W.put_nat(0n, rest)
    case St.Failed{}:
      W.put_nat(1n, rest)
    case St.Unverified{}:
      W.put_nat(2n, rest)
    case St.Passed{}:
      W.put_nat(3n, rest)
    case St.Uncertified{}:
      W.put_nat(4n, rest)

def put_step(x: St.Step, rest: String) -> String:
  match x:
    case St.Measure{i}:
      W.put_nat(0n, W.put_nat(i, rest))
    case St.End{l}:
      W.put_nat(1n, put_label(l, rest))

def put_strength(x: St.Strength, rest: String) -> String:
  match x:
    case St.Strong{}:
      W.put_nat(0n, rest)
    case St.Weak{}:
      W.put_nat(1n, rest)
    case St.Unshown{}:
      W.put_nat(2n, rest)
    case St.Free{}:
      W.put_nat(3n, rest)

def put_recorded(r: Bool & List<&2, St.Gauge>) -> String:
  (ok, gs) = r
  W.put_bool(ok, W.put_list(~St.Gauge, ~put_gauge, gs, ""))

# the reply of a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case QSettle{l, now, gs}:
      put_step(St.settle(l, now, gs), "")
    case QLabel{l, now, gs}:
      put_label(St.label(l, now, gs), "")
    case QExit{base, now, slots, gs}:
      W.put_nat(St.exit(base, now, slots, gs), "")
    case QRecord{who, i, m, gs}:
      put_recorded(St.record(who, i, m, gs))
    case QStrength{now, g}:
      put_strength(St.strength(now, g), "")

# The entry
# ---------

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("strength: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("strength: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(W.get_nat(input)))
