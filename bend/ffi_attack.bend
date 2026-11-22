# ffi_attack: the compiled Bend core's entry for the blind attackers on
# the checks (bend/attack.bend). Rust `eukhe_bend::rules::attack` calls it
# through `eukhe_bend::call` from eukhe-core durable/acceptance/attack (the
# outcome of each attack, the label) and eukhe-cli print_runtime (the exit
# code of a headless run).
#
# Request (crates/eukhe-bend/WIRE.md): a tag, then its fields.
#   0 outcome: whether the attack ran, whether its code passed every
#              gauged check, whether the witness's output differs from
#              the required one (three Bools), the judge's verdict (0 none,
#              or 1 then a Bool: it agrees)
#   1 label:   verify's label, the state now (Nat), the gauges
#              (bend/ffi_strength.bend's spelling), the outcomes
#   2 exit:    the run's own exit code (Nat), the state now, the slots
#              (bend/ffi_verify.bend's spelling), the gauges, the outcomes
# Verify's label: 0 verified, 1 failed, 2 unverified, 3 passed. An
# outcome: 0 survived, 1 clean, 2 unrun. The outcomes: List<Outcome>.
# Reply: outcome: the outcome (0 survived, 1 clean, 2 unrun); label: the
# label (0 verified, 1 failed, 2 unverified, 3 passed, 4 not certified);
# exit: the code (Nat).
# Any other input (an unknown tag, a malformed field, input left after the
# request) answers the error form "attack: malformed request", never a
# default. laws/attack.bend (section entry) states this file's laws.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./verify.bend as V
import ./ffi_verify.bend as FV
import ./strength.bend as St
import ./ffi_strength.bend as FS
import ./attack.bend as At

# A request of the entry
type Req is Data:
  QOutcome{r: At.Run}
  QLabel{l: V.Label, now: Nat, gs: List<&2, St.Gauge>, os: List<&2, At.Outcome>}
  QExit{base: Nat, now: Nat, slots: List<&2, V.Slot>, gs: List<&2, St.Gauge>, os: List<&2, At.Outcome>}

# Decoders
# --------

def get_outcome.tag(r: W.Dec<Nat>) -> W.Dec<At.Outcome>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{At.Survived{}, s}
        case 1n:
          W.Got{At.Clean{}, s}
        case 2n:
          W.Got{At.Unrun{}, s}
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the outcome at the start of s
def get_outcome(s: String) -> W.Dec<At.Outcome>:
  get_outcome.tag(W.get_nat(s))

# the outcomes at the start of s
def get_outcomes(s: String) -> W.Dec<List<&2, At.Outcome>>:
  W.get_list(~At.Outcome, ~get_outcome, s)

def get_agrees.yes(r: W.Dec<Bool>) -> W.Dec<Maybe<&2, Bool>>:
  match r:
    case W.Got{yes, s}:
      W.Got{Some{yes}, s}
    case W.Bad{}:
      W.Bad{}

def get_agrees(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Bool>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_agrees.yes(W.get_bool(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_req.outcome_agrees(ran: Bool, passes: Bool, differs: Bool, r: W.Dec<Maybe<&2, Bool>>) -> W.Dec<Req>:
  match r:
    case W.Got{agrees, s}:
      W.Got{QOutcome{At.Run{ran, passes, differs, agrees}}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.outcome_differs(ran: Bool, passes: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{differs, s}:
      get_req.outcome_agrees(ran, passes, differs, get_agrees(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.outcome_passes(ran: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{passes, s}:
      get_req.outcome_differs(ran, passes, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.outcome(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{ran, s}:
      get_req.outcome_passes(ran, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.label_os(l: V.Label, now: Nat, gs: List<&2, St.Gauge>, r: W.Dec<List<&2, At.Outcome>>) -> W.Dec<Req>:
  match r:
    case W.Got{os, s}:
      W.Got{QLabel{l, now, gs, os}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.label_gs(l: V.Label, now: Nat, r: W.Dec<List<&2, St.Gauge>>) -> W.Dec<Req>:
  match r:
    case W.Got{gs, s}:
      get_req.label_os(l, now, gs, get_outcomes(s))
    case W.Bad{}:
      W.Bad{}

def get_req.label_now(l: V.Label, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_req.label_gs(l, now, FS.get_gauges(s))
    case W.Bad{}:
      W.Bad{}

def get_req.label(r: W.Dec<V.Label>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      get_req.label_now(l, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.exit_os(base: Nat, now: Nat, slots: List<&2, V.Slot>, gs: List<&2, St.Gauge>, r: W.Dec<List<&2, At.Outcome>>) -> W.Dec<Req>:
  match r:
    case W.Got{os, s}:
      W.Got{QExit{base, now, slots, gs, os}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.exit_gs(base: Nat, now: Nat, slots: List<&2, V.Slot>, r: W.Dec<List<&2, St.Gauge>>) -> W.Dec<Req>:
  match r:
    case W.Got{gs, s}:
      get_req.exit_os(base, now, slots, gs, get_outcomes(s))
    case W.Bad{}:
      W.Bad{}

def get_req.exit_slots(base: Nat, now: Nat, r: W.Dec<List<&2, V.Slot>>) -> W.Dec<Req>:
  match r:
    case W.Got{slots, s}:
      get_req.exit_gs(base, now, slots, FS.get_gauges(s))
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

# the request whose tag r read
def get_req(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_req.outcome(W.get_bool(s))
        case 1n:
          get_req.label(FS.get_vlabel(W.get_nat(s)))
        case 2n:
          get_req.exit(W.get_nat(s))
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# Encoders
# --------

def put_outcome(o: At.Outcome, rest: String) -> String:
  match o:
    case At.Survived{}:
      W.put_nat(0n, rest)
    case At.Clean{}:
      W.put_nat(1n, rest)
    case At.Unrun{}:
      W.put_nat(2n, rest)

# the reply of a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case QOutcome{r}:
      put_outcome(At.outcome(r), "")
    case QLabel{l, now, gs, os}:
      FS.put_label(At.label(l, now, gs, os), "")
    case QExit{base, now, slots, gs, os}:
      W.put_nat(At.exit(base, now, slots, gs, os), "")

# The entry
# ---------

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("attack: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("attack: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(W.get_nat(input)))
