# ffi_model_name: the entry of the compiled Bend core for the name rules of
# the quirks rulebook (bend/model_name.bend; Rust: eukhe-bend
# rules/model_name.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   rule     0 contains, strs | 1 is, strs | 2 starts, strs |
#            3 then, a (String), b (String) |
#            4 number, after (strs), least (Nat), whole (Bool) |
#            5 segment_starts, strs                 (strs = List<String>)
#   request  0, sets (List<List<rule>>), groups (List<List<String>>)
#              reply List<Bool>: for each group in order, for each set in
#              order, whether one rule of the set holds for one name of
#              the group (groups x sets verdicts)
#            1, texts (List<String>)
#              reply List<String>: each text dashed (R8)
#
# A request tag past 1, a rule tag past 5, malformed input, or input left
# after the request answers `E model_name: malformed request`, never a
# default. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./model_name.bend as M

# A request of the entry
type Req is Data:
  QHolds{sets: List<&2, List<&2, M.Rule>>, groups: List<&2, List<&2, String>>}
  QDash{texts: List<&2, String>}

def get_strs(s: String) -> W.Dec<List<&2, String>>:
  W.get_list(~String, ~W.get_str, s)

# Rules
# -----

def get_rule.contains(r: W.Dec<List<&2, String>>) -> W.Dec<M.Rule>:
  match r:
    case W.Got{ps, s}:
      W.Got{M.RContains{ps}, s}
    case W.Bad{}:
      W.Bad{}

def get_rule.is(r: W.Dec<List<&2, String>>) -> W.Dec<M.Rule>:
  match r:
    case W.Got{ps, s}:
      W.Got{M.RIs{ps}, s}
    case W.Bad{}:
      W.Bad{}

def get_rule.starts(r: W.Dec<List<&2, String>>) -> W.Dec<M.Rule>:
  match r:
    case W.Got{ps, s}:
      W.Got{M.RStarts{ps}, s}
    case W.Bad{}:
      W.Bad{}

def get_rule.segment(r: W.Dec<List<&2, String>>) -> W.Dec<M.Rule>:
  match r:
    case W.Got{ps, s}:
      W.Got{M.RSegment{ps}, s}
    case W.Bad{}:
      W.Bad{}

def get_rule.then_b(a: String, r: W.Dec<String>) -> W.Dec<M.Rule>:
  match r:
    case W.Got{b, s}:
      W.Got{M.RThen{a, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_rule.then_a(r: W.Dec<String>) -> W.Dec<M.Rule>:
  match r:
    case W.Got{a, s}:
      get_rule.then_b(a, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_rule.whole(ps: List<&2, String>, n: Nat, r: W.Dec<Bool>) -> W.Dec<M.Rule>:
  match r:
    case W.Got{w, s}:
      W.Got{M.RNumber{ps, n, w}, s}
    case W.Bad{}:
      W.Bad{}

def get_rule.least(ps: List<&2, String>, r: W.Dec<Nat>) -> W.Dec<M.Rule>:
  match r:
    case W.Got{n, s}:
      get_rule.whole(ps, n, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_rule.after(r: W.Dec<List<&2, String>>) -> W.Dec<M.Rule>:
  match r:
    case W.Got{ps, s}:
      get_rule.least(ps, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_rule.tag(r: W.Dec<Nat>) -> W.Dec<M.Rule>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_rule.contains(get_strs(s))
        case 1n:
          get_rule.is(get_strs(s))
        case 2n:
          get_rule.starts(get_strs(s))
        case 3n:
          get_rule.then_a(W.get_str(s))
        case 4n:
          get_rule.after(get_strs(s))
        case 5n:
          get_rule.segment(get_strs(s))
        case 6n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the rule at the start of s
def get_rule(s: String) -> W.Dec<M.Rule>:
  get_rule.tag(W.get_nat(s))

def get_set(s: String) -> W.Dec<List<&2, M.Rule>>:
  W.get_list(~M.Rule, ~get_rule, s)

# Requests
# --------

def get_req.groups(sets: List<&2, List<&2, M.Rule>>, r: W.Dec<List<&2, List<&2, String>>>) -> W.Dec<Req>:
  match r:
    case W.Got{gs, s}:
      W.Got{QHolds{sets, gs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.sets(r: W.Dec<List<&2, List<&2, M.Rule>>>) -> W.Dec<Req>:
  match r:
    case W.Got{sets, s}:
      get_req.groups(sets, W.get_list(~List<&2, String>, ~get_strs, s))
    case W.Bad{}:
      W.Bad{}

def get_req.dash(r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ts, s}:
      W.Got{QDash{ts}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_req.sets(W.get_list(~List<&2, M.Rule>, ~get_set, s))
        case 1n:
          get_req.dash(get_strs(s))
        case 2n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# The entry
# ---------

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QHolds{sets, gs}:
      W.put_list(~Bool, ~W.put_bool, M.holds(sets, gs), "")
    case QDash{ts}:
      W.put_list(~String, ~W.put_str, M.dashes(ts), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("model_name: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("model_name: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
