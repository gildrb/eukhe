# ffi_runners: the runners of code (bend/runners.bend) as an entry of the
# compiled Bend core (crates/eukhe-core/src/durable/rlm/tool.rs, the
# registry test of crates/eukhe-core/src/durable/runner/tests.rs, through
# crates/eukhe-bend/src/rules/runners.rs). A request names its question
# (crates/eukhe-bend/WIRE.md is the grammar):
#
#   tag 0  within    a tool's caps, the auto set (List<Nat> each)
#                    -> T when the call runs unasked (`within`)
#   tag 1  cell      the caps, the auto set, who answered: 0 (no client)
#                    | 1 (no answer) | 2, Bool (the user said yes or no)
#                    -> whether it asked (Bool), then how the call ended:
#                       0, 0 (ran, unasked) | 0, 1 (ran, approved)
#                       | 1, 0 (refused, denied) | 1, 1 (refused,
#                       unanswered): `cell`
#   tag 2  registry  whether the session has chat memory (Bool)
#                    -> every tool it installs, in order: its name
#                       (String), its caps (List<Nat>), its gate (0 none,
#                       1 each step, 2 each call): `registry`
#   tag 3  main      whether main has chat memory (Bool)
#                    -> main's roster in the `main-worker` shape, each
#                       tool spelled as for tag 2: `main_roster`
#
# Every input that is not exactly one request answers the error form
# "runners: malformed request", never a default. laws/runners.bend
# (section entry) states this file's laws; PROOF.bend proves them. Pure:
# no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./runners.bend as Ru

# A request of the entry
type Req is Data:
  QWithin{caps: List<&2, Nat>, auto: List<&2, Nat>}
  QCell{caps: List<&2, Nat>, auto: List<&2, Nat>, asker: Ru.Asker}
  QRegistry{chat: Bool}
  QMain{chat: Bool}

# Requests
# --------

def get_ns(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

def get_says(r: W.Dec<Bool>) -> W.Dec<Ru.Asker>:
  match r:
    case W.Got{y, s}:
      W.Got{Ru.Says{y}, s}
    case W.Bad{}:
      W.Bad{}

def get_asker.tag(t: Nat, s: String) -> W.Dec<Ru.Asker>:
  match t:
    case 0n:
      W.Got{Ru.NoClient{}, s}
    case 1n:
      W.Got{Ru.Silent{}, s}
    case 2n:
      get_says(W.get_bool(s))
    case 3n+u:
      W.Bad{}

def get_asker(r: W.Dec<Nat>) -> W.Dec<Ru.Asker>:
  match r:
    case W.Got{t, s}:
      get_asker.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_within.auto(c: List<&2, Nat>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QWithin{c, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_within(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_within.auto(c, get_ns(s))
    case W.Bad{}:
      W.Bad{}

def get_cell.asker(c: List<&2, Nat>, a: List<&2, Nat>, r: W.Dec<Ru.Asker>) -> W.Dec<Req>:
  match r:
    case W.Got{k, s}:
      W.Got{QCell{c, a, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_cell.auto(c: List<&2, Nat>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      get_cell.asker(c, a, get_asker(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_cell(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_cell.auto(c, get_ns(s))
    case W.Bad{}:
      W.Bad{}

def get_registry(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{h, s}:
      W.Got{QRegistry{h}, s}
    case W.Bad{}:
      W.Bad{}

def get_main(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{h, s}:
      W.Got{QMain{h}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_within(get_ns(s))
    case 1n:
      get_cell(get_ns(s))
    case 2n:
      get_registry(W.get_bool(s))
    case 3n:
      get_main(W.get_bool(s))
    case 4n+u:
      W.Bad{}

def get_req.go(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Replies
# -------

def put_end(e: Ru.End, rest: String) -> String:
  match e:
    case Ru.Ran{h}:
      match h:
        case Ru.Auto{}:
          W.put_nat(0n, W.put_nat(0n, rest))
        case Ru.Approved{}:
          W.put_nat(0n, W.put_nat(1n, rest))
    case Ru.Refused{w}:
      match w:
        case Ru.Denied{}:
          W.put_nat(1n, W.put_nat(0n, rest))
        case Ru.Unanswered{}:
          W.put_nat(1n, W.put_nat(1n, rest))

def put_out(o: Ru.Out, rest: String) -> String:
  match o:
    case Ru.Out{a, e}:
      W.put_bool(a, put_end(e, rest))

def put_gate(g: Ru.Gate, rest: String) -> String:
  match g:
    case Ru.Ungated{}:
      W.put_nat(0n, rest)
    case Ru.EachStep{}:
      W.put_nat(1n, rest)
    case Ru.EachCall{}:
      W.put_nat(2n, rest)

def put_tool(t: Ru.Tool, rest: String) -> String:
  match t:
    case Ru.Tool{n, c, g}:
      W.put_str(n, W.put_list(~Nat, ~W.put_nat, c, put_gate(g, rest)))

# the model's decision on a request, encoded
def answer(q: Req) -> String:
  match q:
    case QWithin{c, +a}:
      W.put_bool(Ru.within(c, a), "")
    case QCell{c, +a, k}:
      put_out(Ru.cell(c, a, k), "")
    case QRegistry{h}:
      W.put_list(~Ru.Tool, ~put_tool, Ru.registry(h), "")
    case QMain{h}:
      W.put_list(~Ru.Tool, ~put_tool, Ru.main_roster(h), "")

def malformed() -> String:
  W.err("runners: malformed request")

def run.end(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      malformed()

def run(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      run.end(W.end(s), q)
    case W.Bad{}:
      malformed()

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  run(get_req(input))
