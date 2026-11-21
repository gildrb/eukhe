# ffi_runners: the runners of code (bend/runners.bend) as an entry of the
# compiled Bend core (crates/eukhe-core/src/durable/registry.rs, the
# registry test of crates/eukhe-core/src/durable/runner/tests.rs, through
# crates/eukhe-bend/src/rules/runners.rs). A request names its question
# (crates/eukhe-bend/WIRE.md is the grammar):
#
#   tag 2  registry  nothing more
#                    -> every tool a session installs, in order: its name
#                       (String), its caps (List<Nat>), its gate (0 none,
#                       1 each step, 2 each call): `registry`
#   tag 3  main      whether main has chat memory (Bool)
#                    -> main's roster in the `main-worker` shape, each
#                       tool spelled as for tag 2: `main_roster`
#
# Tags 0 and 1 name no question (they were `within` and `cell`); the tags
# keep their numbers.
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
  QRegistry{}
  QMain{chat: Bool}

# Requests
# --------

def get_main(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{h, s}:
      W.Got{QMain{h}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      W.Bad{}
    case 1n:
      W.Bad{}
    case 2n:
      W.Got{QRegistry{}, s}
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

def put_gate(g: Ru.Gate, rest: String) -> String:
  match g:
    case Ru.Ungated{}:
      W.put_nat(0n, rest)
    case Ru.EachStep{}:
      W.put_nat(1n, rest)
    case Ru.EachCall{}:
      W.put_nat(2n, rest)

def put_tool(t: Ru.ToolReg, rest: String) -> String:
  match t:
    case Ru.ToolReg{n, c, g}:
      W.put_str(n, W.put_list(~Nat, ~W.put_nat, c, put_gate(g, rest)))

# the model's decision on a request, encoded
def answer(q: Req) -> String:
  match q:
    case QRegistry{}:
      W.put_list(~Ru.ToolReg, ~put_tool, Ru.registry(), "")
    case QMain{h}:
      W.put_list(~Ru.ToolReg, ~put_tool, Ru.main_roster(h), "")

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
