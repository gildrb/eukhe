# ffi_tool_surface: the tool surface (bend/tools.bend sections 1 and 2:
# `build`, `step`, `dyn_call`) as an entry of the compiled Bend core
# (crates/eukhe-core/src/durable/tool_contract.rs `build` and
# durable/tool_surface/mod.rs `ToolSurface`, through
# crates/eukhe-bend/src/rules/tool_surface.rs). Rust interns names as Nats
# (a schema's parameter `i` is 0, its other parameters 1, 2, ... in
# declared order; a tool's name its own id) and keeps the registrations;
# the core decides. A request names its question (crates/eukhe-bend/WIRE.md
# is the grammar):
#
#   tag 0  build  a schema's parameters (List<Nat>), its declared version
#                 (Nat)
#                 -> the parameters the harness sends (List<Nat>), then
#                    the version (Nat): `build`
#   tag 1  join   the dynamic tools (List<Nat>, as the model keeps them),
#                 the tool that joins (Nat)
#                 -> the dynamic tools after it: `step` of `Join`
#   tag 2  quit   the dynamic tools, the tool that quits
#                 -> the dynamic tools after it: `step` of `Quit`
#   tag 3  reach  the dynamic tools, a tool
#                 -> T when a call through `dyn` reaches it: `dyn_call`
#
# Every input that is not exactly one request answers the error form
# "tool_surface: malformed request", never a default.
# laws/tool_surface.bend states this file's laws; PROOF.bend proves them.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./tools.bend as Tl

# A request of the entry
type Req is Data:
  QBuild{params: List<&2, Nat>, version: Nat}
  QJoin{dyn: List<&2, Nat>, t: Nat}
  QQuit{dyn: List<&2, Nat>, t: Nat}
  QReach{dyn: List<&2, Nat>, t: Nat}

# Requests
# --------

def get_ns(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

def get_build.version(ps: List<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{v, s}:
      W.Got{QBuild{ps, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_build(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ps, s}:
      get_build.version(ps, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_join.t(d: List<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      W.Got{QJoin{d, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_join(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      get_join.t(d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_quit.t(d: List<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      W.Got{QQuit{d, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_quit(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      get_quit.t(d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_reach.t(d: List<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      W.Got{QReach{d, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_reach(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      get_reach.t(d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_build(get_ns(s))
    case 1n:
      get_join(get_ns(s))
    case 2n:
      get_quit(get_ns(s))
    case 3n:
      get_reach(get_ns(s))
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

def put_ns(xs: List<&2, Nat>, rest: String) -> String:
  W.put_list(~Nat, ~W.put_nat, xs, rest)

def put_schema(x: Tl.Schema) -> String:
  match x:
    case Tl.Schema{ps, v}:
      put_ns(ps, W.put_nat(v, ""))

# the dynamic tools d as the model keeps them after the event e
def after(d: List<&2, Nat>, e: Tl.Ev) -> List<&2, Nat>:
  Tl.Sess.dyn(Tl.step(Tl.Sess{Nil{}, d, Nil{}}, e))

# the model's decision on a request, encoded
def answer(q: Req) -> String:
  match q:
    case QBuild{ps, v}:
      put_schema(Tl.build(Tl.Schema{ps, v}))
    case QJoin{d, t}:
      put_ns(after(d, Tl.Join{t}), "")
    case QQuit{d, t}:
      put_ns(after(d, Tl.Quit{t}), "")
    case QReach{d, t}:
      W.put_bool(Tl.dyn_call(Tl.Sess{Nil{}, d, Nil{}}, t), "")

def malformed() -> String:
  W.err("tool_surface: malformed request")

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
