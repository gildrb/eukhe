# eukhe: the laws of area tool_surface

import Base
import ../bend/ffi_tool_surface.bend as FTs
import ../bend/tools.bend as Tl
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- tool_surface ----

# LAWS (S7, compiled core): the tool surface runs as the compiled model
# (bend/ffi_tool_surface.bend over bend/tools.bend sections 1 and 2; Rust:
# crates/eukhe-bend/src/rules/tool_surface.rs, called by
# crates/eukhe-core/src/durable/tool_contract.rs `build` for every tool
# schema the harness sends and by durable/tool_surface/mod.rs
# `ToolSurface` as tools join, quit and are called through `dyn`). Each
# law is an open claim about FTs.ffi, the function the core runs, stated
# with spec spellers built only from the wire primitives of
# bend/wire.bend.
#
# R1: a request Rust writes reads back whole and the entry answers it with
#     the model's decision: the schema the harness sends (`Tl.build`), the
#     dynamic tools after a tool joins or quits (`Tl.step`), whether a
#     call through `dyn` reaches a tool (`Tl.dyn_call`).
# R2: every other input answers exactly the error form "tool_surface:
#     malformed request".
# Every input is free: any parameters, any version, any dynamic tools,
# any tool, any text.

# Spec spellers
# -------------

def spell_ns(xs: List<&2, Nat>, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)

# the request q as Rust writes it, then rest
def spell_req(q: FTs.Req, rest: String) -> String:
  match q:
    case FTs.QBuild{ps, v}:
      Wr.put_nat(0n, spell_ns(ps, Wr.put_nat(v, rest)))
    case FTs.QJoin{d, t}:
      Wr.put_nat(1n, spell_ns(d, Wr.put_nat(t, rest)))
    case FTs.QQuit{d, t}:
      Wr.put_nat(2n, spell_ns(d, Wr.put_nat(t, rest)))
    case FTs.QReach{d, t}:
      Wr.put_nat(3n, spell_ns(d, Wr.put_nat(t, rest)))

# a list of Nats fits the wire: its length and each item
def ns_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# every number of a request fits the wire
def req_fits(q: FTs.Req) -> Bool:
  match q:
    case FTs.QBuild{ps, v}:
      Bool.and(ns_fit(ps), LawsBase.wire_fits(v))
    case FTs.QJoin{d, t}:
      Bool.and(ns_fit(d), LawsBase.wire_fits(t))
    case FTs.QQuit{d, t}:
      Bool.and(ns_fit(d), LawsBase.wire_fits(t))
    case FTs.QReach{d, t}:
      Bool.and(ns_fit(d), LawsBase.wire_fits(t))

# a schema: its parameters, then its version
def spell_schema(x: Tl.Schema) -> String:
  match x:
    case Tl.Schema{ps, v}:
      spell_ns(ps, Wr.put_nat(v, ""))

# a session with the dynamic tools d (no roster, nothing sent)
def sess(d: List<&2, Nat>) -> Tl.Sess:
  Tl.Sess{Nil{}, d, Nil{}}

# the model's decision on q, spelled
def spell_answer(q: FTs.Req) -> String:
  match q:
    case FTs.QBuild{ps, v}:
      spell_schema(Tl.build(Tl.Schema{ps, v}))
    case FTs.QJoin{d, t}:
      spell_ns(Tl.Sess.dyn(Tl.step(sess(d), Tl.Join{t})), "")
    case FTs.QQuit{d, t}:
      spell_ns(Tl.Sess.dyn(Tl.step(sess(d), Tl.Quit{t})), "")
    case FTs.QReach{d, t}:
      Wr.put_bool(Tl.dyn_call(sess(d), t), "")

# the error form of every input that is not exactly one request
def malformed() -> String:
  SCon{'E', SCon{' ', "tool_surface: malformed request"}}

# Reader: the requests, read with the wire primitives
# ---------------------------------------------------

def read_ns(s: String) -> Wr.Dec<List<&2, Nat>>:
  Wr.get_list(~Nat, ~Wr.get_nat, s)

def read_build.version(ps: List<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FTs.Req>:
  match r:
    case Wr.Got{v, s}:
      Wr.Got{FTs.QBuild{ps, v}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_build(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FTs.Req>:
  match r:
    case Wr.Got{ps, s}:
      read_build.version(ps, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_join.t(d: List<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FTs.Req>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{FTs.QJoin{d, t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_join(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FTs.Req>:
  match r:
    case Wr.Got{d, s}:
      read_join.t(d, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_quit.t(d: List<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FTs.Req>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{FTs.QQuit{d, t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_quit(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FTs.Req>:
  match r:
    case Wr.Got{d, s}:
      read_quit.t(d, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_reach.t(d: List<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FTs.Req>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{FTs.QReach{d, t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_reach(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FTs.Req>:
  match r:
    case Wr.Got{d, s}:
      read_reach.t(d, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_req.tag(t: Nat, s: String) -> Wr.Dec<FTs.Req>:
  match t:
    case 0n:
      read_build(read_ns(s))
    case 1n:
      read_join(read_ns(s))
    case 2n:
      read_quit(read_ns(s))
    case 3n:
      read_reach(read_ns(s))
    case 4n+u:
      Wr.Bad{}

def read_req.go(r: Wr.Dec<Nat>) -> Wr.Dec<FTs.Req>:
  match r:
    case Wr.Got{t, s}:
      read_req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with, and what follows it
def read_req(s: String) -> Wr.Dec<FTs.Req>:
  read_req.go(Wr.get_nat(s))

def spec.end(whole: Bool, q: FTs.Req) -> String:
  match whole:
    case True{}:
      spell_answer(q)
    case False{}:
      malformed()

def spec.run(r: Wr.Dec<FTs.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      spec.end(Wr.end(s), q)
    case Wr.Bad{}:
      malformed()

# the reply to s: the model's decision on the request s is exactly, else
# the error form
def spec(s: String) -> String:
  spec.run(read_req(s))

# Laws
# ----

# LAW tool_surface_ffi_exact: on every input the entry answers the model's decision on the request the input is exactly (the schema the harness sends; the dynamic tools after a join or a quit; whether `dyn` reaches a tool), and exactly the error form "tool_surface: malformed request" on any other input
# EXCLUDES: a schema sent without the intent, with a parameter lost or
#   moved, or at version 0; a tool that joined and is not reached, or quit
#   and is still reached; a default for malformed input, input left over
#   ignored, another error text
law tool_surface_ffi_exact:
  for +s: String
  {FTs.ffi(s) == spec(s) : String}

# LAW tool_surface_ffi_answers: every request Rust writes (every number within the wire) gets the model's decision
# EXCLUDES: a request Rust writes refused or misread
law tool_surface_ffi_answers:
  for +q: FTs.Req
  for fits: {req_fits(q) == True{} : Bool}
  {FTs.ffi(spell_req(q, "")) == spell_answer(q) : String}

# LAW tool_surface_ffi_left_over: a request Rust writes followed by more input gets exactly the error form
# EXCLUDES: a second request or trailing bytes read past or ignored
law tool_surface_ffi_left_over:
  for +q: FTs.Req
  for +more: String
  for fits: {req_fits(q) == True{} : Bool}
  for some: {String.is_empty(more) == False{} : Bool}
  {FTs.ffi(spell_req(q, more)) == malformed() : String}

# LAW tool_surface_ffi_example: anchor: the strings Rust sends: a schema of two parameters and no version gets the intent first and version 1; one that holds the intent at version 5 is kept; tool 4 joins; tool 4 quits (every copy); `dyn` reaches a joined tool and not an absent one; tag 4 is refused
# EXCLUDES: another spelling of a request or a reply
law tool_surface_ffi_example:
  {FTs.ffi("0,2,2,3,0,") == "3,0,2,3,1," : String} &
  {FTs.ffi("0,2,0,2,5,") == "2,0,2,5," : String} &
  {FTs.ffi("1,1,4,4,") == "2,4,4," : String} &
  {FTs.ffi("2,3,4,2,4,4,") == "1,2," : String} &
  {FTs.ffi("3,1,4,4,") == "T" : String} &
  {FTs.ffi("3,0,4,") == "F" : String} &
  {FTs.ffi("4,") == malformed() : String}
