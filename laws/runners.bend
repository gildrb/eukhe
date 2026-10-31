# eukhe: the laws of area runners

import Base
import ../bend/ffi_runners.bend as FRu
import ../bend/runners.bend as Ru
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- runners ----

# LAWS (G4): every runner of code goes through the gate. Each law is an
# open claim about the model in bend/runners.bend; PROOF.bend proves them
# (as Runners.<law>) with the lemmas of proof/runners/.

# (G4) Every runner of code goes through the gate
# -----------------------------------------------
# the model in bend/runners.bend. `Rn.registry` is the
# registry a session installs (crates/eukhe-core/src/durable/registry.rs);
# it and the gate run as the compiled core (section runners entry below),
# and the registry test in crates/eukhe-core/src/durable/runner/tests.rs
# compares the real registry with the core's.

# LAW gate_covers_every_runner: every tool of a session's registry (with or without chat memory)
# that runs code that may run a program is gated
law gate_covers_every_runner:
  for +chat: Bool
  for +i: Nat
  for +t: Ru.Tool
  for at: {List.get(&2, Ru.Tool, Ru.registry(chat), i) == Some{t} : Maybe<&2, Ru.Tool>}
  for runs: {Ru.runs(t) == True{} : Bool}
  {Ru.gated(t) == True{} : Bool}

# LAW ipython_gated_each_call: the `ipython` tool runs code that may run a program, and the gate
# covers each of its calls
law ipython_gated_each_call:
  for +chat: Bool
  {Ru.find(Ru.registry(chat), "ipython") == Some{Ru.Tool{"ipython", [Ru.exec()], Ru.EachCall{}}} : Maybe<&2, Ru.Tool>}

# LAW cell_runs_only_within_or_approved: a gated call runs only when its caps are within the auto set or the
# user approves it
law cell_runs_only_within_or_approved:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Ru.Asker
  for ran: {Ru.ran(Ru.cell(caps, auto, a)) == True{} : Bool}
  {Bool.or(Ru.within(caps, auto), Ru.Asker.yes(a)) == True{} : Bool}

# LAW cell_within_runs_unasked: a call whose caps are within the auto set runs, unasked
law cell_within_runs_unasked:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for a: Ru.Asker
  for free: {Ru.within(caps, auto) == True{} : Bool}
  {Ru.cell(caps, auto, a) == Ru.Out{False{}, Ru.Ran{Ru.Auto{}}} : Ru.Out}

# LAW cell_approved_runs: a call outside the auto set that the user approves runs, asked
law cell_approved_runs:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for held: {Ru.within(caps, auto) == False{} : Bool}
  {Ru.cell(caps, auto, Ru.Says{True{}}) == Ru.Out{True{}, Ru.Ran{Ru.Approved{}}} : Ru.Out}

# LAW cell_no_yes_stops: a call outside the auto set without the user's approval (a denial,
# no answer, no client) does not run
law cell_no_yes_stops:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Ru.Asker
  for held: {Ru.within(caps, auto) == False{} : Bool}
  for no: {Ru.Asker.yes(a) == False{} : Bool}
  {Ru.ran(Ru.cell(caps, auto, a)) == False{} : Bool}

# LAW cell_exec_asks: code that may run a program is never within an auto set without
# `exec`
law cell_exec_asks:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for has: {Ru.elem(caps, Ru.exec()) == True{} : Bool}
  for lacks: {Ru.elem(auto, Ru.exec()) == False{} : Bool}
  {Ru.within(caps, auto) == False{} : Bool}

# ---- runners entry ----

# LAWS (G4, compiled core): the runners of code run as the compiled model
# (bend/ffi_runners.bend over bend/runners.bend; Rust:
# crates/eukhe-bend/src/rules/runners.rs, called by the `ipython` tool's
# gate and the registry test). Each law is an open claim about FRu.ffi,
# the function the core runs, stated with spec spellers built only from
# the wire primitives of bend/wire.bend.
#
# R1: a request Rust writes reads back whole and the entry answers it with
#     the model's decision: whether a call runs unasked (`Ru.within`), how
#     a gated call ends once someone answered or no one could (`Ru.cell`),
#     the tools a session installs (`Ru.registry`).
# R2: every other input answers exactly the error form "runners:
#     malformed request".
# Every input is free: any caps, any auto set, any asker, chat memory or
# not, any text.

# Spec spellers
# -------------

def spell_ns(xs: List<&2, Nat>, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)

def spell_asker(k: Ru.Asker, rest: String) -> String:
  match k:
    case Ru.NoClient{}:
      Wr.put_nat(0n, rest)
    case Ru.Silent{}:
      Wr.put_nat(1n, rest)
    case Ru.Says{y}:
      Wr.put_nat(2n, Wr.put_bool(y, rest))

# the request q as Rust writes it, then rest
def spell_req(q: FRu.Req, rest: String) -> String:
  match q:
    case FRu.QWithin{c, a}:
      Wr.put_nat(0n, spell_ns(c, spell_ns(a, rest)))
    case FRu.QCell{c, a, k}:
      Wr.put_nat(1n, spell_ns(c, spell_ns(a, spell_asker(k, rest))))
    case FRu.QRegistry{h}:
      Wr.put_nat(2n, Wr.put_bool(h, rest))

# a list of Nats fits the wire: its length and each item
def ns_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# every number of a request fits the wire
def req_fits(q: FRu.Req) -> Bool:
  match q:
    case FRu.QWithin{c, a}:
      Bool.and(ns_fit(c), ns_fit(a))
    case FRu.QCell{c, a, k}:
      Bool.and(ns_fit(c), ns_fit(a))
    case FRu.QRegistry{h}:
      True{}

# how a call ended: ran unasked (0, 0) or approved (0, 1); refused,
# denied (1, 0) or unanswered (1, 1)
def spell_end(e: Ru.End) -> String:
  match e:
    case Ru.Ran{h}:
      match h:
        case Ru.Auto{}:
          Wr.put_nat(0n, Wr.put_nat(0n, ""))
        case Ru.Approved{}:
          Wr.put_nat(0n, Wr.put_nat(1n, ""))
    case Ru.Refused{w}:
      match w:
        case Ru.Denied{}:
          Wr.put_nat(1n, Wr.put_nat(0n, ""))
        case Ru.Unanswered{}:
          Wr.put_nat(1n, Wr.put_nat(1n, ""))

# whether a call asked, then how it ended
def spell_out(o: Ru.Out) -> String:
  match o:
    case Ru.Out{a, e}:
      Wr.put_bool(a, spell_end(e))

def spell_gate(g: Ru.Gate) -> Nat:
  match g:
    case Ru.Ungated{}:
      0n
    case Ru.EachStep{}:
      1n
    case Ru.EachCall{}:
      2n

# a tool: its name, its caps, its gate
def spell_tool(t: Ru.Tool, rest: String) -> String:
  match t:
    case Ru.Tool{n, c, g}:
      Wr.put_str(n, spell_ns(c, Wr.put_nat(spell_gate(g), rest)))

# the model's decision on q, spelled
def spell_answer(q: FRu.Req) -> String:
  match q:
    case FRu.QWithin{c, +a}:
      Wr.put_bool(Ru.within(c, a), "")
    case FRu.QCell{c, +a, k}:
      spell_out(Ru.cell(c, a, k))
    case FRu.QRegistry{h}:
      Wr.put_list(~Ru.Tool, ~spell_tool, Ru.registry(h), "")

# the error form of every input that is not exactly one request
def malformed() -> String:
  SCon{'E', SCon{' ', "runners: malformed request"}}

# Reader: the requests, read with the wire primitives
# ---------------------------------------------------

def read_ns(s: String) -> Wr.Dec<List<&2, Nat>>:
  Wr.get_list(~Nat, ~Wr.get_nat, s)

def read_says(r: Wr.Dec<Bool>) -> Wr.Dec<Ru.Asker>:
  match r:
    case Wr.Got{y, s}:
      Wr.Got{Ru.Says{y}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_asker.tag(t: Nat, s: String) -> Wr.Dec<Ru.Asker>:
  match t:
    case 0n:
      Wr.Got{Ru.NoClient{}, s}
    case 1n:
      Wr.Got{Ru.Silent{}, s}
    case 2n:
      read_says(Wr.get_bool(s))
    case 3n+u:
      Wr.Bad{}

def read_asker(r: Wr.Dec<Nat>) -> Wr.Dec<Ru.Asker>:
  match r:
    case Wr.Got{t, s}:
      read_asker.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_within.auto(c: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FRu.Req>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{FRu.QWithin{c, a}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_within(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FRu.Req>:
  match r:
    case Wr.Got{c, s}:
      read_within.auto(c, read_ns(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_cell.asker(c: List<&2, Nat>, a: List<&2, Nat>, r: Wr.Dec<Ru.Asker>) -> Wr.Dec<FRu.Req>:
  match r:
    case Wr.Got{k, s}:
      Wr.Got{FRu.QCell{c, a, k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_cell.auto(c: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FRu.Req>:
  match r:
    case Wr.Got{a, s}:
      read_cell.asker(c, a, read_asker(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_cell(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FRu.Req>:
  match r:
    case Wr.Got{c, s}:
      read_cell.auto(c, read_ns(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_registry(r: Wr.Dec<Bool>) -> Wr.Dec<FRu.Req>:
  match r:
    case Wr.Got{h, s}:
      Wr.Got{FRu.QRegistry{h}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_req.tag(t: Nat, s: String) -> Wr.Dec<FRu.Req>:
  match t:
    case 0n:
      read_within(read_ns(s))
    case 1n:
      read_cell(read_ns(s))
    case 2n:
      read_registry(Wr.get_bool(s))
    case 3n+u:
      Wr.Bad{}

def read_req.go(r: Wr.Dec<Nat>) -> Wr.Dec<FRu.Req>:
  match r:
    case Wr.Got{t, s}:
      read_req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with, and what follows it
def read_req(s: String) -> Wr.Dec<FRu.Req>:
  read_req.go(Wr.get_nat(s))

def spec.end(whole: Bool, q: FRu.Req) -> String:
  match whole:
    case True{}:
      spell_answer(q)
    case False{}:
      malformed()

def spec.run(r: Wr.Dec<FRu.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      spec.end(Wr.end(s), q)
    case Wr.Bad{}:
      malformed()

# the reply to s: the model's decision on the request s is exactly, else
# the error form
def spec(s: String) -> String:
  spec.run(read_req(s))

# LAW runners_ffi_exact: on every input the entry answers the model's decision on the request the input is exactly (whether a call runs unasked; how a gated call ends; the registry), and exactly the error form "runners: malformed request" on any other input
# EXCLUDES: a decision other than the model's (a call run unasked outside
#   the auto set, a denial read as a yes, a tool's gate or caps changed), a
#   default for malformed input, a request misread, input left over
#   ignored, another error text
law runners_ffi_exact:
  for +s: String
  {FRu.ffi(s) == spec(s) : String}

# LAW runners_ffi_answers: every request Rust writes (every number within the wire) gets the model's decision
# EXCLUDES: a request Rust writes refused or misread (the reader and the
#   speller disagree)
law runners_ffi_answers:
  for +q: FRu.Req
  for fits: {req_fits(q) == True{} : Bool}
  {FRu.ffi(spell_req(q, "")) == spell_answer(q) : String}

# LAW runners_ffi_left_over: a request Rust writes followed by more input gets exactly the error form
# EXCLUDES: a second request or trailing bytes read past or ignored
law runners_ffi_left_over:
  for +q: FRu.Req
  for +more: String
  for fits: {req_fits(q) == True{} : Bool}
  for some: {String.is_empty(more) == False{} : Bool}
  {FRu.ffi(spell_req(q, more)) == malformed() : String}

# LAW runners_ffi_example: anchor: the strings Rust sends: caps {exec} under {read} asks, under {exec} runs unasked; a cell under {read} answered yes runs approved, unanswered and with no client is refused unanswered, denied is refused denied; the registry without chat memory; an asker tag 3 is refused
# EXCLUDES: another spelling of a request or a reply
law runners_ffi_example:
  {FRu.ffi("0,1,2,1,0,") == "F" : String} &
  {FRu.ffi("0,1,2,1,2,") == "T" : String} &
  {FRu.ffi("1,1,2,1,0,2,T") == "T0,1," : String} &
  {FRu.ffi("1,1,2,1,0,1,") == "T1,1," : String} &
  {FRu.ffi("1,1,2,1,0,0,") == "F1,1," : String} &
  {FRu.ffi("1,1,2,1,0,2,F") == "T1,0," : String} &
  {FRu.ffi("2,F") == "11,7,ipython1,2,2,8,workflow0,0,4,read0,0,4,edit0,0,4,grep0,0,4,glob0,0,4,bash7,0,1,2,3,4,5,6,1,3,dyn0,0,8,codemode0,0,27,pi.codemode.models.classify0,0,33,pi.codemode.models.generateImages0,0," : String} &
  {FRu.ffi("1,1,2,1,0,3,") == malformed() : String}
