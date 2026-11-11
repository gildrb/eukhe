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

# R4: the call asked
def ru_asked(o: Ru.Out) -> Bool:
  match o:
    case Ru.Out{a, e}:
      a

# R4: a client is attached (it may stay silent)
def ru_client(k: Ru.Asker) -> Bool:
  match k:
    case Ru.NoClient{}:
      False{}
    case Ru.Silent{}:
      True{}
    case Ru.Says{y}:
      True{}

# R4: the user said no
def ru_says_no(k: Ru.Asker) -> Bool:
  match k:
    case Ru.NoClient{}:
      False{}
    case Ru.Silent{}:
      False{}
    case Ru.Says{y}:
      Bool.not(y)

# R4: the call ran unasked
def ru_auto(e: Ru.End) -> Bool:
  match e:
    case Ru.Ran{h}:
      match h:
        case Ru.Auto{}:
          True{}
        case Ru.Approved{}:
          False{}
    case Ru.Refused{w}:
      False{}

# R4: the call was refused as denied
def ru_denied(e: Ru.End) -> Bool:
  match e:
    case Ru.Ran{h}:
      False{}
    case Ru.Refused{w}:
      match w:
        case Ru.Denied{}:
          True{}
        case Ru.Unanswered{}:
          False{}

# LAW gate_covers_every_runner: every tool of a session's registry that runs code that may run a
# program is gated
law gate_covers_every_runner:
  for +i: Nat
  for +t: Ru.ToolReg
  for at: {List.get(&2, Ru.ToolReg, Ru.registry(), i) == Some{t} : Maybe<&2, Ru.ToolReg>}
  for runs: {Ru.runs(t) == True{} : Bool}
  {Ru.gated(t) == True{} : Bool}

# LAW ipython_gated_each_call: the `ipython` tool runs code that may run a program, and the gate
# covers each of its calls
law ipython_gated_each_call:
  {Ru.find(Ru.registry(), "ipython") == Some{Ru.ToolReg{"ipython", [Ru.exec()], Ru.EachCall{}}} : Maybe<&2, Ru.ToolReg>}

# LAW cell_runs_only_within_or_approved: a gated call runs only when its caps are within the auto set or the
# user approves it
law cell_runs_only_within_or_approved:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Ru.Asker
  for ran: {Ru.ran(Ru.cell(caps, auto, a)) == True{} : Bool}
  {Bool.or(Ru.within(caps, auto), Ru.Asker.yes(a)) == True{} : Bool}

# LAW cell_asked (R4): a gated call asks exactly when its caps are not
# within the auto set and a client is attached (silent or answering), for
# every caps, auto set and asker
# EXCLUDES: a call asked without a client, a call within the auto set
#   asked, an asked flag lost for a silent client or a denial
law cell_asked:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Ru.Asker
  {ru_asked(Ru.cell(caps, auto, a)) == Bool.and(Bool.not(Ru.within(caps, auto)), ru_client(a)) : Bool}

# LAW cell_ran_how (R4): a gated call that ran ran unasked (Auto) exactly
# when its caps are within the auto set, else approved
# EXCLUDES: a call outside the auto set reported as unasked, a call within
#   it reported as approved
law cell_ran_how:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Ru.Asker
  for ran: {Ru.ran(Ru.cell(caps, auto, a)) == True{} : Bool}
  {ru_auto(Ru.Out.end(Ru.cell(caps, auto, a))) == Ru.within(caps, auto) : Bool}

# LAW cell_refused_why (R4): a gated call that did not run was denied
# exactly when the user said no, else it ended unanswered
# EXCLUDES: a silent client or no client reported as a denial, a no
#   reported as unanswered
law cell_refused_why:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Ru.Asker
  for stopped: {Ru.ran(Ru.cell(caps, auto, a)) == False{} : Bool}
  {ru_denied(Ru.Out.end(Ru.cell(caps, auto, a))) == ru_says_no(a) : Bool}

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

# (G4) Main's roster: read-only tools and the worker tools
# ---------------------------------------------------------
# docs/usage.md (main and worker). A root session in the `main-worker`
# shape installs `Ru.main_roster`; every other session (a `single` one,
# every child) installs `Ru.registry`. The registry test in
# crates/eukhe-core/src/durable/runner/tests.rs compares each real roster
# with the core's.

# the names of main's read-only tools
def read_names() -> List<&2, String>:
  ["read", "grep", "glob", "zoom", "date"]

# the names of the worker tools
def worker_names() -> List<&2, String>:
  ["worker_assign", "worker_forward", "worker_status"]

# the name n is one of ns
def named_in(+n: String, ns: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case m <> rest:
      Bool.or(String.eq(m, n), named_in(n, rest))

def no_caps(c: List<&2, Nat>) -> Bool:
  match c:
    case Nil{}:
      True{}
    case x <> rest:
      False{}

# the tool runs no code of its own: no caps, not gated
def quiet(t: Ru.ToolReg) -> Bool:
  match t:
    case Ru.ToolReg{n, c, g}:
      Bool.and(no_caps(c), Bool.not(Ru.Gate.gated(g)))

# the tool may be on main's roster: it runs no code of its own and is a
# read-only tool or a worker tool
def main_ok(+t: Ru.ToolReg) -> Bool:
  Bool.and(quiet(t), Bool.or(named_in(Ru.ToolReg.name(t), read_names()), named_in(Ru.ToolReg.name(t), worker_names())))

# the tool is a worker tool
def worker_tool(+t: Ru.ToolReg) -> Bool:
  named_in(Ru.ToolReg.name(t), worker_names())

# LAW main_roster_read_or_workers: every tool of main's roster (the `main-worker` shape, with or without chat memory) runs no code of its own and is a read-only tool (read, grep, glob, zoom, date) or a worker tool (worker_assign, worker_forward, worker_status)
# EXCLUDES: main offered a tool that runs a program (ipython, bash,
#   codemode), edits a file (edit), reaches more tools (dyn) or spawns
#   (workflow)
law main_roster_read_or_workers:
  for +chat: Bool
  for +i: Nat
  for +t: Ru.ToolReg
  for at: {List.get(&2, Ru.ToolReg, Ru.main_roster(chat), i) == Some{t} : Maybe<&2, Ru.ToolReg>}
  {main_ok(t) == True{} : Bool}

# LAW main_roster_offers_workers: main's roster (with or without chat memory) offers the three worker tools, each running no code of its own
# EXCLUDES: a main that cannot hand work over, forward the user's words or
#   see its workers
law main_roster_offers_workers:
  for +chat: Bool
  {Ru.find(Ru.main_roster(chat), "worker_assign") == Some{Ru.plain("worker_assign")} : Maybe<&2, Ru.ToolReg>} &
  {Ru.find(Ru.main_roster(chat), "worker_forward") == Some{Ru.plain("worker_forward")} : Maybe<&2, Ru.ToolReg>} &
  {Ru.find(Ru.main_roster(chat), "worker_status") == Some{Ru.plain("worker_status")} : Maybe<&2, Ru.ToolReg>}

# LAW worker_tools_main_only: no tool of a session's registry outside main (a `single` session, every child; with or without chat memory) is a worker tool
# EXCLUDES: a child or a single session that creates or drives workers
law worker_tools_main_only:
  for +i: Nat
  for +t: Ru.ToolReg
  for at: {List.get(&2, Ru.ToolReg, Ru.registry(), i) == Some{t} : Maybe<&2, Ru.ToolReg>}
  {worker_tool(t) == False{} : Bool}

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
# Every input is free: any caps, any auto set, any asker, any text.

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
    case FRu.QRegistry{}:
      Wr.put_nat(2n, rest)
    case FRu.QMain{h}:
      Wr.put_nat(3n, Wr.put_bool(h, rest))

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
    case FRu.QRegistry{}:
      True{}
    case FRu.QMain{h}:
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
def spell_tool(t: Ru.ToolReg, rest: String) -> String:
  match t:
    case Ru.ToolReg{n, c, g}:
      Wr.put_str(n, spell_ns(c, Wr.put_nat(spell_gate(g), rest)))

# the model's decision on q, spelled
def spell_answer(q: FRu.Req) -> String:
  match q:
    case FRu.QWithin{c, +a}:
      Wr.put_bool(Ru.within(c, a), "")
    case FRu.QCell{c, +a, k}:
      spell_out(Ru.cell(c, a, k))
    case FRu.QRegistry{}:
      Wr.put_list(~Ru.ToolReg, ~spell_tool, Ru.registry(), "")
    case FRu.QMain{h}:
      Wr.put_list(~Ru.ToolReg, ~spell_tool, Ru.main_roster(h), "")

# the error form of every input that is not exactly one request
def malformed() -> String:
  SCon{'E', SCon{' ', "runners: malformed request"}}

# LAW runners_ffi_reads_only_requests (R1, R2): every input the entry does
# not answer with the error form is exactly one request Rust writes
# (spell_req, the wire primitives in Rust's field order)
# EXCLUDES: a default for malformed input (an unknown tag or asker tag, a
#   missing field), input left over answered
law runners_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FRu.ffi(s)) == False{} : Bool}
  exs q: FRu.Req
  {s == spell_req(q, "") : String}

# LAW runners_ffi_refuses (R2): every error the entry answers, on every
# input, is exactly "runners: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form,
#   a decision that opens like the error form
law runners_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FRu.ffi(s)) == True{} : Bool}
  {FRu.ffi(s) == malformed() : String}

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

# LAW runners_ffi_example: anchor, strings spelled by hand from the WIRE.md grammar (no Rust test vector holds them): caps {exec} under {read} asks, under {exec} runs unasked; a cell under {read} answered yes runs approved, unanswered and with no client is refused unanswered, denied is refused denied; the registry; main's roster with chat memory; an asker tag 3 is refused
# EXCLUDES: another spelling of a request or a reply
law runners_ffi_example:
  {FRu.ffi("0,1,2,1,0,") == "F" : String} &
  {FRu.ffi("0,1,2,1,2,") == "T" : String} &
  {FRu.ffi("1,1,2,1,0,2,T") == "T0,1," : String} &
  {FRu.ffi("1,1,2,1,0,1,") == "T1,1," : String} &
  {FRu.ffi("1,1,2,1,0,0,") == "F1,1," : String} &
  {FRu.ffi("1,1,2,1,0,2,F") == "T1,0," : String} &
  {FRu.ffi("2,") == "13,7,ipython1,2,2,4,zoom0,0,4,date0,0,8,workflow0,0,4,read0,0,4,edit0,0,4,grep0,0,4,glob0,0,4,bash7,0,1,2,3,4,5,6,1,3,dyn0,0,8,codemode0,0,27,pi.codemode.models.classify0,0,33,pi.codemode.models.generateImages0,0," : String} &
  {FRu.ffi("3,T") == "8,4,zoom0,0,4,date0,0,13,worker_assign0,0,14,worker_forward0,0,13,worker_status0,0,4,read0,0,4,grep0,0,4,glob0,0," : String} &
  {FRu.ffi("1,1,2,1,0,3,") == malformed() : String}

# ---- runners: the decision, pinned to the requirement ----

# LAWS (G4, the decision): the model the entry answers (runners_ffi_answers)
# is pinned by laws stated from the requirement (bend/runners.bend header,
# crates/eukhe-core/src/durable/registry.rs): R3 by runners_within_sound /
# _complete, R4 by the cell_* laws, R5 by runners_registry_names /
# _quiet, ipython_gated_each_call, bash_gated_each_step, R6 by
# runners_main_names and the main_roster_* laws.
#
# R3: a call runs unasked exactly when each of its caps is a grantable
#     effect (0 read to 5 protected; never 6 secret) in the auto set.
# R4: a gated call within the auto set runs unasked. Outside it, with no
#     client it does not ask and ends unanswered; a client that gives no
#     answer was asked and the call ends unanswered; a yes runs it,
#     approved, a no refuses it, denied (both asked).
# R5: a session installs, in order: `ipython` (caps exec, gated at each
#     call), `zoom` and `date` (with or without chat memory), `workflow`,
#     `read`, `edit`, `grep`, `glob`, `bash` (caps 0 to 6, gated at each
#     step), `dyn`, `codemode`, `pi.codemode.models.classify`,
#     `pi.codemode.models.generateImages` (each of these but `ipython` and
#     `bash` runs no code of its own: no caps, ungated).
# R6: main (a root in the `main-worker` shape) installs, in order: `zoom`
#     and `date` only with chat memory, then `worker_assign`,
#     `worker_forward`, `worker_status`, then `read`, `grep`, `glob` (none
#     runs code of its own: no caps, ungated).

# Spec functions
# --------------

# R3: x is an item of xs
def ru_has(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), ru_has(rest, x))

# R5, R6: the names of the tools ts, in order
def ru_names(ts: List<&2, Ru.ToolReg>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      Ru.ToolReg.name(t) <> ru_names(rest)

# Laws
# ----

# LAW runners_within_sound (R3): when a call runs unasked, each of its caps
# is a grantable effect (below 6, never secret) in the auto set
# EXCLUDES: a cap outside the auto set run unasked, the secret effect run
#   unasked
law runners_within_sound:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +i: Nat
  for +c: Nat
  for free: {Ru.within(caps, auto) == True{} : Bool}
  for at: {List.get(&2, Nat, caps, i) == Some{c} : Maybe<&2, Nat>}
  {Bool.and(Nat.is_lt(c, 6n), ru_has(auto, c)) == True{} : Bool}

# LAW runners_within_complete (R3): when a call does not run unasked, some
# cap of it is not a grantable effect in the auto set
# EXCLUDES: a call whose every cap is granted asked anyway
law runners_within_complete:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for held: {Ru.within(caps, auto) == False{} : Bool}
  exs i: Nat
  exs c: Nat
  {List.get(&2, Nat, caps, i) == Some{c} : Maybe<&2, Nat>} & {Bool.and(Nat.is_lt(c, 6n), ru_has(auto, c)) == False{} : Bool}

# LAW runners_registry_names (R5): a session installs exactly these tools,
# in this order (the R5 list; crates/eukhe-core/src/durable/registry.rs)
# EXCLUDES: a tool lost, added, renamed or moved
law runners_registry_names:
  {ru_names(Ru.registry()) == ["ipython", "zoom", "date", "workflow", "read", "edit", "grep", "glob", "bash", "dyn", "codemode", "pi.codemode.models.classify", "pi.codemode.models.generateImages"] : List<&2, String>}

# LAW runners_registry_quiet (R5): every tool a session installs other than
# `ipython` and `bash` runs no code of its own: no caps, ungated
# EXCLUDES: a tool given caps or a gate it does not have (a spurious ask),
#   a tool that runs code past the gate
law runners_registry_quiet:
  for +i: Nat
  for +t: Ru.ToolReg
  for at: {List.get(&2, Ru.ToolReg, Ru.registry(), i) == Some{t} : Maybe<&2, Ru.ToolReg>}
  for other: {named_in(Ru.ToolReg.name(t), ["ipython", "bash"]) == False{} : Bool}
  {quiet(t) == True{} : Bool}

# LAW bash_gated_each_step (R5): the `bash` tool has the caps 0 to 6 and the
# gate covers each of its steps
# EXCLUDES: a bash step run past the gate, a cap of bash lost
law bash_gated_each_step:
  {Ru.find(Ru.registry(), "bash") == Some{Ru.ToolReg{"bash", [0n, 1n, 2n, 3n, 4n, 5n, 6n], Ru.EachStep{}}} : Maybe<&2, Ru.ToolReg>}

# LAW runners_main_names (R6): main installs, in order, `zoom` and `date`
# only with chat memory, then the three worker tools, then `read`, `grep`,
# `glob` (both values of the chat flag: the whole domain)
# EXCLUDES: chat tools on main without chat memory, a worker tool lost, a
#   tool moved
law runners_main_names:
  {[ru_names(Ru.main_roster(True{})), ru_names(Ru.main_roster(False{}))] == [["zoom", "date", "worker_assign", "worker_forward", "worker_status", "read", "grep", "glob"], ["worker_assign", "worker_forward", "worker_status", "read", "grep", "glob"]] : List<&2, List<&2, String>>}

# LAW cell_within_runs_unasked: a call whose caps are within the auto set runs, unasked
law cell_within_runs_unasked:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for a: Ru.Asker
  for free: {Ru.within(caps, auto) == True{} : Bool}
  {Ru.cell(caps, auto, a) == Ru.Out{False{}, Ru.Ran{Ru.Auto{}}} : Ru.Out}

# R4: how a gated call goes; free: it runs unasked (R3)
def ru_cell(free: Bool, a: Ru.Asker) -> Ru.Out:
  match free:
    case True{}:
      Ru.Out{False{}, Ru.Ran{Ru.Auto{}}}
    case False{}:
      match a:
        case Ru.NoClient{}:
          Ru.Out{False{}, Ru.Refused{Ru.Unanswered{}}}
        case Ru.Silent{}:
          Ru.Out{True{}, Ru.Refused{Ru.Unanswered{}}}
        case Ru.Says{y}:
          match y:
            case True{}:
              Ru.Out{True{}, Ru.Ran{Ru.Approved{}}}
            case False{}:
              Ru.Out{True{}, Ru.Refused{Ru.Denied{}}}

# R3: an auto set may hold effect c (0 to 5)
def ru_grantable(c: Nat) -> Bool:
  Nat.is_lt(c, 6n)

# R3: every cap is grantable and in the auto set
def ru_within(caps: List<&2, Nat>, +auto: List<&2, Nat>) -> Bool:
  match caps:
    case Nil{}:
      True{}
    case +c <> rest:
      Bool.and(Bool.and(ru_grantable(c), ru_has(auto, c)), ru_within(rest, auto))

# LAW runners_cell_spec: a gated call within the auto set runs unasked; outside it, no client ends unanswered unasked, a silent client unanswered asked, a yes runs approved, a no is denied
# EXCLUDES: a call asked without a client, a silent client read as a
#   denial or a yes, an asked flag lost, a denial that runs
law runners_cell_spec:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for a: Ru.Asker
  {Ru.cell(caps, auto, a) == ru_cell(ru_within(caps, auto), a) : Ru.Out}

# LAW runners_within_spec: a call runs unasked exactly when each cap is a grantable effect (0 to 5) in the auto set
# EXCLUDES: a cap outside the auto set run unasked, the secret effect run
#   unasked, a cap in the auto set asked
law runners_within_spec:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  {Ru.within(caps, auto) == ru_within(caps, auto) : Bool}

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

def read_ns(s: String) -> Wr.Dec<List<&2, Nat>>:
  Wr.get_list(~Nat, ~Wr.get_nat, s)

def read_cell(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FRu.Req>:
  match r:
    case Wr.Got{c, s}:
      read_cell.auto(c, read_ns(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_main(r: Wr.Dec<Bool>) -> Wr.Dec<FRu.Req>:
  match r:
    case Wr.Got{h, s}:
      Wr.Got{FRu.QMain{h}, s}
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

def read_req.tag(t: Nat, s: String) -> Wr.Dec<FRu.Req>:
  match t:
    case 0n:
      read_within(read_ns(s))
    case 1n:
      read_cell(read_ns(s))
    case 2n:
      Wr.Got{FRu.QRegistry{}, s}
    case 3n:
      read_main(Wr.get_bool(s))
    case 4n+u:
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

# R5: a tool that runs no code of its own
def ru_plain(n: String) -> Ru.ToolReg:
  Ru.ToolReg{n, Nil{}, Ru.Ungated{}}

# R6: main's roster, with chat memory or without
def ru_main_roster(chat: Bool) -> List<&2, Ru.ToolReg>:
  match chat:
    case True{}:
      [ru_plain("zoom"), ru_plain("date"), ru_plain("worker_assign"), ru_plain("worker_forward"), ru_plain("worker_status"), ru_plain("read"), ru_plain("grep"), ru_plain("glob")]
    case False{}:
      [ru_plain("worker_assign"), ru_plain("worker_forward"), ru_plain("worker_status"), ru_plain("read"), ru_plain("grep"), ru_plain("glob")]

# R5: every tool a session installs
def ru_registry() -> List<&2, Ru.ToolReg>:
  [Ru.ToolReg{"ipython", [2n], Ru.EachCall{}}, ru_plain("zoom"), ru_plain("date"), ru_plain("workflow"), ru_plain("read"), ru_plain("edit"), ru_plain("grep"), ru_plain("glob"), Ru.ToolReg{"bash", [0n, 1n, 2n, 3n, 4n, 5n, 6n], Ru.EachStep{}}, ru_plain("dyn"), ru_plain("codemode"), ru_plain("pi.codemode.models.classify"), ru_plain("pi.codemode.models.generateImages")]

# the reply R3-R6 give a request
def ru_reply(q: FRu.Req) -> String:
  match q:
    case FRu.QWithin{c, +a}:
      Wr.put_bool(ru_within(c, a), "")
    case FRu.QCell{c, +a, k}:
      spell_out(ru_cell(ru_within(c, a), k))
    case FRu.QRegistry{}:
      Wr.put_list(~Ru.ToolReg, ~spell_tool, ru_registry(), "")
    case FRu.QMain{h}:
      Wr.put_list(~Ru.ToolReg, ~spell_tool, ru_main_roster(h), "")

def ru_spec.end(whole: Bool, q: FRu.Req) -> String:
  match whole:
    case True{}:
      ru_reply(q)
    case False{}:
      malformed()

def ru_spec.run(r: Wr.Dec<FRu.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      ru_spec.end(Wr.end(s), q)
    case Wr.Bad{}:
      malformed()

# the reply R1-R5 give the input s: the reply to the request s is exactly,
# else the error form
def ru_spec(s: String) -> String:
  ru_spec.run(read_req(s))

# LAW runners_ffi_spec: on every input the entry answers the reply R3-R5 give the request the input is exactly, and the error form on any other input
# EXCLUDES: a decision the model computes wrong (a call run unasked
#   outside the auto set, a denial run, a tool lost from the registry), a
#   default for malformed input, input left over ignored
law runners_ffi_spec:
  for +s: String
  {FRu.ffi(s) == ru_spec(s) : String}

# LAW runners_registry_spec: a session installs exactly the R5 tools, in order
# EXCLUDES: a tool lost, added or moved; a caps list or gate changed
law runners_registry_spec:
  {Ru.registry() == ru_registry() : List<&2, Ru.ToolReg>}

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
