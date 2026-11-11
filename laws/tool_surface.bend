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
# `ToolSurface` as tools join, quit and are called through `dyn`). The
# wire laws are open claims about FTs.ffi, the function the core runs,
# stated with spec spellers built only from the wire primitives of
# bend/wire.bend; the decision laws are properties of the model the entry
# answers (Tl.build, Tl.step, Tl.dyn_call), stated without its helpers.
#
# Requirements (sources: crates/eukhe-bend/src/rules/tool_surface.rs and
# its test `the_codec_carries_each_question_through_the_core`;
# bend/tools.bend header 1-2; crates/eukhe-bend/WIRE.md):
# R1: a request Rust writes reads back whole and the entry answers it with
#     the model's decision: the schema the harness sends (`Tl.build`), the
#     dynamic tools after a tool joins or quits (`Tl.step`), whether a
#     call through `dyn` reaches a tool (`Tl.dyn_call`).
# R2: every other input answers exactly the error form "tool_surface:
#     malformed request".
# R3: the schema the harness sends holds the declared parameters, in
#     order, preceded by the intent parameter (0) when they do not hold it;
#     its version is the declared one, or 1 when that is 0.
# R4: a tool that joins goes in front of the dynamic tools (newest first);
#     the others stay, in order.
# R5: a tool that quits leaves the dynamic tools: every copy of it goes,
#     the others stay, in order.
# R6: a call through `dyn` reaches a tool exactly when it is among the
#     dynamic tools.
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

# Laws: the entry (R1, R2)
# ------------------------

# LAW tool_surface_ffi_answers (R1): every request Rust writes (every number within the wire) gets the model's decision
# EXCLUDES: a request Rust writes refused or misread
law tool_surface_ffi_answers:
  for +q: FTs.Req
  for fits: {req_fits(q) == True{} : Bool}
  {FTs.ffi(spell_req(q, "")) == spell_answer(q) : String}

# LAW tool_surface_ffi_left_over (R2): a request Rust writes followed by more input gets exactly the error form
# EXCLUDES: a second request or trailing bytes read past or ignored
law tool_surface_ffi_left_over:
  for +q: FTs.Req
  for +more: String
  for fits: {req_fits(q) == True{} : Bool}
  for some: {String.is_empty(more) == False{} : Bool}
  {FTs.ffi(spell_req(q, more)) == malformed() : String}

# LAW tool_surface_ffi_example (R1, R2): anchor: the strings Rust sends: a schema of two parameters and no version gets the intent first and version 1; one that holds the intent at version 5 is kept; tool 4 joins; tool 4 quits (every copy); `dyn` reaches a joined tool and not an absent one; tag 4 is refused
# EXCLUDES: another spelling of a request or a reply
law tool_surface_ffi_example:
  {FTs.ffi("0,2,2,3,0,") == "3,0,2,3,1," : String} &
  {FTs.ffi("0,2,0,2,5,") == "2,0,2,5," : String} &
  {FTs.ffi("1,1,4,4,") == "2,4,4," : String} &
  {FTs.ffi("2,3,4,2,4,4,") == "1,2," : String} &
  {FTs.ffi("3,1,4,4,") == "T" : String} &
  {FTs.ffi("3,0,4,") == "F" : String} &
  {FTs.ffi("4,") == malformed() : String}

# LAW tool_surface_ffi_reads_only_requests (R1, R2): an answer that is not the error form "tool_surface: malformed request" answers a request: the input is exactly the spelling of a request whose numbers fit the wire, with nothing after it, and the answer is the model's decision on it, spelled (with tool_surface_ffi_answers and tool_surface_ffi_left_over this pins the answer to every input)
# EXCLUDES: an unknown tag (4 and up), a short or overlong field or input
#   left over answered with a decision or a default, another error text, a
#   second spelling of a request accepted
law tool_surface_ffi_reads_only_requests:
  for +s: String
  for other: {String.eq(FTs.ffi(s), malformed()) == False{} : Bool}
  exs q: FTs.Req
  {(s, (req_fits(q), FTs.ffi(s))) == (spell_req(q, ""), (True{}, spell_answer(q))) : String & (Bool & String)}

# ---- tool_surface: the decision (R3-R6) ----

# The decision the entry answers, stated as properties of the model's
# build, step and dyn_call, with no helper of the model: each law below
# holds of R3-R6 and a model that breaks R3-R6 breaks one of them.
# Together they pin the decision whole: R3 by schema_has_intent (laws/
# tools.bend) with the three build laws (at most one parameter put before
# the declared ones, none when they hold the intent, so exactly the
# intent when they lack it); R5 by dyn_drops_quit (laws/tools.bend) with
# the two quit laws (a copy of the quitting tool changes nothing, a list
# without it stays: by induction on its copies, the list without them);
# R6 by the two reach laws.

# Terms
# -----

def ts_one(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# how many copies of t xs holds
def ts_count(xs: List<&2, Nat>, +t: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case y <> rest:
      Nat.add(ts_one(Nat.is_eq(y, t)), ts_count(rest, t))

# the session after the tools ts join, one after the other, from s
def ts_join_all(ts: List<&2, Nat>, s: Tl.Sess) -> Tl.Sess:
  match ts:
    case Nil{}:
      s
    case t <> rest:
      ts_join_all(rest, Tl.step(s, Tl.Join{t}))

# Laws
# ----

# LAW tool_surface_build_adds_at_most_one (R3): the parameters the harness sends for any schema are its declared parameters, in order, with at most one parameter put before them (schema_has_intent: that one is the intent when the declared ones lack it)
# EXCLUDES: a declared parameter lost, moved or repeated, a parameter
#   added after or among the declared ones, the intent added twice
law tool_surface_build_adds_at_most_one:
  for +ps: List<&2, Nat>
  for v: Nat
  exs pre: List<&2, Nat>
  {(Tl.Schema.params(Tl.build(Tl.Schema{ps, v})), Nat.is_le(List.length(&2, Nat, pre), 1n)) == (List.append(&2, Nat, pre, ps), True{}) : List<&2, Nat> & Bool}

# LAW tool_surface_build_keeps_declared_intent (R3): a schema that declares the intent (0) at any place among its parameters is sent with exactly its declared parameters, at any version
# EXCLUDES: a second intent added, the declared intent moved to the front
#   or dropped
law tool_surface_build_keeps_declared_intent:
  for +pre: List<&2, Nat>
  for +post: List<&2, Nat>
  for v: Nat
  {Tl.Schema.params(Tl.build(Tl.Schema{List.append(&2, Nat, pre, 0n <> post), v})) == List.append(&2, Nat, pre, 0n <> post) : List<&2, Nat>}

# LAW tool_surface_build_version (R3): a declared version 1 + w is sent as declared, version 0 as 1, whatever the parameters
# EXCLUDES: a version 0 sent, a declared version raised, lowered or reset
law tool_surface_build_version:
  for +ps: List<&2, Nat>
  for +w: Nat
  {(Tl.Schema.version(Tl.build(Tl.Schema{ps, 0n})), Tl.Schema.version(Tl.build(Tl.Schema{ps, 1n+w}))) == (1n, 1n+w) : Nat & Nat}

# LAW tool_surface_joins_newest_first (R4): after the tools ts join one after the other, the dynamic tools are ts newest first (List.reverse), in front of the dynamic tools before, in their order; roster and requests sent are any
# EXCLUDES: a joined tool put behind the others or lost, joins kept
#   oldest first, a dynamic tool lost, moved or repeated by a join
law tool_surface_joins_newest_first:
  for +ts: List<&2, Nat>
  for r: List<&2, Nat>
  for +d: List<&2, Nat>
  for x: List<&2, List<&2, Nat>>
  {Tl.Sess.dyn(ts_join_all(ts, Tl.Sess{r, d, x})) == List.append(&2, Nat, List.reverse(&2, Nat, ts), d) : List<&2, Nat>}

# LAW tool_surface_quit_keeps_absent (R5): a quit of a tool that the dynamic tools do not hold (no copy) leaves them exactly as they are
# EXCLUDES: a quit that drops, reorders or repeats another tool
law tool_surface_quit_keeps_absent:
  for r: List<&2, Nat>
  for +d: List<&2, Nat>
  for x: List<&2, List<&2, Nat>>
  for +t: Nat
  for none: {ts_count(d, t) == 0n : Nat}
  {Tl.Sess.dyn(Tl.step(Tl.Sess{r, d, x}, Tl.Quit{t})) == d : List<&2, Nat>}

# LAW tool_surface_quit_drops_every_copy (R5): a copy of the quitting tool at any place among the dynamic tools changes nothing in what the quit leaves
# EXCLUDES: a quit that keeps a copy (the first, the last), or that drops
#   or moves another tool next to a copy
law tool_surface_quit_drops_every_copy:
  for r: List<&2, Nat>
  for +pre: List<&2, Nat>
  for +post: List<&2, Nat>
  for x: List<&2, List<&2, Nat>>
  for +t: Nat
  {Tl.Sess.dyn(Tl.step(Tl.Sess{r, List.append(&2, Nat, pre, t <> post), x}, Tl.Quit{t})) == Tl.Sess.dyn(Tl.step(Tl.Sess{r, List.append(&2, Nat, pre, post), x}, Tl.Quit{t})) : List<&2, Nat>}

# LAW tool_surface_reaches_present (R6): a call through `dyn` reaches a tool that is at any place among the dynamic tools
# EXCLUDES: a present tool missed (one past the first, a repeated one)
law tool_surface_reaches_present:
  for r: List<&2, Nat>
  for +pre: List<&2, Nat>
  for +t: Nat
  for post: List<&2, Nat>
  for x: List<&2, List<&2, Nat>>
  {Tl.dyn_call(Tl.Sess{r, List.append(&2, Nat, pre, t <> post), x}, t) == True{} : Bool}

# LAW tool_surface_misses_absent (R6): a call through `dyn` never reaches a tool that the dynamic tools do not hold (no copy)
# EXCLUDES: an absent tool reached (a roster tool, any tool, a near id)
law tool_surface_misses_absent:
  for r: List<&2, Nat>
  for +d: List<&2, Nat>
  for x: List<&2, List<&2, Nat>>
  for +t: Nat
  for none: {ts_count(d, t) == 0n : Nat}
  {Tl.dyn_call(Tl.Sess{r, d, x}, t) == False{} : Bool}
