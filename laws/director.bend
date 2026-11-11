# eukhe: the laws of area director

import Base
import ../bend/director.bend as Dr
import ../bend/ffi_director.bend as FDr
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S5) The Director stack
# -----------------------
# The model in bend/director.bend, which the Rust code runs as the
# compiled core (crates/eukhe-core/src/durable/directors/stack.rs
# `Loop::tick`, entry bend/ffi_director.bend). Every verdict is free:
# each layer of each step says what the adversary picks. Requirements
# (stack.rs `Verdict` and `Loop::tick` doc comments, the header of
# bend/director.bend; omp has no Director stack, so they are eukhe's own):
#
# R1: the top layer decides first. A layer that says Defer, or has no
#     verdict, stays where it is and the next layer down decides; a layer
#     that says Unstack is removed and the next layer down decides. The
#     first layer with another verdict decides; verdicts past the stack's
#     last layer are never read.
# R2: Yield stops the loop and hands back to the user; Abort stops it
#     with a failure. The deciding layer and the layers below it stay as
#     they are.
# R3: Again goes on and costs the deciding layer one unit of its budget;
#     with no budget left it yields instead, nothing spent.
# R4: Stack{p} puts p right on top of the deciding layer (under the
#     layers above it that stay) and goes on; it costs the deciding layer
#     one unit; with no budget left it yields instead, nothing spent,
#     nothing pushed. A stack that holds cap layers already (every layer
#     counted, those above the deciding one too) has no room: the step
#     fails, the unit spent, nothing pushed.
# R5: Lead (a reminder) leaves with the continuation it leads: when the
#     step goes on it leaves, when the step ends the loop it stays. Either
#     way the next layer down decides.
# R6: with no layer left to decide (every layer deferred, left or had no
#     verdict) the loop hands back to the user.
# R7: the loop has a global budget of steps: a step that goes on costs
#     exactly one step, a step that ends the loop costs none. A continue
#     with no step left ends the loop handed back, with the stack that
#     step leaves (the unit spent, a pushed layer pushed, a layer that
#     leads staying; the Rust test
#     `the_global_budget_hands_back_whatever_the_layers_say` pins the
#     spent unit).
# R8: an ended loop stays as it ended, whatever the layers say
#     (dir_ended_stays_any_outcome, dir_ffi_ended_stays_any_outcome).
# R9: the loop ends after at most n + 1 steps of a global budget n
#     (dir_loop_ends).
# R10: no step grows the stack past its cap (dir_stack_bounded,
#     dir_loop_stack_bounded).
# R11: a run of steps is those steps, one after another, first first.
# R12: the entry answers each request Rust writes with the loop after
#     the step, spelled in Rust's grammar (crates/eukhe-bend/WIRE.md), and
#     any other input with the exact error forms (the entry section).
# A1: Dr.encode/Dr.decode, the model's spelling of the stack as session
#     tree nodes, read back what they write (dir_resume_restores). No
#     entry calls them: Rust keeps the stack in the rewindable
#     eukhe.directors document (crates/eukhe-core/src/durable/directors/
#     mod.rs), whose resume and rewind the Rust tests check, unproven.

# LAW dir_stack_bounded: a decision never grows the stack past its cap
law dir_stack_bounded:
  for +s: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +cap: Nat
  for fits: {Nat.is_le(List.length(&2, Dr.Layer, s), cap) == True{} : Bool}
  {Nat.is_le(List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.decide(s, vs, cap))), cap) == True{} : Bool}

# LAW dir_loop_stack_bounded: so neither does the loop, whatever its steps
law dir_loop_stack_bounded:
  for vss: List<&2, List<&2, Dr.Verdict>>
  for +cap: Nat
  for +l: Dr.Loop
  for fits: {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(l)), cap) == True{} : Bool}
  {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(Dr.run(vss, cap, l))), cap) == True{} : Bool}

# the outcome o stops the loop: a hand back or a failure
def dir_stops(o: Dr.Out) -> Bool:
  match o:
    case Dr.Cont{}:
      False{}
    case Dr.Hand{}:
      True{}
    case Dr.Failed{}:
      True{}

# the loop l has stopped: its end field holds a hand back or a failure
def dir_stopped(l: Dr.Loop) -> Bool:
  match l:
    case Dr.Loop{n, s, e}:
      match e:
        case None{}:
          False{}
        case Some{o}:
          dir_stops(o)

# the loop l still runs: its end field holds no outcome
def dir_running(l: Dr.Loop) -> Bool:
  match l:
    case Dr.Loop{n, s, e}:
      match e:
        case None{}:
          True{}
        case Some{o}:
          False{}

# LAW dir_loop_ends (R9): a running loop with global budget n, after n + 1
# steps, has stopped: its end field holds a hand back or a failure (never
# a continue, never no outcome), whatever every layer says and whatever
# the cap and the stack: no Director keeps the loop going for ever
# EXCLUDES: a loop that runs past its global budget, a step that ends the
#   loop without an outcome or with a continue, an ended loop the model's
#   own `ended` test misreads (the law reads the end field, not Dr.ended)
law dir_loop_ends:
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +vss: List<&2, List<&2, Dr.Verdict>>
  for +cap: Nat
  for long: {List.length(&2, List<&2, Dr.Verdict>, vss) == 1n+n : Nat}
  {dir_stopped(Dr.run(vss, cap, Dr.Loop{n, s, None{}})) == True{} : Bool}

# LAW dir_ended_stays_any_outcome (R8): a loop that has ended, with any outcome
# (continue, hand back or failure), any steps left and any stack, is left
# by a step exactly as it ended, whatever the cap and whatever every
# layer says
# EXCLUDES: an ended loop (of any outcome, a continue included) revived as
#   running, a step or a unit charged, a layer pushed, left or changed, the
#   outcome rewritten
law dir_ended_stays_any_outcome:
  for +cap: Nat
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +o: Dr.Out
  for vs: List<&2, Dr.Verdict>
  {Dr.tick(cap, Dr.Loop{n, s, Some{o}}, vs) == Dr.Loop{n, s, Some{o}} : Dr.Loop}

# LAW dir_resume_restores (A1): the model's tree spelling of a stack reads back
# as that stack (Dr.decode of Dr.encode), exactly. A model-only claim: no
# entry calls Dr.encode or Dr.decode, and the Rust code resumes the stack
# from the eukhe.directors document, which this law does not cover
law dir_resume_restores:
  for +s: List<&2, Dr.Layer>
  {Dr.decode(Dr.encode(s)) == s : List<&2, Dr.Layer>}

# The step, verdict by verdict
# ----------------------------
# Each law below takes a running loop whose stack is the layers a above
# the deciding layer above the layers b, and verdicts that give each
# layer of a its verdict of va (one each, in order, each Defer or Unstack),
# the deciding layer its verdict, and then anything (vr, never read). A
# Lead is read by the lead laws further down (R5): with them, and with
# dir_step_no_verdict_defers for a stack longer than its verdicts, these
# laws give every step of a running loop.

# R1: a verdict that passes the decision to the next layer down and
# leaves no doubt whether its layer stays: Defer (it stays), Unstack (it
# goes)
def dir_passes(v: Dr.Verdict) -> Bool:
  match v:
    case Dr.Defer{}:
      True{}
    case Dr.Again{}:
      False{}
    case Dr.Yield{}:
      False{}
    case Dr.Stack{p}:
      False{}
    case Dr.Unstack{}:
      True{}
    case Dr.Abort{}:
      False{}
    case Dr.Lead{}:
      False{}

# R1: every verdict of vs passes
def dir_all_pass(vs: List<&2, Dr.Verdict>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case v <> rest:
      Bool.and(dir_passes(v), dir_all_pass(rest))

# R1: the layers of a that stay, each saying its verdict of va (in
# order): a layer that says Unstack is gone, every other one stays where it
# is
def dir_stayers(a: List<&2, Dr.Layer>, va: List<&2, Dr.Verdict>) -> List<&2, Dr.Layer>:
  match a:
    case Nil{}:
      Nil{}
    case l <> t:
      match va:
        case Nil{}:
          l <> t
        case v <> vt:
          match v:
            case Dr.Defer{}:
              l <> dir_stayers(t, vt)
            case Dr.Again{}:
              l <> dir_stayers(t, vt)
            case Dr.Yield{}:
              l <> dir_stayers(t, vt)
            case Dr.Stack{p}:
              l <> dir_stayers(t, vt)
            case Dr.Unstack{}:
              dir_stayers(t, vt)
            case Dr.Abort{}:
              l <> dir_stayers(t, vt)
            case Dr.Lead{}:
              l <> dir_stayers(t, vt)

# R3, R4: the verdicts that ask the loop to go on at the cost of a unit
def dir_asks_a_step(v: Dr.Verdict) -> Bool:
  match v:
    case Dr.Defer{}:
      False{}
    case Dr.Again{}:
      True{}
    case Dr.Yield{}:
      False{}
    case Dr.Stack{p}:
      True{}
    case Dr.Unstack{}:
      False{}
    case Dr.Abort{}:
      False{}
    case Dr.Lead{}:
      False{}

# LAW dir_step_undecided (R1, R6): a running loop whose every layer says Defer or
# Unstack (one verdict a layer, in order, any verdicts after them) ends
# handed back with its steps left; the layers that said Unstack are gone,
# the others stay in order
# EXCLUDES: no deciding layer read as a continue or a failure; an Unstack
#   kept, a Defer dropped, layers reordered; a verdict past the stack
#   read; a step charged for a hand back
law dir_step_undecided:
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +va: List<&2, Dr.Verdict>
  for +vr: List<&2, Dr.Verdict>
  for +cap: Nat
  for one: {Nat.is_eq(List.length(&2, Dr.Layer, s), List.length(&2, Dr.Verdict, va)) == True{} : Bool}
  for pass: {dir_all_pass(va) == True{} : Bool}
  {Dr.tick(cap, Dr.Loop{n, s, None{}}, List.append(&2, Dr.Verdict, va, vr)) == Dr.Loop{n, dir_stayers(s, va), Some{Dr.Hand{}}} : Dr.Loop}

# LAW dir_step_no_verdict_defers (R1): a layer with no verdict defers: one more Defer after
# the verdicts changes no step, of any loop
# EXCLUDES: a missing verdict read as Again, Yield, Unstack or any verdict
#   but Defer; a short verdict list refused or misaligned
law dir_step_no_verdict_defers:
  for +cap: Nat
  for +l: Dr.Loop
  for +vs: List<&2, Dr.Verdict>
  {Dr.tick(cap, l, vs) == Dr.tick(cap, l, List.append(&2, Dr.Verdict, vs, [Dr.Defer{}])) : Dr.Loop}

# LAW dir_step_yield (R1, R2): a running loop whose deciding layer says Yield ends
# handed back with its steps left; the layers above it that said Unstack are
# gone, the others stay; the deciding layer and those below stay as they
# are
# EXCLUDES: a Yield that goes on, fails, charges a step or a unit, drops
#   or reorders a layer; a decision by a layer below a deciding one
law dir_step_yield:
  for +n: Nat
  for +a: List<&2, Dr.Layer>
  for +d: Dr.Layer
  for +b: List<&2, Dr.Layer>
  for +va: List<&2, Dr.Verdict>
  for +vr: List<&2, Dr.Verdict>
  for +cap: Nat
  for one: {Nat.is_eq(List.length(&2, Dr.Layer, a), List.length(&2, Dr.Verdict, va)) == True{} : Bool}
  for pass: {dir_all_pass(va) == True{} : Bool}
  {Dr.tick(cap, Dr.Loop{n, List.append(&2, Dr.Layer, a, d <> b), None{}}, List.append(&2, Dr.Verdict, va, Dr.Yield{} <> vr)) == Dr.Loop{n, List.append(&2, Dr.Layer, dir_stayers(a, va), d <> b), Some{Dr.Hand{}}} : Dr.Loop}

# LAW dir_step_abort (R1, R2): a running loop whose deciding layer says Abort ends failed
# with its steps left; the layers above it that said Unstack are gone, the
# others stay; the deciding layer and those below stay as they are
# EXCLUDES: an Abort read as a hand back or a continue, a step or a unit
#   charged, a layer dropped or reordered
law dir_step_abort:
  for +n: Nat
  for +a: List<&2, Dr.Layer>
  for +d: Dr.Layer
  for +b: List<&2, Dr.Layer>
  for +va: List<&2, Dr.Verdict>
  for +vr: List<&2, Dr.Verdict>
  for +cap: Nat
  for one: {Nat.is_eq(List.length(&2, Dr.Layer, a), List.length(&2, Dr.Verdict, va)) == True{} : Bool}
  for pass: {dir_all_pass(va) == True{} : Bool}
  {Dr.tick(cap, Dr.Loop{n, List.append(&2, Dr.Layer, a, d <> b), None{}}, List.append(&2, Dr.Verdict, va, Dr.Abort{} <> vr)) == Dr.Loop{n, List.append(&2, Dr.Layer, dir_stayers(a, va), d <> b), Some{Dr.Failed{}}} : Dr.Loop}

# LAW dir_step_spent (R1, R3, R4): a running loop whose deciding layer has no budget left
# and says Again or Stack ends handed back with its steps left; nothing is
# spent or pushed; the layers above it that said Unstack are gone, the
# others stay
# EXCLUDES: a budget that goes below zero or is ignored (a continue on no
#   budget), a layer pushed on no budget, a spent budget read as a failure
law dir_step_spent:
  for +n: Nat
  for +a: List<&2, Dr.Layer>
  for +k: Nat
  for +b: List<&2, Dr.Layer>
  for +va: List<&2, Dr.Verdict>
  for +v: Dr.Verdict
  for +vr: List<&2, Dr.Verdict>
  for +cap: Nat
  for one: {Nat.is_eq(List.length(&2, Dr.Layer, a), List.length(&2, Dr.Verdict, va)) == True{} : Bool}
  for pass: {dir_all_pass(va) == True{} : Bool}
  for asks: {dir_asks_a_step(v) == True{} : Bool}
  {Dr.tick(cap, Dr.Loop{n, List.append(&2, Dr.Layer, a, Dr.Layer{k, 0n} <> b), None{}}, List.append(&2, Dr.Verdict, va, v <> vr)) == Dr.Loop{n, List.append(&2, Dr.Layer, dir_stayers(a, va), Dr.Layer{k, 0n} <> b), Some{Dr.Hand{}}} : Dr.Loop}

# LAW dir_step_again (R1, R3, R7): a running loop with a step left whose deciding layer
# has budget and says Again goes on: it costs the loop exactly one step
# and the deciding layer exactly one unit; the layers above it that said
# Unstack are gone, the others stay; nothing else changes
# EXCLUDES: an Again that costs no unit or two, charges another layer,
#   costs no step, ends the loop, or drops, adds or reorders a layer
law dir_step_again:
  for +m: Nat
  for +a: List<&2, Dr.Layer>
  for +k: Nat
  for +c: Nat
  for +b: List<&2, Dr.Layer>
  for +va: List<&2, Dr.Verdict>
  for +vr: List<&2, Dr.Verdict>
  for +cap: Nat
  for one: {Nat.is_eq(List.length(&2, Dr.Layer, a), List.length(&2, Dr.Verdict, va)) == True{} : Bool}
  for pass: {dir_all_pass(va) == True{} : Bool}
  {Dr.tick(cap, Dr.Loop{1n+m, List.append(&2, Dr.Layer, a, Dr.Layer{k, 1n+c} <> b), None{}}, List.append(&2, Dr.Verdict, va, Dr.Again{} <> vr)) == Dr.Loop{m, List.append(&2, Dr.Layer, dir_stayers(a, va), Dr.Layer{k, c} <> b), None{}} : Dr.Loop}

# LAW dir_step_push (R1, R4, R7): a running loop with a step left whose deciding layer
# has budget and says Stack{p}, its whole stack holding fewer than cap
# layers, goes on with p right on top of the deciding layer: it costs the
# loop exactly one step and the deciding layer exactly one unit; the
# layers above it that said Unstack are gone, the others stay above p
# EXCLUDES: a push past the cap or refused below it, room counted on part
#   of the stack, p put on the very top or under the deciding layer, a
#   push that costs no unit or no step, a pushed layer changed
law dir_step_push:
  for +m: Nat
  for +a: List<&2, Dr.Layer>
  for +k: Nat
  for +c: Nat
  for +b: List<&2, Dr.Layer>
  for +p: Dr.Layer
  for +va: List<&2, Dr.Verdict>
  for +vr: List<&2, Dr.Verdict>
  for +cap: Nat
  for one: {Nat.is_eq(List.length(&2, Dr.Layer, a), List.length(&2, Dr.Verdict, va)) == True{} : Bool}
  for pass: {dir_all_pass(va) == True{} : Bool}
  for room: {Nat.is_lt(List.length(&2, Dr.Layer, List.append(&2, Dr.Layer, a, Dr.Layer{k, 1n+c} <> b)), cap) == True{} : Bool}
  {Dr.tick(cap, Dr.Loop{1n+m, List.append(&2, Dr.Layer, a, Dr.Layer{k, 1n+c} <> b), None{}}, List.append(&2, Dr.Verdict, va, Dr.Stack{p} <> vr)) == Dr.Loop{m, List.append(&2, Dr.Layer, dir_stayers(a, va), p <> Dr.Layer{k, c} <> b), None{}} : Dr.Loop}

# LAW dir_step_push_full (R1, R4): a running loop whose deciding layer has budget and says
# Stack{p}, its whole stack holding cap layers or more, ends failed with
# its steps left: nothing is pushed, the deciding layer's unit is spent;
# the layers above it that said Unstack are gone, the others stay
# EXCLUDES: a push past the cap, a full stack read as a hand back or a
#   continue, a step charged for the failure
law dir_step_push_full:
  for +n: Nat
  for +a: List<&2, Dr.Layer>
  for +k: Nat
  for +c: Nat
  for +b: List<&2, Dr.Layer>
  for +p: Dr.Layer
  for +va: List<&2, Dr.Verdict>
  for +vr: List<&2, Dr.Verdict>
  for +cap: Nat
  for one: {Nat.is_eq(List.length(&2, Dr.Layer, a), List.length(&2, Dr.Verdict, va)) == True{} : Bool}
  for pass: {dir_all_pass(va) == True{} : Bool}
  for full: {Nat.is_lt(List.length(&2, Dr.Layer, List.append(&2, Dr.Layer, a, Dr.Layer{k, 1n+c} <> b)), cap) == False{} : Bool}
  {Dr.tick(cap, Dr.Loop{n, List.append(&2, Dr.Layer, a, Dr.Layer{k, 1n+c} <> b), None{}}, List.append(&2, Dr.Verdict, va, Dr.Stack{p} <> vr)) == Dr.Loop{n, List.append(&2, Dr.Layer, dir_stayers(a, va), Dr.Layer{k, c} <> b), Some{Dr.Failed{}}} : Dr.Loop}

# A reminder leaves only with the continuation it leads

# the verdict v, a Lead read as w
def dir_lead_as(v: Dr.Verdict, +w: Dr.Verdict) -> Dr.Verdict:
  match v:
    case Dr.Defer{}:
      Dr.Defer{}
    case Dr.Again{}:
      Dr.Again{}
    case Dr.Yield{}:
      Dr.Yield{}
    case Dr.Stack{l}:
      Dr.Stack{l}
    case Dr.Unstack{}:
      Dr.Unstack{}
    case Dr.Abort{}:
      Dr.Abort{}
    case Dr.Lead{}:
      w

# the verdicts vs, every Lead read as w
def dir_leads(vs: List<&2, Dr.Verdict>, +w: Dr.Verdict) -> List<&2, Dr.Verdict>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> rest:
      dir_lead_as(v, w) <> dir_leads(rest, w)

# LAW dir_lead_leaves_with_the_continuation (R5): a step that goes on (the
# step where every layer that leads would leave leaves the loop running:
# its end field holds no outcome) is that step: every layer that leads
# leaves
# EXCLUDES: a reminder that stays although the loop goes on (it would
#   lead the next continuation twice), a step that goes on read through
#   the model's own `ended` test (the premise reads the end field)
law dir_lead_leaves_with_the_continuation:
  for +cap: Nat
  for +l: Dr.Loop
  for +vs: List<&2, Dr.Verdict>
  for on: {dir_running(Dr.tick(cap, l, dir_leads(vs, Dr.Unstack{}))) == True{} : Bool}
  {Dr.tick(cap, l, vs) == Dr.tick(cap, l, dir_leads(vs, Dr.Unstack{})) : Dr.Loop}

# LAW dir_lead_stays_when_the_loop_ends (R5): a step that ends the loop
# (the step where every layer that leads would leave leaves an outcome in
# the loop's end field) is the step where every layer that leads stays
# (defers): a reminder never leaves without its continuation
# EXCLUDES: a reminder dropped by a step that hands back or fails (its
#   continuation lost), a step that ends read through the model's own
#   `ended` test (the premise reads the end field)
law dir_lead_stays_when_the_loop_ends:
  for +cap: Nat
  for +l: Dr.Loop
  for +vs: List<&2, Dr.Verdict>
  for ends: {dir_running(Dr.tick(cap, l, dir_leads(vs, Dr.Unstack{}))) == False{} : Bool}
  {Dr.tick(cap, l, vs) == Dr.tick(cap, l, dir_leads(vs, Dr.Defer{})) : Dr.Loop}

# LAW dir_lead_goes_example: anchor: a reminder over a goal with budget leads the goal's
# continuation and leaves with it
law dir_lead_goes_example:
  {Dr.tick(4n, Dr.Loop{3n, [Dr.Layer{2n, 0n}, Dr.Layer{0n, 5n}], None{}}, [Dr.Lead{}, Dr.Again{}]) == Dr.Loop{2n, [Dr.Layer{0n, 4n}], None{}} : Dr.Loop}

# LAW dir_lead_stays_example: anchor: a reminder over a goal that yields stays for the next run
law dir_lead_stays_example:
  {Dr.tick(4n, Dr.Loop{3n, [Dr.Layer{2n, 0n}, Dr.Layer{0n, 5n}], None{}}, [Dr.Lead{}, Dr.Yield{}]) == Dr.Loop{3n, [Dr.Layer{2n, 0n}, Dr.Layer{0n, 5n}], Some{Dr.Hand{}}} : Dr.Loop}

# LAW dir_step_out_of_steps (R5, R7): with no step left, a step that would go on (with one
# step left, every layer that leads reading as Defer, it gives the loop
# 0 steps left, the stack t, still running) ends the loop handed back with
# that stack t: what the step does to the stack stands (a unit spent, a
# layer pushed), and a layer that leads stays
# EXCLUDES: a continue on no step left (the global budget ignored or gone
#   below zero), an out-of-steps end read as a failure, a reminder that
#   leaves without its continuation, a stack rolled back or changed
#   otherwise than the step would change it
law dir_step_out_of_steps:
  for +cap: Nat
  for +s: List<&2, Dr.Layer>
  for +vs: List<&2, Dr.Verdict>
  for +t: List<&2, Dr.Layer>
  for on: {Dr.tick(cap, Dr.Loop{1n, s, None{}}, dir_leads(vs, Dr.Defer{})) == Dr.Loop{0n, t, None{}} : Dr.Loop}
  {Dr.tick(cap, Dr.Loop{0n, s, None{}}, vs) == Dr.Loop{0n, t, Some{Dr.Hand{}}} : Dr.Loop}

# The loop's run
# --------------

# LAW dir_run_step_by_step (R11): a run of no step leaves the loop as it is, and a run of
# the steps xs and then one more step vs is the step vs (Dr.tick) on the
# loop the run of xs leaves: so a run takes its steps one at a time, first
# step first, from the loop it starts from
# EXCLUDES: a run that drops, repeats, reorders or invents steps or
#   verdicts (the run that aborts at once, `run(vss, cap, l) = tick(cap, l,
#   [Abort{}])`, passes dir_loop_ends and dir_loop_stack_bounded), a run
#   that ignores the loop it starts from
law dir_run_step_by_step:
  for +xs: List<&2, List<&2, Dr.Verdict>>
  for +vs: List<&2, Dr.Verdict>
  for +cap: Nat
  for +l: Dr.Loop
  {(Dr.run(Nil{}, cap, l), Dr.run(List.append(&2, List<&2, Dr.Verdict>, xs, [vs]), cap, l)) == (l, Dr.tick(cap, Dr.run(xs, cap, l), vs)) : Dr.Loop & Dr.Loop}

# ---- director_entry ----

# LAWS (S5, the compiled core): the entry bend/ffi_director.bend runs the
# Director stack's step for the Rust code. Each law is an open claim about
# that entry; PROOF.bend proves them (as Director.<law>) with the lemmas of
# proof/director/.

# The entry of the compiled core (bend/ffi_director.bend)
# --------------------------------------------------------
# The Rust code sends one loop step as text and reads the loop after it.
# Every number it sends fits the wire: it saturates the counts (the
# budgets, the global budget, the cap) at the wire's largest Nat, 10^14-1
# (`eukhe_bend::wire::NAT_MAX`), a count no loop runs out of.

# the numbers of a layer fit the wire
def dir_layer_fits(l: Dr.Layer) -> Bool:
  match l:
    case Dr.Layer{k, b}:
      Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(b))

# every item of xs fits the wire
def dir_layers_fit(xs: List<&2, Dr.Layer>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(dir_layer_fits(x), dir_layers_fit(t))

# the numbers of a verdict fit the wire
def dir_verdict_fits(v: Dr.Verdict) -> Bool:
  match v:
    case Dr.Defer{}:
      True{}
    case Dr.Again{}:
      True{}
    case Dr.Yield{}:
      True{}
    case Dr.Stack{l}:
      dir_layer_fits(l)
    case Dr.Unstack{}:
      True{}
    case Dr.Abort{}:
      True{}
    case Dr.Lead{}:
      True{}

# every item of xs fits the wire
def dir_verdicts_fit(xs: List<&2, Dr.Verdict>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(dir_verdict_fits(x), dir_verdicts_fit(t))

# the numbers of a loop fit the wire
def dir_loop_fits(l: Dr.Loop) -> Bool:
  match l:
    case Dr.Loop{n, +s, e}:
      Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Layer, s)), dir_layers_fit(s)))

# the numbers of a request fit the wire
def dir_req_fits(q: FDr.Req) -> Bool:
  match q:
    case FDr.Req{c, l, +vs}:
      Bool.and(LawsBase.wire_fits(c), Bool.and(dir_loop_fits(l), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Verdict, vs)), dir_verdicts_fit(vs))))

# LAW dir_ffi_round_trip: a request that fits reads back whole, and the input after it stays
# EXCLUDES: a layer, a verdict, a budget, the cap or the end lost, swapped
#   or misread on the way to the model
law dir_ffi_round_trip:
  for +q: FDr.Req
  for +rest: String
  for h: {dir_req_fits(q) == True{} : Bool}
  {FDr.get_req(FDr.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FDr.Req>}

# LAW dir_ffi_is_tick: the entry answers one step of the model: the loop after the tick
# EXCLUDES: an entry that decides anything but Dr.tick (a default, a
#   second rule), a reply that encodes another loop
law dir_ffi_is_tick:
  for +c: Nat
  for +l: Dr.Loop
  for +vs: List<&2, Dr.Verdict>
  for h: {dir_req_fits(FDr.Req{c, l, vs}) == True{} : Bool}
  {FDr.ffi(FDr.put_req(FDr.Req{c, l, vs}, "")) == FDr.put_loop(Dr.tick(c, l, vs), "") : String}

# LAW dir_req_fits_example: witness: a request fits (the premise of the laws above can hold)
law dir_req_fits_example:
  {dir_req_fits(FDr.Req{4n, Dr.Loop{3n, [Dr.Layer{0n, 5n}], Some{Dr.Hand{}}}, [Dr.Stack{Dr.Layer{1n, 1n}}, Dr.Lead{}]}) == True{} : Bool}

# The entry, spelled by the grammar Rust writes and reads
# (crates/eukhe-core/src/durable/directors/stack.rs `Loop::tick` and
# `read_loop`), not by the entry's own encoders

# a layer: its kind, then its budget
def dir_spell_layer(l: Dr.Layer, rest: String) -> String:
  match l:
    case Dr.Layer{k, b}:
      Wr.put_nat(k, Wr.put_nat(b, rest))

# the layers of xs, each spelled, then rest
def dir_spell_layers.items(xs: List<&2, Dr.Layer>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      dir_spell_layer(x, dir_spell_layers.items(t, rest))

# a stack (top first): its count, then each layer
def dir_spell_layers(+xs: List<&2, Dr.Layer>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Dr.Layer, xs), dir_spell_layers.items(xs, rest))

# a verdict: Defer 0, Again 1, Yield 2, Stack 3 then the pushed layer,
# Unstack 4, Abort 5, Lead 6
def dir_spell_verdict(v: Dr.Verdict, rest: String) -> String:
  match v:
    case Dr.Defer{}:
      Wr.put_nat(0n, rest)
    case Dr.Again{}:
      Wr.put_nat(1n, rest)
    case Dr.Yield{}:
      Wr.put_nat(2n, rest)
    case Dr.Stack{l}:
      Wr.put_nat(3n, dir_spell_layer(l, rest))
    case Dr.Unstack{}:
      Wr.put_nat(4n, rest)
    case Dr.Abort{}:
      Wr.put_nat(5n, rest)
    case Dr.Lead{}:
      Wr.put_nat(6n, rest)

# the verdicts of xs, each spelled, then rest
def dir_spell_verdicts.items(xs: List<&2, Dr.Verdict>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      dir_spell_verdict(x, dir_spell_verdicts.items(t, rest))

# the verdicts (top first): their count, then each verdict
def dir_spell_verdicts(+xs: List<&2, Dr.Verdict>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Dr.Verdict, xs), dir_spell_verdicts.items(xs, rest))

# an outcome: Cont 0, Hand 1, Failed 2
def dir_spell_out(o: Dr.Out, rest: String) -> String:
  match o:
    case Dr.Cont{}:
      Wr.put_nat(0n, rest)
    case Dr.Hand{}:
      Wr.put_nat(1n, rest)
    case Dr.Failed{}:
      Wr.put_nat(2n, rest)

# how a loop ended: 0 running, 1 then the outcome
def dir_spell_end(m: Maybe<&2, Dr.Out>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{o}:
      Wr.put_nat(1n, dir_spell_out(o, rest))

# a loop: the steps left, the stack, then how it ended
def dir_spell_loop(l: Dr.Loop, rest: String) -> String:
  match l:
    case Dr.Loop{n, s, e}:
      Wr.put_nat(n, dir_spell_layers(s, dir_spell_end(e, rest)))

# a request: the cap, the loop, then the verdicts
def dir_spell_req(q: FDr.Req, rest: String) -> String:
  match q:
    case FDr.Req{c, l, vs}:
      Wr.put_nat(c, dir_spell_loop(l, dir_spell_verdicts(vs, rest)))

# the spelled reply of the model's step on request q: the loop after the
# tick
def dir_spell_answer(q: FDr.Req) -> String:
  match q:
    case FDr.Req{c, l, vs}:
      dir_spell_loop(Dr.tick(c, l, vs), "")

# LAW dir_ffi_answers_spelled: a request spelled by the grammar, every number within the wire,
# is answered with the grammar's spelling of the loop after the model's
# step (Dr.tick of the cap, the loop and the verdicts)
# EXCLUDES: a verdict, outcome or end tag, a field order or a list count
#   that drifts from the grammar Rust reads and writes (swapped on both
#   sides of the entry alike); a field lost, swapped or defaulted
law dir_ffi_answers_spelled:
  for +q: FDr.Req
  for fits: {dir_req_fits(q) == True{} : Bool}
  {FDr.ffi(dir_spell_req(q, "")) == dir_spell_answer(q) : String}

# LAW dir_ffi_ended_stays_any_outcome (R8, R12): a request spelled by the grammar, every
# number within the wire, whose loop has ended with any outcome (end tag
# 1, then outcome 0, 1 or 2), whatever the cap, steps left, stack and
# verdicts, is answered with the grammar's spelling of that same loop,
# unchanged
# EXCLUDES: an entry that revives an ended loop (a continue included) as
#   running, charges a step or a unit, pushes, drops or changes a layer, or
#   spells another outcome
law dir_ffi_ended_stays_any_outcome:
  for +c: Nat
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +o: Dr.Out
  for +vs: List<&2, Dr.Verdict>
  for fits: {dir_req_fits(FDr.Req{c, Dr.Loop{n, s, Some{o}}, vs}) == True{} : Bool}
  {FDr.ffi(dir_spell_req(FDr.Req{c, Dr.Loop{n, s, Some{o}}, vs}, "")) == dir_spell_loop(Dr.Loop{n, s, Some{o}}, "") : String}

# LAW dir_ffi_left_over_spelled: a spelled request that fits, followed by any more input, answers
# the error form "director: input left over"
# EXCLUDES: trailing input ignored, read as part of the request, or
#   answered with the malformed error
law dir_ffi_left_over_spelled:
  for +q: FDr.Req
  for fits: {dir_req_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FDr.ffi(dir_spell_req(q, SCon{c, t})) == Wr.err("director: input left over") : String}

# LAW dir_ffi_unknown_verdict: a spelled cap and loop that fit, then a verdict count that fits
# and spelled verdicts that fit, fewer than the count, then a verdict tag of
# 7 or more (of any length), answer the error form "director: malformed
# request", whatever follows
# EXCLUDES: an unknown verdict tag, at any place of the list, read as a
#   known verdict, skipped, or answered with another error
law dir_ffi_unknown_verdict:
  for +c: Nat
  for +l: Dr.Loop
  for +vs: List<&2, Dr.Verdict>
  for +m: Nat
  for fits: {Bool.and(Bool.and(LawsBase.wire_fits(c), dir_loop_fits(l)), Bool.and(LawsBase.wire_fits(Nat.add(List.length(&2, Dr.Verdict, vs), 1n+m)), dir_verdicts_fit(vs))) == True{} : Bool}
  for +n: Nat
  for +rest: String
  {FDr.ffi(Wr.put_nat(c, dir_spell_loop(l, Wr.put_nat(Nat.add(List.length(&2, Dr.Verdict, vs), 1n+m), dir_spell_verdicts.items(vs, Wr.put_nat(7n+n, rest)))))) == Wr.err("director: malformed request") : String}

# LAW dir_ffi_unknown_end: a spelled cap, steps left and stack that fit, then an end tag of 2 or
# more (of any length), answer the error form "director: malformed
# request", whatever follows
# EXCLUDES: an unknown end tag read as a running or an ended loop
law dir_ffi_unknown_end:
  for +c: Nat
  for +left: Nat
  for +s: List<&2, Dr.Layer>
  for fits: {Bool.and(LawsBase.wire_fits(c), dir_loop_fits(Dr.Loop{left, s, None{}})) == True{} : Bool}
  for +n: Nat
  for +rest: String
  {FDr.ffi(Wr.put_nat(c, Wr.put_nat(left, dir_spell_layers(s, Wr.put_nat(2n+n, rest))))) == Wr.err("director: malformed request") : String}

# LAW dir_ffi_unknown_out: a spelled cap, steps left and stack that fit, an ended loop, then an
# outcome tag of 3 or more (of any length), answer the error form
# "director: malformed request", whatever follows
# EXCLUDES: an unknown outcome read as a continue, a hand back or a failure
law dir_ffi_unknown_out:
  for +c: Nat
  for +left: Nat
  for +s: List<&2, Dr.Layer>
  for fits: {Bool.and(LawsBase.wire_fits(c), dir_loop_fits(Dr.Loop{left, s, None{}})) == True{} : Bool}
  for +n: Nat
  for +rest: String
  {FDr.ffi(Wr.put_nat(c, Wr.put_nat(left, dir_spell_layers(s, Wr.put_nat(1n, Wr.put_nat(3n+n, rest)))))) == Wr.err("director: malformed request") : String}

# LAW dir_ffi_reads_only_requests: an answer that is not the error form answers a request: the
# input is exactly the spelling of a request whose numbers fit the wire,
# and the answer is the spelled loop after the model's step
# EXCLUDES: a decoder that accepts an unknown tag (verdict, end or
#   outcome), a count larger or smaller than its items, a missing or extra
#   field, or input left over, and answers it anyway (a default instead of
#   the error form)
law dir_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FDr.ffi(s)) == False{} : Bool}
  exs q: FDr.Req
  {(s, (dir_req_fits(q), FDr.ffi(s))) == (dir_spell_req(q, ""), (True{}, dir_spell_answer(q))) : String & (Bool & String)}

# LAW dir_ffi_malformed_unless_request: every answer but the error form "director: malformed
# request" comes from an input that begins with a spelled request that fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law dir_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FDr.ffi(s), Wr.err("director: malformed request")) == False{} : Bool}
  exs q: FDr.Req
  exs rest: String
  {(s, dir_req_fits(q)) == (dir_spell_req(q, rest), True{}) : String & Bool}

# LAW dir_ffi_tags_example: anchor: the bytes Rust sends and reads: cap 4, 3 steps left, a
# reminder (kind 1, no budget) over a goal (kind 0, budget 5), running;
# Lead then Again: the reminder leaves with the continuation (2,1,0,4,0,);
# Lead then Yield: the reminder stays, handed back (3,2,1,0,0,5,1,1,);
# cap 1, a Stack with no room fails and costs one unit (3,1,0,4,1,2,); an
# ended loop stays; verdict tag 7, end tag 2 and outcome tag 3 are
# malformed; a request with input left over is refused
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, a stack read bottom first, an unknown tag read as a known one
law dir_ffi_tags_example:
  {[FDr.ffi("4,3,2,1,0,0,5,0,2,6,1,"), FDr.ffi("4,3,2,1,0,0,5,0,2,6,2,"), FDr.ffi("1,3,1,0,5,0,1,3,1,1,"), FDr.ffi("4,3,0,1,2,1,1,"), FDr.ffi("4,3,0,0,1,7,"), FDr.ffi("4,3,0,2,0,"), FDr.ffi("4,3,0,1,3,0,"), FDr.ffi("4,3,0,0,0,x")] == ["2,1,0,4,0,", "3,2,1,0,0,5,1,1,", "3,1,0,4,1,2,", "3,0,1,2,", Wr.err("director: malformed request"), Wr.err("director: malformed request"), Wr.err("director: malformed request"), Wr.err("director: input left over")] : List<&2, String>}
