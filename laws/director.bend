# eukhe: the laws of area director

import Base
import ../bend/director.bend as Dr
import ../bend/ffi_director.bend as FDr
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S5) The Director stack
# -----------------------
# docs/control.md S5, the model in bend/director.bend. Every verdict is
# free: each layer of each step says what the adversary picks.

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

# LAW dir_loop_ends: the loop ends (hands back or fails) after at most n + 1 steps,
# with n its global budget, whatever every layer says: no Director keeps
# the loop going for ever
law dir_loop_ends:
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +vss: List<&2, List<&2, Dr.Verdict>>
  for +cap: Nat
  for long: {List.length(&2, List<&2, Dr.Verdict>, vss) == 1n+n : Nat}
  {Dr.ended(Dr.run(vss, cap, Dr.Loop{n, s, None{}})) == True{} : Bool}

# LAW dir_end_is_final: an ended loop stays as it ended
law dir_end_is_final:
  for +cap: Nat
  for +l: Dr.Loop
  for done: {Dr.ended(l) == True{} : Bool}
  for vs: List<&2, Dr.Verdict>
  {Dr.tick(cap, l, vs) == l : Dr.Loop}

# LAW dir_resume_restores: a resume reads back the stack the tree holds, exactly
law dir_resume_restores:
  for +s: List<&2, Dr.Layer>
  {Dr.decode(Dr.encode(s)) == s : List<&2, Dr.Layer>}

# The rule, verdict by verdict (bend/director.bend `decide.go`): one
# decision of the stack (top first) on the verdicts (top first), with room
# telling whether the whole stack holds fewer than cap layers and stay
# telling whether the loop ends (a layer that leads stays) or goes on (it
# leaves). Together these laws give every decision exactly.

# the decision d with the layer l put back on top of its stack
def dir_on_top(+l: Dr.Layer, d: Dr.Dec) -> Dr.Dec:
  match d:
    case Dr.Dec{o, s}:
      Dr.Dec{o, l <> s}

# LAW dir_go_empty: with no layer left, the loop hands back with an empty stack
law dir_go_empty:
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(Nil{}, vs, room, stay) == Dr.Dec{Dr.Hand{}, Nil{}} : Dr.Dec}

# LAW dir_go_unjudged: a layer with no verdict defers: it stays on top of the decision of
# the layers below, which have no verdict either
law dir_go_unjudged:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(l <> rest, Nil{}, room, stay) == dir_on_top(l, Dr.decide.go(rest, Nil{}, room, stay)) : Dr.Dec}

# LAW dir_go_defer: a Defer stays on top of the decision of the layers below
law dir_go_defer:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(l <> rest, Dr.Defer{} <> vs, room, stay) == dir_on_top(l, Dr.decide.go(rest, vs, room, stay)) : Dr.Dec}

# LAW dir_go_leave: a Leave removes the layer; the layers below decide
law dir_go_leave:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(l <> rest, Dr.Leave{} <> vs, room, stay) == Dr.decide.go(rest, vs, room, stay) : Dr.Dec}

# LAW dir_go_lead_stays: a Lead stays when the loop ends: it stays on top of the decision of
# the layers below
law dir_go_lead_stays:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  {Dr.decide.go(l <> rest, Dr.Lead{} <> vs, room, True{}) == dir_on_top(l, Dr.decide.go(rest, vs, room, True{})) : Dr.Dec}

# LAW dir_go_lead_leaves: a Lead leaves when the loop goes on; the layers below decide
law dir_go_lead_leaves:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  {Dr.decide.go(l <> rest, Dr.Lead{} <> vs, room, False{}) == Dr.decide.go(rest, vs, room, False{}) : Dr.Dec}

# LAW dir_go_yield: a Yield hands back; the stack stays as it is
law dir_go_yield:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(l <> rest, Dr.Yield{} <> vs, room, stay) == Dr.Dec{Dr.Hand{}, l <> rest} : Dr.Dec}

# LAW dir_go_abort: an Abort fails; the stack stays as it is
law dir_go_abort:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(l <> rest, Dr.Abort{} <> vs, room, stay) == Dr.Dec{Dr.Failed{}, l <> rest} : Dr.Dec}

# LAW dir_go_again: an Again with budget goes on and costs the layer one unit
law dir_go_again:
  for +k: Nat
  for +b: Nat
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(Dr.Layer{k, 1n+b} <> rest, Dr.Again{} <> vs, room, stay) == Dr.Dec{Dr.Cont{}, Dr.Layer{k, b} <> rest} : Dr.Dec}

# LAW dir_go_again_spent: an Again with no budget left hands back; the stack stays
law dir_go_again_spent:
  for +k: Nat
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(Dr.Layer{k, 0n} <> rest, Dr.Again{} <> vs, room, stay) == Dr.Dec{Dr.Hand{}, Dr.Layer{k, 0n} <> rest} : Dr.Dec}

# LAW dir_go_push: a Stack with budget and room puts the new layer on top, goes on,
# and costs the layer one unit
law dir_go_push:
  for +k: Nat
  for +b: Nat
  for +n: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +stay: Bool
  {Dr.decide.go(Dr.Layer{k, 1n+b} <> rest, Dr.Stack{n} <> vs, True{}, stay) == Dr.Dec{Dr.Cont{}, n <> Dr.Layer{k, b} <> rest} : Dr.Dec}

# LAW dir_go_push_full: a Stack with budget and no room fails; it still costs the layer
# one unit, and the layers above the deciding one are gone
law dir_go_push_full:
  for +k: Nat
  for +b: Nat
  for +n: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +stay: Bool
  {Dr.decide.go(Dr.Layer{k, 1n+b} <> rest, Dr.Stack{n} <> vs, False{}, stay) == Dr.Dec{Dr.Failed{}, Dr.Layer{k, b} <> rest} : Dr.Dec}

# LAW dir_go_push_spent: a Stack with no budget left hands back; nothing is pushed
law dir_go_push_spent:
  for +k: Nat
  for +n: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(Dr.Layer{k, 0n} <> rest, Dr.Stack{n} <> vs, room, stay) == Dr.Dec{Dr.Hand{}, Dr.Layer{k, 0n} <> rest} : Dr.Dec}

# LAW dir_room: the room of a decision: the whole stack (every layer, those above
# the deciding one too) holds fewer than cap layers. A cap the Rust code
# saturates (at the wire's largest Nat) leaves room for every stack.
law dir_room:
  for +s: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +cap: Nat
  for +stay: Bool
  {Dr.decide.as(s, vs, cap, stay) == Dr.decide.go(s, vs, Nat.is_lt(List.length(&2, Dr.Layer, s), cap), stay) : Dr.Dec}

# LAW dir_decide_goes_on: a decision of the loop is the one where a layer that leads leaves
law dir_decide_goes_on:
  for +s: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +cap: Nat
  {Dr.decide(s, vs, cap) == Dr.decide.as(s, vs, cap, False{}) : Dr.Dec}

# The loop, step by step (with dir_end_is_final, every tick exactly)

# LAW dir_tick_goes_on: a continue with a step left goes on, one step fewer, with the
# decision's stack (a layer that leads left with it)
law dir_tick_goes_on:
  for +cap: Nat
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +vs: List<&2, Dr.Verdict>
  for +t: List<&2, Dr.Layer>
  for go: {Dr.decide(s, vs, cap) == Dr.Dec{Dr.Cont{}, t} : Dr.Dec}
  {Dr.tick(cap, Dr.Loop{1n+n, s, None{}}, vs) == Dr.Loop{n, t, None{}} : Dr.Loop}

# LAW dir_tick_out_of_steps: a continue with no step left yields; a layer that leads stays
law dir_tick_out_of_steps:
  for +cap: Nat
  for +s: List<&2, Dr.Layer>
  for +vs: List<&2, Dr.Verdict>
  for go: {Dr.Dec.out(Dr.decide(s, vs, cap)) == Dr.Cont{} : Dr.Out}
  {Dr.tick(cap, Dr.Loop{0n, s, None{}}, vs) == Dr.Loop{0n, Dr.Dec.stack(Dr.decide.as(s, vs, cap, True{})), Some{Dr.Hand{}}} : Dr.Loop}

# LAW dir_tick_hands_back: a hand back ends the loop with its steps left; a layer that leads
# stays
law dir_tick_hands_back:
  for +cap: Nat
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +vs: List<&2, Dr.Verdict>
  for h: {Dr.Dec.out(Dr.decide(s, vs, cap)) == Dr.Hand{} : Dr.Out}
  {Dr.tick(cap, Dr.Loop{n, s, None{}}, vs) == Dr.Loop{n, Dr.Dec.stack(Dr.decide.as(s, vs, cap, True{})), Some{Dr.Hand{}}} : Dr.Loop}

# LAW dir_tick_fails: a failure ends the loop with its steps left; a layer that leads
# stays
law dir_tick_fails:
  for +cap: Nat
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +vs: List<&2, Dr.Verdict>
  for f: {Dr.Dec.out(Dr.decide(s, vs, cap)) == Dr.Failed{} : Dr.Out}
  {Dr.tick(cap, Dr.Loop{n, s, None{}}, vs) == Dr.Loop{n, Dr.Dec.stack(Dr.decide.as(s, vs, cap, True{})), Some{Dr.Failed{}}} : Dr.Loop}

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
    case Dr.Leave{}:
      Dr.Leave{}
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

# LAW dir_lead_leaves_with_the_continuation: a step that goes on is the step where every layer that leads
# leaves
law dir_lead_leaves_with_the_continuation:
  for +cap: Nat
  for +l: Dr.Loop
  for +vs: List<&2, Dr.Verdict>
  for on: {Dr.ended(Dr.tick(cap, l, dir_leads(vs, Dr.Leave{}))) == False{} : Bool}
  {Dr.tick(cap, l, vs) == Dr.tick(cap, l, dir_leads(vs, Dr.Leave{})) : Dr.Loop}

# LAW dir_lead_stays_when_the_loop_ends: a step that ends the loop is the step where every layer that leads
# stays (defers): a reminder never leaves without its continuation
law dir_lead_stays_when_the_loop_ends:
  for +cap: Nat
  for +l: Dr.Loop
  for +vs: List<&2, Dr.Verdict>
  for ends: {Dr.ended(Dr.tick(cap, l, dir_leads(vs, Dr.Leave{}))) == True{} : Bool}
  {Dr.tick(cap, l, vs) == Dr.tick(cap, l, dir_leads(vs, Dr.Defer{})) : Dr.Loop}

# LAW dir_lead_goes_example: anchor: a reminder over a goal with budget leads the goal's
# continuation and leaves with it
law dir_lead_goes_example:
  {Dr.tick(4n, Dr.Loop{3n, [Dr.Layer{2n, 0n}, Dr.Layer{0n, 5n}], None{}}, [Dr.Lead{}, Dr.Again{}]) == Dr.Loop{2n, [Dr.Layer{0n, 4n}], None{}} : Dr.Loop}

# LAW dir_lead_stays_example: anchor: a reminder over a goal that yields stays for the next run
law dir_lead_stays_example:
  {Dr.tick(4n, Dr.Loop{3n, [Dr.Layer{2n, 0n}, Dr.Layer{0n, 5n}], None{}}, [Dr.Lead{}, Dr.Yield{}]) == Dr.Loop{3n, [Dr.Layer{2n, 0n}, Dr.Layer{0n, 5n}], Some{Dr.Hand{}}} : Dr.Loop}

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
    case Dr.Leave{}:
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

# LAW dir_ffi_malformed: a malformed request answers the error form, never a loop
# EXCLUDES: a default loop for input the decoder refuses
law dir_ffi_malformed:
  for +s: String
  for h: {FDr.get_req(s) == Wr.Bad{} : Wr.Dec<FDr.Req>}
  {FDr.ffi(s) == Wr.err("director: malformed request") : String}

# LAW dir_ffi_left_over: a request with input left over answers the error form
# EXCLUDES: a reply to a request followed by anything (a second request
#   glued on, a truncated encoding read as a shorter one)
law dir_ffi_left_over:
  for +s: String
  for +q: FDr.Req
  for +r: String
  for h: {FDr.get_req(s) == Wr.Got{q, r} : Wr.Dec<FDr.Req>}
  for e: {String.is_empty(r) == False{} : Bool}
  {FDr.ffi(s) == Wr.err("director: input left over") : String}

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
# Leave 4, Abort 5, Lead 6
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
    case Dr.Leave{}:
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
