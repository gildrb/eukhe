# eukhe: the laws of area director

import Base
import ../bend/director.bend as Dr
import ../bend/ffi_director.bend as FDr
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S5) The Director stack
# -----------------------
# the model in bend/director.bend. Every verdict is
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

# The entry, independently of bend/ffi_director.bend and of the model's
# functions: a reader of the request grammar (the header of
# bend/ffi_director.bend, crates/eukhe-bend/WIRE.md) built from the wire
# primitives, the loop step as the laws above state it, and a speller of
# the loop after it from the wire primitives.

# a layer: its kind, then its budget
def dirr.layer.b(k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Dr.Layer>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{Dr.Layer{k, b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def dirr.layer.k(r: Wr.Dec<Nat>) -> Wr.Dec<Dr.Layer>:
  match r:
    case Wr.Got{k, s}:
      dirr.layer.b(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def dirr.layer(s: String) -> Wr.Dec<Dr.Layer>:
  dirr.layer.k(Wr.get_nat(s))

# a verdict: 0 Defer | 1 Again | 2 Yield | 3 Stack, then a layer | 4 Leave
# | 5 Abort | 6 Lead
def dirr.verdict.stack(r: Wr.Dec<Dr.Layer>) -> Wr.Dec<Dr.Verdict>:
  match r:
    case Wr.Got{l, s}:
      Wr.Got{Dr.Stack{l}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def dirr.verdict.tag(t: Nat, s: String) -> Wr.Dec<Dr.Verdict>:
  match t:
    case 0n:
      Wr.Got{Dr.Defer{}, s}
    case 1n:
      Wr.Got{Dr.Again{}, s}
    case 2n:
      Wr.Got{Dr.Yield{}, s}
    case 3n:
      dirr.verdict.stack(dirr.layer(s))
    case 4n:
      Wr.Got{Dr.Leave{}, s}
    case 5n:
      Wr.Got{Dr.Abort{}, s}
    case 6n:
      Wr.Got{Dr.Lead{}, s}
    case 7n+x:
      Wr.Bad{}

def dirr.verdict.go(r: Wr.Dec<Nat>) -> Wr.Dec<Dr.Verdict>:
  match r:
    case Wr.Got{t, s}:
      dirr.verdict.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def dirr.verdict(s: String) -> Wr.Dec<Dr.Verdict>:
  dirr.verdict.go(Wr.get_nat(s))

# how a loop ended: 0 (running) | 1, then 0 Cont | 1 Hand | 2 Failed
def dirr.end.out(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Dr.Out>>:
  match t:
    case 0n:
      Wr.Got{Some{Dr.Cont{}}, s}
    case 1n:
      Wr.Got{Some{Dr.Hand{}}, s}
    case 2n:
      Wr.Got{Some{Dr.Failed{}}, s}
    case 3n+x:
      Wr.Bad{}

def dirr.end.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Dr.Out>>:
  match r:
    case Wr.Got{t, s}:
      dirr.end.out(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def dirr.end.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Dr.Out>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      dirr.end.some(Wr.get_nat(s))
    case 2n+x:
      Wr.Bad{}

def dirr.end(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Dr.Out>>:
  match r:
    case Wr.Got{t, s}:
      dirr.end.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a loop: the global budget left, the stack (a list of layers, top
# first), how it ended
def dirr.loop.end(n: Nat, st: List<&2, Dr.Layer>, r: Wr.Dec<Maybe<&2, Dr.Out>>) -> Wr.Dec<Dr.Loop>:
  match r:
    case Wr.Got{e, s}:
      Wr.Got{Dr.Loop{n, st, e}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def dirr.loop.stack(n: Nat, r: Wr.Dec<List<&2, Dr.Layer>>) -> Wr.Dec<Dr.Loop>:
  match r:
    case Wr.Got{st, s}:
      dirr.loop.end(n, st, dirr.end(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def dirr.loop(r: Wr.Dec<Nat>) -> Wr.Dec<Dr.Loop>:
  match r:
    case Wr.Got{n, s}:
      dirr.loop.stack(n, Wr.get_list(~Dr.Layer, ~dirr.layer, s))
    case Wr.Bad{}:
      Wr.Bad{}

# a request: the cap, the loop, the verdicts (a list, top first)
def dirr.req.vs(c: Nat, l: Dr.Loop, r: Wr.Dec<List<&2, Dr.Verdict>>) -> Wr.Dec<FDr.Req>:
  match r:
    case Wr.Got{vs, s}:
      Wr.Got{FDr.Req{c, l, vs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def dirr.req.loop(c: Nat, r: Wr.Dec<Dr.Loop>) -> Wr.Dec<FDr.Req>:
  match r:
    case Wr.Got{l, s}:
      dirr.req.vs(c, l, Wr.get_list(~Dr.Verdict, ~dirr.verdict, s))
    case Wr.Bad{}:
      Wr.Bad{}

def dirr.req(r: Wr.Dec<Nat>) -> Wr.Dec<FDr.Req>:
  match r:
    case Wr.Got{c, s}:
      dirr.req.loop(c, dirr.loop(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with, and what follows it
def dirr.read(s: String) -> Wr.Dec<FDr.Req>:
  dirr.req(Wr.get_nat(s))

# an Again of l above the layers rest (dir_go_again, dir_go_again_spent)
def dirs.again(l: Dr.Layer, +rest: List<&2, Dr.Layer>) -> Dr.Dec:
  match l:
    case Dr.Layer{k, b}:
      match b:
        case 0n:
          Dr.Dec{Dr.Hand{}, Dr.Layer{k, 0n} <> rest}
        case 1n+c:
          Dr.Dec{Dr.Cont{}, Dr.Layer{k, c} <> rest}

# a Stack of n by l above the layers rest, room telling whether the whole
# stack holds fewer than cap layers (dir_go_push, dir_go_push_full,
# dir_go_push_spent)
def dirs.push(l: Dr.Layer, +n: Dr.Layer, +rest: List<&2, Dr.Layer>, room: Bool) -> Dr.Dec:
  match l:
    case Dr.Layer{k, b}:
      match b:
        case 0n:
          Dr.Dec{Dr.Hand{}, Dr.Layer{k, 0n} <> rest}
        case 1n+c:
          match room:
            case True{}:
              Dr.Dec{Dr.Cont{}, n <> Dr.Layer{k, c} <> rest}
            case False{}:
              Dr.Dec{Dr.Failed{}, Dr.Layer{k, c} <> rest}

# a Lead of l over the decision d of the layers below: on top when the
# loop ends (stay), gone when it goes on (dir_go_lead_stays,
# dir_go_lead_leaves)
def dirs.lead(stay: Bool, +l: Dr.Layer, d: Dr.Dec) -> Dr.Dec:
  match stay:
    case True{}:
      dir_on_top(l, d)
    case False{}:
      d

# one decision, verdict by verdict, as the laws dir_go_* state it
def dirs.go(s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +room: Bool, +stay: Bool) -> Dr.Dec:
  match s:
    case Nil{}:
      Dr.Dec{Dr.Hand{}, Nil{}}
    case +l <> +rest:
      match vs:
        case Nil{}:
          dir_on_top(l, dirs.go(rest, Nil{}, room, stay))
        case v <> vr:
          match v:
            case Dr.Defer{}:
              dir_on_top(l, dirs.go(rest, vr, room, stay))
            case Dr.Again{}:
              dirs.again(l, rest)
            case Dr.Yield{}:
              Dr.Dec{Dr.Hand{}, l <> rest}
            case Dr.Stack{n}:
              dirs.push(l, n, rest, room)
            case Dr.Leave{}:
              dirs.go(rest, vr, room, stay)
            case Dr.Abort{}:
              Dr.Dec{Dr.Failed{}, l <> rest}
            case Dr.Lead{}:
              dirs.lead(stay, l, dirs.go(rest, vr, room, stay))

# a decision with room for cap layers (dir_room): a push needs the whole
# stack to hold fewer than cap layers
def dirs.decide(+s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat, +stay: Bool) -> Dr.Dec:
  dirs.go(s, vs, Nat.is_lt(List.length(&2, Dr.Layer, s), cap), stay)

def dirs.stack(d: Dr.Dec) -> List<&2, Dr.Layer>:
  match d:
    case Dr.Dec{o, t}:
      t

# a continue with n steps left: with a step left the loop goes on with the
# decision's stack t (dir_tick_goes_on); with none it yields, a layer that
# leads staying (dir_tick_out_of_steps)
def dirs.on(n: Nat, t: List<&2, Dr.Layer>, +s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat) -> Dr.Loop:
  match n:
    case 0n:
      Dr.Loop{0n, dirs.stack(dirs.decide(s, vs, cap, True{})), Some{Dr.Hand{}}}
    case 1n+m:
      Dr.Loop{m, t, None{}}

# the loop after the decision d of the stack s on vs (made as the loop
# goes on, dir_decide_goes_on), with n steps left: dirs.on, then
# dir_tick_hands_back, dir_tick_fails
def dirs.settle(d: Dr.Dec, +n: Nat, +s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat) -> Dr.Loop:
  match d:
    case Dr.Dec{o, t}:
      match o:
        case Dr.Cont{}:
          dirs.on(n, t, s, vs, cap)
        case Dr.Hand{}:
          Dr.Loop{n, dirs.stack(dirs.decide(s, vs, cap, True{})), Some{Dr.Hand{}}}
        case Dr.Failed{}:
          Dr.Loop{n, dirs.stack(dirs.decide(s, vs, cap, True{})), Some{Dr.Failed{}}}

# one loop step: an ended loop stays as it ended (dir_end_is_final); a
# running one settles the decision of its stack
def dirs.tick(+cap: Nat, l: Dr.Loop, vs: List<&2, Dr.Verdict>) -> Dr.Loop:
  match l:
    case Dr.Loop{n, +s, e}:
      match e:
        case Some{x}:
          Dr.Loop{n, s, Some{x}}
        case None{}:
          +w = vs
          dirs.settle(dirs.decide(s, w, cap, False{}), n, s, w, cap)

# the loop after the step, as the Rust Reader reads it: the budget left,
# the stack (each layer its kind, then its budget), the end (0 | 1, then
# 0 Cont | 1 Hand | 2 Failed)
def dirs.layer(l: Dr.Layer, rest: String) -> String:
  match l:
    case Dr.Layer{k, b}:
      Wr.put_nat(k, Wr.put_nat(b, rest))

def dirs.end(e: Maybe<&2, Dr.Out>, rest: String) -> String:
  match e:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{o}:
      match o:
        case Dr.Cont{}:
          Wr.put_nat(1n, Wr.put_nat(0n, rest))
        case Dr.Hand{}:
          Wr.put_nat(1n, Wr.put_nat(1n, rest))
        case Dr.Failed{}:
          Wr.put_nat(1n, Wr.put_nat(2n, rest))

def dirs.loop(l: Dr.Loop, rest: String) -> String:
  match l:
    case Dr.Loop{n, st, e}:
      Wr.put_nat(n, Wr.put_list(~Dr.Layer, ~dirs.layer, st, dirs.end(e, rest)))

def dirs.whole(done: Bool, q: FDr.Req) -> String:
  match done:
    case True{}:
      match q:
        case FDr.Req{c, l, vs}:
          dirs.loop(dirs.tick(c, l, vs), "")
    case False{}:
      Wr.err("director: input left over")

def dirs.run(r: Wr.Dec<FDr.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      dirs.whole(Wr.end(s), q)
    case Wr.Bad{}:
      Wr.err("director: malformed request")

# the reply to the input s
def dirs.spec(s: String) -> String:
  dirs.run(dirr.read(s))

# LAW dir_ffi_exact: on every input the entry answers the loop after one step (as the laws above state the step: an ended loop stays; a running one settles its stack's decision, verdict by verdict) of the request the input starts with, spelled as the Rust Reader reads it, when nothing follows the request; "director: input left over" when something does; "director: malformed request" when the input starts with no request
# EXCLUDES: a step other than the laws' (a verdict misread, an ended loop
#   stepped, a cap or a budget off by one), a reply in another spelling, a
#   loop answered for an input that is no request (an unknown tag, a list
#   cut short, a 15-digit number) or for a request with input left over,
#   another error text
law dir_ffi_exact:
  for +s: String
  {FDr.ffi(s) == dirs.spec(s) : String}
