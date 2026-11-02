# eukhe: the laws of area infer

import Base
import ../bend/effort.bend as Ef
import ../bend/facts.bend as Fx
import ../bend/ffi_infer.bend as FIn
import ../bend/infer.bend as If
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S6) The inference layer
# ------------------------
# the model in bend/infer.bend. Every input is free:
# any rulebook, query and directive; any replies of the model; any
# provider support; any tools; any stream; any context sizes.

# LAW quirk_unknown_rejected: a rulebook with a rule of an unknown directive does not compile
law quirk_unknown_rejected:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +r: If.Rule
  for +post: List<&2, If.Rule>
  for bad: {If.elem(known, If.Rule.dir(r)) == False{} : Bool}
  {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == False{} : Bool}

# LAW quirk_clash_rejected: a rulebook with two rules of one layer, target and directive and
# different values does not compile: precedence is never ambiguous
law quirk_clash_rejected:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +a: If.Rule
  for +mid: List<&2, If.Rule>
  for +b: If.Rule
  for +post: List<&2, If.Rule>
  for both: {If.clash(a, b) == True{} : Bool}
  {If.compiles(known, List.append(&2, If.Rule, pre, a <> List.append(&2, If.Rule, mid, b <> post))) == False{} : Bool}

# LAW quirk_unknown_when_none: with no rule that applies, the answer is Unknown, never a guess
law quirk_unknown_when_none:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for none: {If.any_at(rs, q, d, 0n) == False{} : Bool}
  {If.lookup(rs, q, d) == If.Unknown{} : If.Ans}

# LAW quirk_known_when_some: a rule that applies always gives an answer
law quirk_known_when_some:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for some: {If.any_at(rs, q, d, 0n) == True{} : Bool}
  {If.is_known(If.lookup(rs, q, d)) == True{} : Bool}

# LAW quirk_highest_wins: in a rulebook that compiles, a rule of the highest layer that
# applies gives the answer: host over model over family
law quirk_highest_wins:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +r: If.Rule
  for +post: List<&2, If.Rule>
  for +q: If.Query
  for ok: {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == True{} : Bool}
  for hit: {If.applies(q, r) == True{} : Bool}
  for top: {If.any_at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), 1n+If.Rule.rank(r)) == False{} : Bool}
  {If.lookup(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r)) == If.Known{If.Rule.val(r)} : If.Ans}

# LAW quirk_order_free: in a rulebook that compiles, the order of two rules changes no
# answer
law quirk_order_free:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +a: If.Rule
  for +b: If.Rule
  for +post: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for ok: {If.compiles(known, List.append(&2, If.Rule, pre, a <> b <> post)) == True{} : Bool}
  {If.lookup(List.append(&2, If.Rule, pre, b <> a <> post), q, d) == If.lookup(List.append(&2, If.Rule, pre, a <> b <> post), q, d) : If.Ans}

# LAW quirk_compile_order_free: the order of two rules changes nothing about whether the rulebook
# compiles
law quirk_compile_order_free:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +a: If.Rule
  for +b: If.Rule
  for +post: List<&2, If.Rule>
  {If.compiles(known, List.append(&2, If.Rule, pre, b <> a <> post)) == If.compiles(known, List.append(&2, If.Rule, pre, a <> b <> post)) : Bool}

# LAW force_bounded: a forced call makes at most 1 + r attempts
law force_bounded:
  for +r: Nat
  for +replies: List<&2, Bool>
  for +sup: Bool
  for +free: Bool
  {Nat.is_le(List.length(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))), 1n+r) == True{} : Bool}

# LAW force_first_flag: the first attempt sets the native flag only when it is supported
# and free
law force_first_flag:
  for +r: Nat
  for +replies: List<&2, Bool>
  for +sup: Bool
  for +free: Bool
  {List.head(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))) == Some{If.Try{Bool.and(sup, free)}} : Maybe<&2, If.Try>}

# LAW force_retry_flag: every retry escalates to the native flag when it is supported
law force_retry_flag:
  for +r: Nat
  for +replies: List<&2, Bool>
  for +sup: Bool
  for +free: Bool
  {If.flags(List.drop(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free)), 1n), sup) == True{} : Bool}

# LAW force_reports: a forced call reports a call exactly when the model called the
# tool within its attempts; otherwise it reports the failure
law force_reports:
  for +r: Nat
  for +replies: List<&2, Bool>
  for +sup: Bool
  for +free: Bool
  {If.Forced.called(Pair.snd(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))) == If.called_within(1n+r, replies) : Bool}

# LAW strict_within_cap: at most cap tools get strict schemas
law strict_within_cap:
  for +cap: Nat
  for +ts: List<&2, If.Tool>
  {Nat.is_le(List.length(&2, If.Tool, Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts))), cap) == True{} : Bool}

# LAW strict_keeps_every_tool: no tool is lost: every tool is strict or loose, as many times as
# it was given
law strict_keeps_every_tool:
  for +cap: Nat
  for +ts: List<&2, If.Tool>
  for +i: Nat
  {Nat.add(If.count(Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), i), If.count(Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), i)) == If.count(ts, i) : Nat}

# LAW strict_by_priority: every strict tool has a priority of at least every loose tool
law strict_by_priority:
  for +cap: Nat
  for +ts: List<&2, If.Tool>
  {If.dominates(Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts))) == True{} : Bool}

# LAW strict_no_cap: with no cap every tool keeps its strict schema
law strict_no_cap:
  for +ts: List<&2, If.Tool>
  {If.strict.of(None{}, ts) == (ts, []) : List<&2, If.Tool> & List<&2, If.Tool>}

# LAW strict_cap_is_strict: a request's cap splits the tools as strict does, so
# strict_within_cap, strict_keeps_every_tool and strict_by_priority hold
# for every request
law strict_cap_is_strict:
  for +c: Nat
  for +ts: List<&2, If.Tool>
  {If.strict.of(Some{c}, ts) == If.strict(c, ts) : List<&2, If.Tool> & List<&2, If.Tool>}

# the ids of the tools of ts, in order
def strict.ids(ts: List<&2, If.Tool>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      If.Tool.id(t) <> strict.ids(rest)

# LAW plan_fits_lists_the_loose: a plan that fits lists exactly the loose tools of the request
law plan_fits_lists_the_loose:
  for cap: Maybe<&2, Nat>
  for +ts: List<&2, If.Tool>
  for +need: List<&2, Nat>
  for +ls: List<&2, Nat>
  for f: {If.plan(cap, ts, need) == If.Fits{ls} : If.Plan}
  {ls == strict.ids(Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict.of(cap, ts))) : List<&2, Nat>}

# LAW plan_never_loosens_a_needed_tool: a tool that requires a strict schema is never sent loose
# EXCLUDES: a request that drops the schema a tool requires
law plan_never_loosens_a_needed_tool:
  for cap: Maybe<&2, Nat>
  for +ts: List<&2, If.Tool>
  for +need: List<&2, Nat>
  for +ls: List<&2, Nat>
  for +i: Nat
  for +f: {If.plan(cap, ts, need) == If.Fits{ls} : If.Plan}
  for +n: {If.elem(need, i) == True{} : Bool}
  {If.elem(ls, i) == False{} : Bool}

# LAW plan_refusal_names_a_needed_loose_tool: a refusal names a tool that requires a strict schema and is past
# the cap; EXCLUDES: refusing a request that fits
# LEAVES FREE: which such tool it names when there are several (the
# model names the first loose one, highest priority first)
law plan_refusal_names_a_needed_loose_tool:
  for cap: Maybe<&2, Nat>
  for +ts: List<&2, If.Tool>
  for +need: List<&2, Nat>
  for +i: Nat
  for o: {If.plan(cap, ts, need) == If.Over{i} : If.Plan}
  {Bool.and(If.elem(need, i), If.elem(strict.ids(Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict.of(cap, ts))), i)) == True{} : Bool}

# LAW plan_example_over: a required tool past the cap refuses the request (witness of the
# refusal)
law plan_example_over:
  {If.plan(Some{1n}, [If.Tool{0n, 1n}, If.Tool{1n, 3n}, If.Tool{2n, 2n}], [0n, 2n]) == If.Over{2n} : If.Plan}

# LAW plan_example_fits: a required tool within the cap fits (witness of a fit)
law plan_example_fits:
  {If.plan(Some{1n}, [If.Tool{0n, 1n}, If.Tool{1n, 3n}, If.Tool{2n, 3n}], [1n]) == If.Fits{[2n, 0n]} : If.Plan}

# LAW guard_cuts_repeats: a stream that repeats a chunk k times in a row is cut
law guard_cuts_repeats:
  for +xs: List<&2, Nat>
  for +k: Nat
  for rep: {If.repeats(xs, k) == True{} : Bool}
  {If.Cut.cut(If.guard(xs, k)) == True{} : Bool}

# LAW guard_cuts_loops: a stream with a window of k chunks that is periodic, with a period
# of at most k/4 (at least 1), is cut
law guard_cuts_loops:
  for +xs: List<&2, Nat>
  for +k: Nat
  for lp: {If.loops(xs, k) == True{} : Bool}
  {If.Cut.cut(If.guard(xs, k)) == True{} : Bool}

# LAW guard_keeps_others: a stream with no window of k chunks that is periodic, with a
# period of at most k/4 (at least 1), is not cut
law guard_keeps_others:
  for +xs: List<&2, Nat>
  for +k: Nat
  for calm: {If.loops(xs, k) == False{} : Bool}
  {If.guard(xs, k) == If.Whole{} : If.Cut}

# LAW compact_starts_early: when each turn grows the context by at most m, compaction (at the
# threshold limit - m) starts at a turn before any turn over the limit
law compact_starts_early:
  for +xs: List<&2, Nat>
  for +m: Nat
  for +lim: Nat
  for small: {Nat.is_le(m, lim) == True{} : Bool}
  for steps: {If.steps_le(xs, m, 0n) == True{} : Bool}
  {If.m.lt(If.first_at(xs, Nat.sub(lim, m), 0n), If.first_at(xs, 1n+lim, 0n)) == True{} : Bool}

# ---- ladder ----

# LAWS (S6.9): the thinking ladder of a model is rulebook data. Each law
# is an open claim about the model in bend/infer.bend section 6;
# PROOF.bend proves them (as Infer.<law>) with the lemmas of
# proof/infer/.

# (S6.9) The thinking ladder
# --------------------------
# the model in
# bend/infer.bend section 6. Every input is free: any explicit map, any
# rulebook ladder, any default ladders, any level.

# LAW quirk_ladder_explicit_first: a model's explicit thinking-level map is its chosen ladder, over
# any ladder of the rulebook
law quirk_ladder_explicit_first:
  for +e: Ef.LvMap
  for +rule: Maybe<&2, Ef.LvMap>
  {If.lad.chosen(Some{e}, rule) == e : Ef.LvMap}

# LAW quirk_ladder_rule_second: with no explicit map, the rulebook's ladder is the chosen ladder
law quirk_ladder_rule_second:
  for +l: Ef.LvMap
  {If.lad.chosen(None{}, Some{l}) == l : Ef.LvMap}

# LAW quirk_ladder_default_last: with no explicit map and no rulebook ladder, the chosen ladder has
# no entry: the default ladder gives every level
law quirk_ladder_default_last:
  {If.lad.chosen(None{}, None{}) == Ef.LvMap.none() : Ef.LvMap}

# LAW quirk_ladder_shipped_is_s10: with the shipped default ladders, the levels a model offers are the
# S10 ladder of its chosen map, so every law of S10 holds for them
law quirk_ladder_shipped_is_s10:
  for r: Bool
  for +map: Ef.LvMap
  {If.lad.offered.of(r, map, If.lad.shipped()) == Ef.offered(Ef.Mdl{r, map}) : List<&2, Ef.Lv>}

# the entry is a wire string
def ladder.is_wire(e: Ef.Ent) -> Bool:
  match e:
    case Ef.Missing{}:
      False{}
    case Ef.Null{}:
      False{}
    case Ef.Wire{}:
      True{}

# some level of ls has a wire entry in m
def ladder.wired.go(ls: List<&2, Ef.Lv>, +m: Ef.LvMap) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case l <> rest:
      Bool.or(ladder.is_wire(Ef.entry(l, m)), ladder.wired.go(rest, m))

# an explicit map gives some level a wire string
def ladder.wired(explicit: Maybe<&2, Ef.LvMap>) -> Bool:
  match explicit:
    case Some{+m}:
      ladder.wired.go(Ef.ladder(), m)
    case None{}:
      False{}

# LAW quirk_ladder_reasons: a model reasons when its flag says so and, for a registry model
# (by_map, #2858), when its explicit map gives some level a wire string;
# no other input makes a model reason
law quirk_ladder_reasons:
  for f: Bool
  for bm: Bool
  for +explicit: Maybe<&2, Ef.LvMap>
  {If.lad.reasons(f, bm, explicit) == Bool.or(f, Bool.and(bm, ladder.wired(explicit))) : Bool}

# (infer) The strict plan: bend/ffi_infer.bend
# --------------------------------------------

def core_tool_fits(t: If.Tool) -> Bool:
  match t:
    case If.Tool{i, p}:
      Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(p))

def core_tools_fit(ts: List<&2, If.Tool>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, u}:
      Bool.and(core_tool_fits(t), core_tools_fit(u))

def core_infer_fits(q: FIn.Req) -> Bool:
  match q:
    case FIn.Req{cap, +ts, +need}:
      Bool.and(LawsBase.core_mfits(cap), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, If.Tool, ts)), core_tools_fit(ts)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, need)), LawsBase.wire_nats_fit(need))))

# LAW core_infer_round_trip (R1): a strict plan request that fits reads back, and the rest is
# untouched
# EXCLUDES: the cap read as none or the reverse, a tool's id and priority
#   swapped, tools or needed ids lost, added or reordered
law core_infer_round_trip:
  for +q: FIn.Req
  for rest: String
  for h: {core_infer_fits(q) == True{} : Bool}
  {FIn.get_req(FIn.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FIn.Req>}

# LAW core_infer_answers (R2): the entry answers the model's strict plan of the request
# EXCLUDES: a plan of other tools or another cap, a refusal for a request
#   that fits, a plan that ignores the needed tools
law core_infer_answers:
  for +cap: Maybe<&2, Nat>
  for +ts: List<&2, If.Tool>
  for +need: List<&2, Nat>
  for h: {core_infer_fits(FIn.Req{cap, ts, need}) == True{} : Bool}
  {FIn.ffi(FIn.put_req(FIn.Req{cap, ts, need}, "")) == FIn.put_plan(If.plan(cap, ts, need), "") : String}

# LAW core_infer_malformed (R3): a malformed strict plan request answers the error form
# EXCLUDES: a default plan (every tool strict, or none) for a request it
#   cannot read
law core_infer_malformed:
  for +s: String
  for h: {FIn.get_req(s) == Wr.Bad{} : Wr.Dec<FIn.Req>}
  {FIn.ffi(s) == Wr.err("strict plan request: malformed") : String}

# LAW core_infer_left_over (R3): a strict plan request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law core_infer_left_over:
  for +q: FIn.Req
  for c: Char
  for rest: String
  for h: {core_infer_fits(q) == True{} : Bool}
  {FIn.ffi(FIn.put_req(q, SCon{c, rest})) == Wr.err("strict plan request: input left over") : String}

# LAW core_infer_req_example (R1): anchor and witness: a request is the cap (0, or 1 then the cap),
# the tools (count, then id and priority each) and the needed ids
# EXCLUDES: a vacuous core_infer_round_trip, fields in another order than
#   `api/constrained_sampling.rs` writes them
law core_infer_req_example:
  {core_infer_fits(FIn.Req{Some{1n}, [If.Tool{7n, 3n}, If.Tool{9n, 0n}], [9n]}) == True{} : Bool} & {FIn.put_req(FIn.Req{Some{1n}, [If.Tool{7n, 3n}, If.Tool{9n, 0n}], [9n]}, "") == "1,1,2,7,3,9,0,1,9," : String}

# LAW core_infer_reply_example (R2): anchor: a plan that fits is 0 then the loose ids; a refusal is 1
# then the tool's id
# EXCLUDES: a refusal the Rust reader reads as a plan, or the reverse
law core_infer_reply_example:
  {FIn.put_plan(If.Fits{[3n, 1n]}, FIn.put_plan(If.Over{7n}, "")) == "0,2,3,1,1,7," : String}

# LAW core_infer_malformed_example (R3): witness: a malformed strict plan request exists (an unknown cap
# tag)
# EXCLUDES: a vacuous core_infer_malformed
law core_infer_malformed_example:
  {FIn.get_req("2,") == Wr.Bad{} : Wr.Dec<FIn.Req>} & {FIn.ffi("2,") == Wr.err("strict plan request: malformed") : String}

# The entry, independently of bend/ffi_infer.bend and of the model's
# functions: a reader of the request grammar (the header of
# bend/ffi_infer.bend) built from the wire primitives, the plan as
# bend/infer.bend's header (section 3) states it, and a speller of the
# reply from the wire primitives.

# a Maybe<Nat>: 0 none | 1, then the Nat
def ir.mnat.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Some{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ir.mnat.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      ir.mnat.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def ir.mnat(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      ir.mnat.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a tool: its id, then its priority
def ir.tool.p(i: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<If.Tool>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{If.Tool{i, p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ir.tool.i(r: Wr.Dec<Nat>) -> Wr.Dec<If.Tool>:
  match r:
    case Wr.Got{i, s}:
      ir.tool.p(i, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ir.tool(s: String) -> Wr.Dec<If.Tool>:
  ir.tool.i(Wr.get_nat(s))

# a request: the cap, the tools (a list), the needed ids (a list)
def ir.req.need(cap: Maybe<&2, Nat>, ts: List<&2, If.Tool>, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FIn.Req>:
  match r:
    case Wr.Got{need, s}:
      Wr.Got{FIn.Req{cap, ts, need}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ir.req.ts(cap: Maybe<&2, Nat>, r: Wr.Dec<List<&2, If.Tool>>) -> Wr.Dec<FIn.Req>:
  match r:
    case Wr.Got{ts, s}:
      ir.req.need(cap, ts, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

def ir.req.cap(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<FIn.Req>:
  match r:
    case Wr.Got{cap, s}:
      ir.req.ts(cap, Wr.get_list(~If.Tool, ~ir.tool, s))
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with, and what follows it
def ir.read(s: String) -> Wr.Dec<FIn.Req>:
  ir.req.cap(ir.mnat(Wr.get_nat(s)))

# b ? t : e
def is.if(-A: Data, b: Bool, t: A, e: A) -> A:
  match b:
    case True{}:
      t
    case False{}:
      e

def is.id(t: If.Tool) -> Nat:
  match t:
    case If.Tool{i, p}:
      i

def is.prio(t: If.Tool) -> Nat:
  match t:
    case If.Tool{i, p}:
      p

# x put into ys (highest priority first) before the first tool of
# priority at most x's: x goes before the tools it ties with
def is.ins(+x: If.Tool, ys: List<&2, If.Tool>) -> List<&2, If.Tool>:
  match ys:
    case Nil{}:
      [x]
    case +y <> +yt:
      is.if(List<&2, If.Tool>, Nat.is_le(is.prio(y), is.prio(x)), x <> y <> yt, y <> is.ins(x, yt))

# the tools by priority, highest first; among equal priorities the earlier
# tool comes first (a stable sort)
def is.sort(ts: List<&2, If.Tool>) -> List<&2, If.Tool>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      is.ins(t, is.sort(rest))

# the loose tools: with no cap none; with a cap c the tools past the c
# highest
def is.loose(cap: Maybe<&2, Nat>, ts: List<&2, If.Tool>) -> List<&2, If.Tool>:
  match cap:
    case None{}:
      Nil{}
    case Some{c}:
      List.drop(&2, If.Tool, is.sort(ts), c)

# xs lists x
def is.elem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), is.elem(rest, x))

# the id of the first tool of ls that requires a strict schema
def is.needed(ls: List<&2, If.Tool>, +need: List<&2, Nat>) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case +t <> rest:
      is.if(Maybe<&2, Nat>, is.elem(need, is.id(t)), Some{is.id(t)}, is.needed(rest, need))

def is.ids(ts: List<&2, If.Tool>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      is.id(t) <> is.ids(rest)

def is.plan.of(m: Maybe<&2, Nat>, loose: List<&2, If.Tool>) -> If.Plan:
  match m:
    case Some{i}:
      If.Over{i}
    case None{}:
      If.Fits{is.ids(loose)}

# the plan: the first loose tool (highest priority first) that requires a
# strict schema is refused; else every tool fits, with the loose ids
def is.plan(cap: Maybe<&2, Nat>, ts: List<&2, If.Tool>, +need: List<&2, Nat>) -> If.Plan:
  +loose = is.loose(cap, ts)
  is.plan.of(is.needed(loose, need), loose)

# the reply: 0 then the loose ids | 1 then the refused tool's id
def is.put_plan(p: If.Plan) -> String:
  match p:
    case If.Fits{ls}:
      Wr.put_nat(0n, Wr.put_list(~Nat, ~Wr.put_nat, ls, ""))
    case If.Over{i}:
      Wr.put_nat(1n, Wr.put_nat(i, ""))

def is.end(whole: Bool, q: FIn.Req) -> String:
  match whole:
    case True{}:
      match q:
        case FIn.Req{cap, ts, need}:
          is.put_plan(is.plan(cap, ts, need))
    case False{}:
      Wr.err("strict plan request: input left over")

def is.run(r: Wr.Dec<FIn.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      is.end(Wr.end(s), q)
    case Wr.Bad{}:
      Wr.err("strict plan request: malformed")

# the reply to the input s
def is.spec(s: String) -> String:
  is.run(ir.read(s))

# LAW core_infer_ffi_exact (R1-R3): on every input the entry answers the plan of the request the input starts with (the tools ranked by priority, highest first, an earlier tool first among equals; with a cap c the tools past the c highest are loose, with no cap none; the first loose tool, in that order, that requires a strict schema is refused by its id, else the loose ids, in that order), spelled as the Rust reader reads it, when nothing follows the request; "strict plan request: input left over" when something does; "strict plan request: malformed" when the input starts with no request
# EXCLUDES: a ranking that breaks a tie by the later tool or by id, loose
#   ids in another order, another refused tool than the first loose needed
#   one, a needed tool sent loose; a reply in another spelling; a value for
#   an input that is no request (an unknown cap tag, a list cut short, a
#   15-digit number) or for a request with input left over; another error
#   text
law core_infer_ffi_exact:
  for +s: String
  {FIn.ffi(s) == is.spec(s) : String}

# ---- model_facts ----

# LAWS (S6.10): model and provider facts are data. A wire API decides a
# fact of a model only from the quirks rulebook's answer (and the model's
# explicit compat flag or the user's setting), the thinking budgets stay
# inside the model's limits, and where a fact moved from code into data the
# data gives the answers the code gave. Each law is an open claim about the
# model in bend/facts.bend; PROOF.bend proves them (as Infer.<law>)
# with the lemmas of proof/facts/. The decisions run as the compiled core
# (entry bend/ffi_model_facts.bend, laws/model_facts.bend).

# (S6.10.1) Decisions are rulebook lookups
# ----------------------------------------

# LAW facts_rulebook_decides: when a rule of a compiled rulebook applies to a model and no rule of
# a higher layer applies with its directive, the decision of that directive
# is the rule's value: the table decides, whatever the wire API's default
law facts_rulebook_decides:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +r: If.Rule
  for +post: List<&2, If.Rule>
  for +q: If.Query
  for dflt: Bool
  for ok: {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == True{} : Bool}
  for hit: {If.applies(q, r) == True{} : Bool}
  for top: {If.any_at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), 1n+If.Rule.rank(r)) == False{} : Bool}
  {Fx.decide(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), dflt) == Nat.is_eq(If.Rule.val(r), 1n) : Bool}

# LAW facts_rulebook_default: with no rule that applies, the decision is the wire API's stated
# default, never a guess from the model's id
law facts_rulebook_default:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for dflt: Bool
  for none: {If.any_at(rs, q, d, 0n) == False{} : Bool}
  {Fx.decide(rs, q, d, dflt) == dflt : Bool}

# LAW facts_only_the_rulebook_decides: two models with one rulebook answer get one decision: a model's id
# reaches a decision only through the rulebook
law facts_only_the_rulebook_decides:
  for +rs: List<&2, If.Rule>
  for +q1: If.Query
  for +q2: If.Query
  for +d: Nat
  for dflt: Bool
  for same: {If.lookup(rs, q1, d) == If.lookup(rs, q2, d) : If.Ans}
  {Fx.decide(rs, q1, d, dflt) == Fx.decide(rs, q2, d, dflt) : Bool}
