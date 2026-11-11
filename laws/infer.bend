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
#
# Requirements (bend/infer.bend header, sections 1-6;
# crates/eukhe-ai/src/models/ladder.rs module docs; R1-R3 of the core
# entries: laws/base.bend):
# S6.1  The quirks rulebook: a rule of an unknown directive, or two rules of
#       one layer, target and directive with different values, make the
#       rulebook fail to compile; a lookup takes the rule of the highest
#       layer that applies (host over model over family); no rule applies:
#       Unknown, never a guess.
# S6.2  A forced tool call: the first attempt sets the native flag only when
#       supported and free, each retry when supported; at most 1 + r
#       attempts; the call reports a call or the failure.
# S6.3  The strict schema budget: with a cap c, at most c tools are strict,
#       those of highest priority, the rest loose, none lost (no cap: every
#       tool strict); a tool that requires a strict schema is never sent
#       loose: the plan refuses and names such a tool.
# S6.4  The repetition guard: a stream whose last k chunks are periodic, with
#       a period of at most k/4 (at least 1), is cut; no other is.
# S6.5  Early compaction starts a margin below the limit.
# S6.9  The thinking ladder: (a) the explicit map decides, else the
#       rulebook's ladder, else no map (every level left to the default
#       ladder); (b) a reasoning model offers a level whose entry is a wire
#       string, or that has no entry and the default ladder lists, never a
#       level whose entry is null; (c) a model reasons by its flag, a
#       registry model also by an explicit map that gives a level a wire
#       string (#2858), by nothing else.
# S6.10 A wire API decides a flag fact by the rulebook's answer (below).
# A1    Whether a rulebook compiles does not depend on the order of its rules.
# A2    The plan refuses only when a loose tool requires a strict schema;
#       otherwise it fits and lists the loose tools.

# LAW quirk_unknown_when_none: with no rule that applies, the answer is Unknown, never a guess
law quirk_unknown_when_none:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for none: {If.any_at(rs, q, d, 0n) == False{} : Bool}
  {If.lookup(rs, q, d) == If.Unknown{} : If.Ans}

# the answer a is known: some value, not Unknown
def rb.known(a: If.Ans) -> Bool:
  match a:
    case If.Known{v}:
      True{}
    case If.Unknown{}:
      False{}

# LAW quirk_known_when_some (S6.1): a rule that applies (a rule of the
# directive whose target the query matches, any layer) always gives an
# answer: the lookup is Known{v} for some value v, never Unknown
# EXCLUDES: an applying rule ignored (Unknown answered), a known answer
#   read through the model's own is_known test (the law reads the answer's
#   constructor)
law quirk_known_when_some:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for some: {If.any_at(rs, q, d, 0n) == True{} : Bool}
  {rb.known(If.lookup(rs, q, d)) == True{} : Bool}

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

# The rulebook conditions of S6.1, written here from the rule fields only
# (never the code's elem, clash, clashes, ambiguous or known_all)

# directive d is one of the known directives ks
def rb.has(ks: List<&2, Nat>, +d: Nat) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case k <> rest:
      Bool.or(Nat.is_eq(k, d), rb.has(rest, d))

# every rule of rs has a known directive
def rb.all_known(+ks: List<&2, Nat>, rs: List<&2, If.Rule>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +r <> rest:
      Bool.and(rb.has(ks, If.Rule.dir(r)), rb.all_known(ks, rest))

# a and b are of one layer
def rb.same_layer(a: If.Lay, b: If.Lay) -> Bool:
  match a b:
    case If.Fam{} If.Fam{}:
      True{}
    case If.Fam{} If.Mod{}:
      False{}
    case If.Fam{} If.Host{}:
      False{}
    case If.Mod{} If.Fam{}:
      False{}
    case If.Mod{} If.Mod{}:
      True{}
    case If.Mod{} If.Host{}:
      False{}
    case If.Host{} If.Fam{}:
      False{}
    case If.Host{} If.Mod{}:
      False{}
    case If.Host{} If.Host{}:
      True{}

# a and b clash (S6.1): one layer, target and directive, different values
def rb.clash(a: If.Rule, b: If.Rule) -> Bool:
  match a b:
    case If.Rule{la, ta, da, va} If.Rule{lb, tb, db, vb}:
      Bool.and(rb.same_layer(la, lb), Bool.and(Nat.is_eq(ta, tb), Bool.and(Nat.is_eq(da, db), Bool.not(Nat.is_eq(va, vb)))))

# r clashes with no rule of rs
def rb.calm(+r: If.Rule, rs: List<&2, If.Rule>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +s <> rest:
      Bool.and(Bool.not(rb.clash(r, s)), rb.calm(r, rest))

# no rule of xs clashes with any rule of rs
def rb.calm_all(xs: List<&2, If.Rule>, +rs: List<&2, If.Rule>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(rb.calm(x, rs), rb.calm_all(rest, rs))

# LAW quirk_unknown_rejected (S6.1): a rulebook with a rule whose
# directive is none of the known directives (rb.has, the laws' own check)
# does not compile, wherever the rule stands and whatever the other rules
# EXCLUDES: an unknown directive compiled (a typo in rulebook.json taken
#   as a rule nobody reads), only the first or last rule checked, the
#   check read through the model's own elem
law quirk_unknown_rejected:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +r: If.Rule
  for +post: List<&2, If.Rule>
  for bad: {rb.has(known, If.Rule.dir(r)) == False{} : Bool}
  {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == False{} : Bool}

# LAW quirk_clash_rejected (S6.1): a rulebook with two rules that clash
# (rb.clash, the laws' own check: one layer, target and directive,
# different values), at any two places, does not compile: precedence is
# never ambiguous
# EXCLUDES: two clashing rules compiled (the answer then depends on their
#   order), only neighbours checked, the clash read through the model's
#   own clash
law quirk_clash_rejected:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +a: If.Rule
  for +mid: List<&2, If.Rule>
  for +b: If.Rule
  for +post: List<&2, If.Rule>
  for both: {rb.clash(a, b) == True{} : Bool}
  {If.compiles(known, List.append(&2, If.Rule, pre, a <> List.append(&2, If.Rule, mid, b <> post))) == False{} : Bool}

# LAW quirk_valid_rulebook_compiles (S6.1): a rulebook compiles whenever every rule has a
# known directive and no rule clashes with any rule of the rulebook (no
# two rules of one layer, target and directive with different values),
# for every list of known directives and every list of rules, the empty
# one included
# EXCLUDES: a valid rulebook refused (a compiler that refuses every
#   rulebook, the empty one, one rule, or rules that repeat one value)
law quirk_valid_rulebook_compiles:
  for +known: List<&2, Nat>
  for +rs: List<&2, If.Rule>
  for kn: {rb.all_known(known, rs) == True{} : Bool}
  for calm: {rb.calm_all(rs, rs) == True{} : Bool}
  {If.compiles(known, rs) == True{} : Bool}

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

# LAW strict_within_cap (S6.3): with a cap, at most cap tools of a request get strict schemas
law strict_within_cap:
  for +cap: Nat
  for +ts: List<&2, If.ToolPrio>
  {Nat.is_le(List.length(&2, If.ToolPrio, Pair.fst(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(Some{cap}, ts))), cap) == True{} : Bool}

# LAW strict_keeps_every_tool (S6.3): with a cap, no tool of a request is lost: every tool is strict
# or loose, as many times as it was given
law strict_keeps_every_tool:
  for +cap: Nat
  for +ts: List<&2, If.ToolPrio>
  for +i: Nat
  {Nat.add(If.count(Pair.fst(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(Some{cap}, ts)), i), If.count(Pair.snd(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(Some{cap}, ts)), i)) == If.count(ts, i) : Nat}

# LAW strict_by_priority (S6.3): with a cap, every strict tool of a request has a priority of at
# least every loose tool
law strict_by_priority:
  for +cap: Nat
  for +ts: List<&2, If.ToolPrio>
  {If.dominates(Pair.fst(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(Some{cap}, ts)), Pair.snd(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(Some{cap}, ts))) == True{} : Bool}

# the ids of the tools of ts, in order
def strict.ids(ts: List<&2, If.ToolPrio>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      If.ToolPrio.id(t) <> strict.ids(rest)

# no id of ids is in need
def plan.none_needed(ids: List<&2, Nat>, +need: List<&2, Nat>) -> Bool:
  match ids:
    case Nil{}:
      True{}
    case i <> rest:
      Bool.and(Bool.not(If.elem(need, i)), plan.none_needed(rest, need))

# LAW plan_fits_unless_forced (S6.3, A2): when no loose tool of a request (under its cap, as
# strict.of splits it, pinned by the strict_* laws) requires a strict
# schema, the plan fits and lists exactly the ids of the loose tools, in
# their order
# EXCLUDES: a refusal of a request that fits, a fit that lists other tools
#   than the loose ones (or drops, adds or reorders loose ids)
law plan_fits_unless_forced:
  for cap: Maybe<&2, Nat>
  for +ts: List<&2, If.ToolPrio>
  for +need: List<&2, Nat>
  for calm: {plan.none_needed(strict.ids(Pair.snd(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(cap, ts))), need) == True{} : Bool}
  {If.plan(cap, ts, need) == If.Fits{strict.ids(Pair.snd(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(cap, ts)))} : If.Plan}

# LAW plan_fits_only_unforced (S6.3): a plan fits only when no loose tool of the request requires a
# strict schema: a loose tool that requires one makes the plan refuse
# EXCLUDES: a fit (with the needed tool dropped from the loose ids, or
#   any list) where the request must be refused
law plan_fits_only_unforced:
  for cap: Maybe<&2, Nat>
  for +ts: List<&2, If.ToolPrio>
  for +need: List<&2, Nat>
  for +ls: List<&2, Nat>
  for f: {If.plan(cap, ts, need) == If.Fits{ls} : If.Plan}
  {plan.none_needed(strict.ids(Pair.snd(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(cap, ts))), need) == True{} : Bool}

# LAW plan_never_loosens_a_needed_tool: a tool that requires a strict schema is never sent loose
# EXCLUDES: a request that drops the schema a tool requires
law plan_never_loosens_a_needed_tool:
  for cap: Maybe<&2, Nat>
  for +ts: List<&2, If.ToolPrio>
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
  for +ts: List<&2, If.ToolPrio>
  for +need: List<&2, Nat>
  for +i: Nat
  for o: {If.plan(cap, ts, need) == If.Over{i} : If.Plan}
  {Bool.and(If.elem(need, i), If.elem(strict.ids(Pair.snd(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(cap, ts))), i)) == True{} : Bool}

# LAW plan_example_over: a required tool past the cap refuses the request (witness of the
# refusal)
law plan_example_over:
  {If.plan(Some{1n}, [If.ToolPrio{0n, 1n}, If.ToolPrio{1n, 3n}, If.ToolPrio{2n, 2n}], [0n, 2n]) == If.Over{2n} : If.Plan}

# LAW plan_example_fits: a required tool within the cap fits (witness of a fit)
law plan_example_fits:
  {If.plan(Some{1n}, [If.ToolPrio{0n, 1n}, If.ToolPrio{1n, 3n}, If.ToolPrio{2n, 3n}], [1n]) == If.Fits{[2n, 0n]} : If.Plan}

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
# rulebook ladder, any default ladders, any level, any flags.
# The precedence (S6.9 a) is stated on the levels a reasoning model offers,
# not on the code's chosen map: each law names the one map that decides
# and reads its entry through `ladder.offers`, the rule S6.9 b, row by row.

# whether a reasoning model offers a level, given the level's entry in the
# map that decides and whether the reasoning default ladder lists the
# level (S6.9 b; crates/eukhe-ai/src/models/ladder.rs module docs, rule 2):
#   a wire string offers the level ("each level whose entry ... is a wire
#   string"); a null entry removes it ("A `null` entry removes the
#   level"); no entry leaves it to the default ladder ("each level that the
#   chosen ladder does not name and the rulebook's default ladder lists")
def ladder.offers(e: Ef.Ent, listed: Bool) -> Bool:
  match e:
    case Ef.Wire{}:
      True{}
    case Ef.Null{}:
      False{}
    case Ef.Missing{}:
      listed

# LAW quirk_ladder_explicit_decides (S6.9 a, b): a reasoning model with an explicit thinking-level
# map e offers a level l exactly when e gives l a wire string, or gives l
# no entry and the reasoning default ladder lists l, whatever ladder the
# rulebook gives the model
# EXCLUDES: the rulebook's ladder (or the default ladder) read over an
#   explicit map, an explicit map ignored, a null entry that keeps its
#   level, a missing entry that drops a level the default ladder lists
law quirk_ladder_explicit_decides:
  for +e: Ef.LvMap
  for +rule: Maybe<&2, Ef.LvMap>
  for +d: If.Defaults
  for +l: Ef.Lv
  {Ef.has(If.lad.offered(True{}, Some{e}, rule, d), l) == ladder.offers(Ef.entry(l, e), Ef.has(If.Defaults.reasoning(d), l)) : Bool}

# LAW quirk_ladder_rule_decides (S6.9 a, b): a reasoning model with no explicit map, to which the
# rulebook gives the ladder m, offers a level l exactly when m gives l a
# wire string, or gives l no entry and the reasoning default ladder lists l
# EXCLUDES: the rulebook's ladder ignored when no explicit map is given
law quirk_ladder_rule_decides:
  for +m: Ef.LvMap
  for +d: If.Defaults
  for +l: Ef.Lv
  {Ef.has(If.lad.offered(True{}, None{}, Some{m}, d), l) == ladder.offers(Ef.entry(l, m), Ef.has(If.Defaults.reasoning(d), l)) : Bool}

# LAW quirk_ladder_default_decides (S6.9 a, b): a reasoning model with no explicit map and no
# rulebook ladder offers exactly the levels the reasoning default ladder
# lists
# EXCLUDES: a level invented or dropped when no map names any level, the
#   plain default ladder read for a reasoning model
law quirk_ladder_default_decides:
  for +d: If.Defaults
  for +l: Ef.Lv
  {Ef.has(If.lad.offered(True{}, None{}, None{}, d), l) == Ef.has(If.Defaults.reasoning(d), l) : Bool}

# LAW quirk_ladder_shipped_is_s10: with the shipped default ladders, the levels a model offers are the
# S10 ladder of its chosen map, so every law of S10 holds for them
law quirk_ladder_shipped_is_s10:
  for r: Bool
  for +map: Ef.LvMap
  {If.lad.offered.of(r, map, If.lad.shipped()) == Ef.offered(Ef.Mdl{r, map}) : List<&2, Ef.Lv>}

# LAW quirk_ladder_flag_reasons (S6.9 c): a model whose reasoning flag is set reasons, whatever
# its maps and whether it is a registry model
# EXCLUDES: a set flag vetoed by an empty or all-null explicit map
law quirk_ladder_flag_reasons:
  for bm: Bool
  for ex: Maybe<&2, Ef.LvMap>
  {If.lad.reasons(True{}, bm, ex) == True{} : Bool}

# LAW quirk_ladder_map_reasons (S6.9 c, #2858): a registry model (by_map) whose explicit map gives
# some level l a wire string reasons, whatever its flag
# EXCLUDES: the coarse flag vetoing what the map addresses (#2858), a map
#   level other than the first ones ignored
law quirk_ladder_map_reasons:
  for f: Bool
  for +m: Ef.LvMap
  for +l: Ef.Lv
  for w: {Ef.entry(l, m) == Ef.Wire{} : Ef.Ent}
  {If.lad.reasons(f, True{}, Some{m}) == True{} : Bool}

# LAW quirk_ladder_reasons_only_so (S6.9 c): a model whose flag is not set reasons only as a
# registry model whose explicit map gives some level a wire string
# EXCLUDES: a model without the flag made to reason by a rulebook ladder,
#   by a map of a model that is no registry model, by a map with only null
#   or missing entries, or by no map
law quirk_ladder_reasons_only_so:
  for bm: Bool
  for ex: Maybe<&2, Ef.LvMap>
  for ok: {If.lad.reasons(False{}, bm, ex) == True{} : Bool}
  exs m: Ef.LvMap
  exs l: Ef.Lv
  {(bm, (ex, Ef.entry(l, m))) == (True{}, (Some{m}, Ef.Wire{})) : Bool & (Maybe<&2, Ef.LvMap> & Ef.Ent)}

# LAW quirk_ladder_map_reasons_example (S6.9 b, c): anchor from the Rust test of #2858
# (crates/eukhe-core/src/durable/models.rs
# `a_map_addressed_level_makes_a_model_thinking_capable`): a registry model
# with the flag off and the map {off: null, xhigh: a string} offers
# minimal, low, medium, high and xhigh under the shipped default ladders;
# one with the map {off: null} does not reason and offers off alone
# EXCLUDES: a vacuous quirk_ladder_map_reasons, the #2858 vector broken
law quirk_ladder_map_reasons_example:
  {[If.lad.offered(If.lad.reasons(False{}, True{}, Some{Ef.LvMap{Ef.Null{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Wire{}, Ef.Missing{}}}), Some{Ef.LvMap{Ef.Null{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Wire{}, Ef.Missing{}}}, None{}, If.lad.shipped()), If.lad.offered(If.lad.reasons(False{}, True{}, Some{Ef.LvMap{Ef.Null{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}}}), Some{Ef.LvMap{Ef.Null{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}}}, None{}, If.lad.shipped())] == [[Ef.Minimal{}, Ef.Low{}, Ef.Medium{}, Ef.High{}, Ef.Xhigh{}], [Ef.Off{}]] : List<&2, List<&2, Ef.Lv>>}

# (infer) The strict plan: bend/ffi_infer.bend
# --------------------------------------------

def core_tool_fits(t: If.ToolPrio) -> Bool:
  match t:
    case If.ToolPrio{i, p}:
      Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(p))

def core_tools_fit(ts: List<&2, If.ToolPrio>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, u}:
      Bool.and(core_tool_fits(t), core_tools_fit(u))

def core_infer_fits(q: FIn.Req) -> Bool:
  match q:
    case FIn.Req{cap, +ts, +need}:
      Bool.and(LawsBase.core_mfits(cap), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, If.ToolPrio, ts)), core_tools_fit(ts)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, need)), LawsBase.wire_nats_fit(need))))

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
  for +ts: List<&2, If.ToolPrio>
  for +need: List<&2, Nat>
  for h: {core_infer_fits(FIn.Req{cap, ts, need}) == True{} : Bool}
  {FIn.ffi(FIn.put_req(FIn.Req{cap, ts, need}, "")) == FIn.put_plan(If.plan(cap, ts, need), "") : String}

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
  {core_infer_fits(FIn.Req{Some{1n}, [If.ToolPrio{7n, 3n}, If.ToolPrio{9n, 0n}], [9n]}) == True{} : Bool} & {FIn.put_req(FIn.Req{Some{1n}, [If.ToolPrio{7n, 3n}, If.ToolPrio{9n, 0n}], [9n]}, "") == "1,1,2,7,3,9,0,1,9," : String}

# LAW core_infer_reply_example (R2): anchor: a plan that fits is 0 then the loose ids; a refusal is 1
# then the tool's id
# EXCLUDES: a refusal the Rust reader reads as a plan, or the reverse
law core_infer_reply_example:
  {FIn.put_plan(If.Fits{[3n, 1n]}, FIn.put_plan(If.Over{7n}, "")) == "0,2,3,1,1,7," : String}

# LAW core_infer_malformed_example (R3): anchor: the input "2," (an unknown cap tag) is read as no
# request and answers the error form "strict plan request: malformed"
# (a closed instance of core_infer_unknown_cap)
# EXCLUDES: an unknown cap tag read as a known one
law core_infer_malformed_example:
  {FIn.get_req("2,") == Wr.Bad{} : Wr.Dec<FIn.Req>} & {FIn.ffi("2,") == Wr.err("strict plan request: malformed") : String}

# (infer) The entry's bytes, spelled by the grammar
# -------------------------------------------------
# The request and the reply as the wire grammar (bend/wire.bend) and
# `api/constrained_sampling.rs` spell them, written here from the wire
# primitives only (never the entry's put_* or get_*), so a tag, a field
# order or a reply form that drifts on both sides of the entry alike is
# caught.

# a cap or none: 0 none, 1 then the cap
def core_infer_spell_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

# a tool: its id, then its priority
def core_infer_spell_tool(t: If.ToolPrio, rest: String) -> String:
  match t:
    case If.ToolPrio{i, p}:
      Wr.put_nat(i, Wr.put_nat(p, rest))

# the tools of ts, each spelled, then rest
def core_infer_spell_tools.items(ts: List<&2, If.ToolPrio>, rest: String) -> String:
  match ts:
    case Nil{}:
      rest
    case t <> u:
      core_infer_spell_tool(t, core_infer_spell_tools.items(u, rest))

# a list of tools: its count, then each tool
def core_infer_spell_tools(+ts: List<&2, If.ToolPrio>, rest: String) -> String:
  Wr.put_nat(List.length(&2, If.ToolPrio, ts), core_infer_spell_tools.items(ts, rest))

# a request: the cap, the tools, the ids of the tools that need a strict
# schema
def core_infer_spell_req(q: FIn.Req, rest: String) -> String:
  match q:
    case FIn.Req{cap, ts, need}:
      core_infer_spell_mnat(cap, core_infer_spell_tools(ts, LawsBase.wire_spell_nats(need, rest)))

# a plan: 0 then the ids of the loose tools (it fits), or 1 then the id of
# the tool it refuses
def core_infer_spell_plan(p: If.Plan, rest: String) -> String:
  match p:
    case If.Fits{ls}:
      Wr.put_nat(0n, LawsBase.wire_spell_nats(ls, rest))
    case If.Over{i}:
      Wr.put_nat(1n, Wr.put_nat(i, rest))

# the spelled reply of the model's strict plan of q (bend/infer.bend plan)
def core_infer_spell_answer(q: FIn.Req) -> String:
  match q:
    case FIn.Req{cap, +ts, +need}:
      core_infer_spell_plan(If.plan(cap, ts, need), "")

# LAW core_infer_answers_spelled: a strict plan request spelled by the grammar, every number
# within the wire, is answered with the grammar's spelling of the model's
# plan: 0 then the loose ids (a count, then each id), or 1 then the id of
# the refused tool
# EXCLUDES: a cap tag or a plan tag that drifts from the grammar Rust
#   writes and reads (swapped on both sides of the entry alike), a tool's
#   id and priority swapped, tools or needed ids lost, added or reordered,
#   another reply form
law core_infer_answers_spelled:
  for +q: FIn.Req
  for fits: {core_infer_fits(q) == True{} : Bool}
  {FIn.ffi(core_infer_spell_req(q, "")) == core_infer_spell_answer(q) : String}

# LAW core_infer_left_over_spelled: a spelled strict plan request that fits, followed by any more
# input, answers the error form "strict plan request: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request
law core_infer_left_over_spelled:
  for +q: FIn.Req
  for fits: {core_infer_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FIn.ffi(core_infer_spell_req(q, SCon{c, t})) == Wr.err("strict plan request: input left over") : String}

# LAW core_infer_unknown_cap: a cap tag of 2 or more (of any length) answers the error form
# "strict plan request: malformed", whatever follows
# EXCLUDES: an unknown cap tag read as no cap or as some cap
law core_infer_unknown_cap:
  for +n: Nat
  for +rest: String
  {FIn.ffi(Wr.put_nat(2n+n, rest)) == Wr.err("strict plan request: malformed") : String}

# LAW core_infer_reads_only_requests: an answer that is not the error form answers a strict
# plan request: the input is exactly the spelling of a request whose
# numbers fit the wire, and the answer is the spelled reply of the model's
# plan of it
# EXCLUDES: a decoder that accepts an unknown cap tag, a missing or extra
#   tool field or id, a count larger than the items, or input left over,
#   and answers it anyway (a default instead of the error form)
law core_infer_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FIn.ffi(s)) == False{} : Bool}
  exs q: FIn.Req
  {(s, (core_infer_fits(q), FIn.ffi(s))) == (core_infer_spell_req(q, ""), (True{}, core_infer_spell_answer(q))) : String & (Bool & String)}

# LAW core_infer_malformed_unless_request: every answer but the error form "strict plan request:
# malformed" comes from an input that begins with a spelled strict plan
# request that fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law core_infer_malformed_unless_request:
  for +s: String
  for other: {String.eq(FIn.ffi(s), Wr.err("strict plan request: malformed")) == False{} : Bool}
  exs q: FIn.Req
  exs rest: String
  {(s, core_infer_fits(q)) == (core_infer_spell_req(q, rest), True{}) : String & Bool}

# LAW core_infer_tags_example: anchor: the bytes `api/constrained_sampling.rs` sends and reads:
# cap 1, tools 7 (priority 3) and 9 (priority 0), 9 needed: 9 is loose and
# refused (1,9,); 7 needed instead: fits, 9 loose (0,1,9,); no cap: fits,
# none loose (0,0,); cap 0: fits, both loose; cap tag 2, a tool with no
# priority and a needed count with no id are malformed; a request with
# input left over is refused
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, an unknown cap tag read as a known one
law core_infer_tags_example:
  {[FIn.ffi("1,1,2,7,3,9,0,1,9,"), FIn.ffi("1,1,2,7,3,9,0,1,7,"), FIn.ffi("0,2,7,3,9,0,0,"), FIn.ffi("1,0,2,7,3,9,0,0,")] == ["1,9,", "0,1,9,", "0,0,", "0,2,7,9,"] : List<&2, String>} & {[FIn.ffi("2,0,0,"), FIn.ffi("0,1,7,"), FIn.ffi("0,0,1,"), FIn.ffi("0,0,0,x")] == [Wr.err("strict plan request: malformed"), Wr.err("strict plan request: malformed"), Wr.err("strict plan request: malformed"), Wr.err("strict plan request: input left over")] : List<&2, String>}

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
def ir.tool.p(i: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<If.ToolPrio>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{If.ToolPrio{i, p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ir.tool.i(r: Wr.Dec<Nat>) -> Wr.Dec<If.ToolPrio>:
  match r:
    case Wr.Got{i, s}:
      ir.tool.p(i, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ir.tool(s: String) -> Wr.Dec<If.ToolPrio>:
  ir.tool.i(Wr.get_nat(s))

# a request: the cap, the tools (a list), the needed ids (a list)
def ir.req.need(cap: Maybe<&2, Nat>, ts: List<&2, If.ToolPrio>, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FIn.Req>:
  match r:
    case Wr.Got{need, s}:
      Wr.Got{FIn.Req{cap, ts, need}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ir.req.ts(cap: Maybe<&2, Nat>, r: Wr.Dec<List<&2, If.ToolPrio>>) -> Wr.Dec<FIn.Req>:
  match r:
    case Wr.Got{ts, s}:
      ir.req.need(cap, ts, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

def ir.req.cap(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<FIn.Req>:
  match r:
    case Wr.Got{cap, s}:
      ir.req.ts(cap, Wr.get_list(~If.ToolPrio, ~ir.tool, s))
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

def is.id(t: If.ToolPrio) -> Nat:
  match t:
    case If.ToolPrio{i, p}:
      i

def is.prio(t: If.ToolPrio) -> Nat:
  match t:
    case If.ToolPrio{i, p}:
      p

# x put into ys (highest priority first) before the first tool of
# priority at most x's: x goes before the tools it ties with
def is.ins(+x: If.ToolPrio, ys: List<&2, If.ToolPrio>) -> List<&2, If.ToolPrio>:
  match ys:
    case Nil{}:
      [x]
    case +y <> +yt:
      is.if(List<&2, If.ToolPrio>, Nat.is_le(is.prio(y), is.prio(x)), x <> y <> yt, y <> is.ins(x, yt))

# the tools by priority, highest first; among equal priorities the earlier
# tool comes first (a stable sort)
def is.sort(ts: List<&2, If.ToolPrio>) -> List<&2, If.ToolPrio>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      is.ins(t, is.sort(rest))

# the loose tools: with no cap none; with a cap c the tools past the c
# highest
def is.loose(cap: Maybe<&2, Nat>, ts: List<&2, If.ToolPrio>) -> List<&2, If.ToolPrio>:
  match cap:
    case None{}:
      Nil{}
    case Some{c}:
      List.drop(&2, If.ToolPrio, is.sort(ts), c)

# xs lists x
def is.elem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), is.elem(rest, x))

# the id of the first tool of ls that requires a strict schema
def is.needed(ls: List<&2, If.ToolPrio>, +need: List<&2, Nat>) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case +t <> rest:
      is.if(Maybe<&2, Nat>, is.elem(need, is.id(t)), Some{is.id(t)}, is.needed(rest, need))

def is.ids(ts: List<&2, If.ToolPrio>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      is.id(t) <> is.ids(rest)

def is.plan.of(m: Maybe<&2, Nat>, loose: List<&2, If.ToolPrio>) -> If.Plan:
  match m:
    case Some{i}:
      If.Over{i}
    case None{}:
      If.Fits{is.ids(loose)}

# the plan: the first loose tool (highest priority first) that requires a
# strict schema is refused; else every tool fits, with the loose ids
def is.plan(cap: Maybe<&2, Nat>, ts: List<&2, If.ToolPrio>, +need: List<&2, Nat>) -> If.Plan:
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

# LAWS (S6.10.1): a wire API's decision of a flag fact is the quirks
# rulebook's answer for one directive: the value of the highest rule that
# applies (facts_rulebook_decides), else the wire API's stated default
# (facts_rulebook_default). Each law is an open claim about `Fx.decide` in
# bend/facts.bend; PROOF.bend proves them (as Infer.<law>). That a model's
# id reaches a decision only through the rulebook is not a law here: it is
# the shape of the entry bend/ffi_model_facts.bend, whose requests carry the
# rulebook's answer, the compat flag and the user's setting and no model id
# (its laws: laws/model_facts.bend). The budgets and the facts that moved
# from code into data: laws/facts/.

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

# LAW strict_no_cap: with no cap every tool keeps its strict schema
law strict_no_cap:
  for +ts: List<&2, If.ToolPrio>
  {If.strict.of(None{}, ts) == (ts, []) : List<&2, If.ToolPrio> & List<&2, If.ToolPrio>}

# LAW quirk_known_when_some: a rule that applies always gives an answer
law quirk_known_when_some_orig:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for some: {If.any_at(rs, q, d, 0n) == True{} : Bool}
  {If.is_known(If.lookup(rs, q, d)) == True{} : Bool}
