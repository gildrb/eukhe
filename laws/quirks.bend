# eukhe: the laws of area quirks

import Base
import ../bend/infer.bend as If
import ../bend/ffi_quirks.bend as FQ
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- quirks ----

# LAWS (S6.1): the quirks rulebook runs as the compiled model
# (bend/ffi_quirks.bend, a stepper over bend/infer.bend section 1; the
# model's own laws are in laws/infer.bend). Rust opens it with the known
# directives and the rules, as numbers; the core keeps a rulebook that
# compiles and answers each lookup. Each law is an open claim about the
# entry; PROOF.bend proves them (as Quirks.<law>) with the lemmas of
# proof/quirks/.
#
# R1: an open answers whether the rulebook compiles (the model's
#     `compiles`) and the verdict on each rule, in order: its directive is
#     unknown; else it clashes with a later rule (one layer, target and
#     directive, another value): the index of the first such rule; else it
#     is fine. A rulebook that compiles is kept; one that does not is not.
# R2: some verdict is not fine exactly when the rulebook does not compile,
#     so Rust never takes a rejected rulebook for a good one, nor reports
#     no reason for a rejection.
# R3: a lookup in a kept rulebook answers the model's lookup (the rule of
#     the highest layer that applies: host over model over family;
#     Unknown when none does), and keeps the rulebook.
# R4: any open that is not exactly an open Rust writes (two lists of Nats,
#     the second four Nats a rule with a layer tag below 3, nothing after)
#     answers the error form and keeps no rulebook; any lookup that is not
#     exactly four Nats answers the error form and keeps the rulebook; a
#     rulebook that was not kept answers every lookup with the error form.
# Every input is free: any known directives, rules, queries and text;
# every number that fits the wire.
# R1 is quirks_open_answers (the reply's spelling) with the verdict laws
# quirks_verdicts_count, _heard, _fine, _clash and _first (each verdict
# by its properties, which fix it), and quirks_rejected_run; R2 is
# quirks_faults_iff_rejected; R3 is quirks_lookup_answers and
# quirks_lookup_exact, with quirks_any_at_found and quirks_any_at_witness
# for the model's `any_at` the model's laws read; R4 is quirks_open_reads,
# quirks_open_refuses, quirks_lookup_reads, quirks_lookup_refuses and
# quirks_rejected_run.

# Spellers: what Rust writes, from the wire primitives
# ----------------------------------------------------

# a layer's tag
def qs_lay(l: If.Lay) -> Nat:
  match l:
    case If.Fam{}:
      0n
    case If.Mod{}:
      1n
    case If.Host{}:
      2n

# the rules, four Nats each: layer, target, directive, value
def qs_flat(rs: List<&2, If.Rule>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case If.Rule{l, t, d, v}:
          qs_lay(l) <> t <> d <> v <> qs_flat(rest)

# the open Rust writes: the known directives, then the rules
def spell_open(known: List<&2, Nat>, rs: List<&2, If.Rule>) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, known, Wr.put_list(~Nat, ~Wr.put_nat, qs_flat(rs), ""))

# every number of an open fits the wire
def open_fits(+known: List<&2, Nat>, +rs: List<&2, If.Rule>) -> Bool:
  +xs = qs_flat(rs)
  Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, known)), LawsBase.wire_nats_fit(known)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)))

# the lookup Rust writes: family, model, host, directive
def spell_lookup(q: If.Query, d: Nat) -> String:
  match q:
    case If.Query{f, m, h}:
      Wr.put_list(~Nat, ~Wr.put_nat, [f, m, h, d], "")

# every number of a lookup fits the wire
def lookup_fits(q: If.Query, +d: Nat) -> Bool:
  match q:
    case If.Query{f, m, h}:
      LawsBase.wire_nats_fit([f, m, h, d])

# The verdicts, as a spec
# -----------------------

def qs_lay_same(a: If.Lay, b: If.Lay) -> Bool:
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

# two rules clash: one layer, target and directive, and another value
def qs_clash(a: If.Rule, b: If.Rule) -> Bool:
  match a b:
    case If.Rule{la, ta, da, va} If.Rule{lb, tb, db, vb}:
      Bool.and(qs_lay_same(la, lb), Bool.and(Nat.is_eq(ta, tb), Bool.and(Nat.is_eq(da, db), Bool.not(Nat.is_eq(va, vb)))))

def qs_pick(b: Bool, i: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{i}
    case False{}:
      m

# the index of the first rule of rs that clashes with r, rs starting at
# index i
def qs_partner(rs: List<&2, If.Rule>, +r: If.Rule, +i: Nat) -> Maybe<&2, Nat>:
  match rs:
    case Nil{}:
      None{}
    case s <> rest:
      qs_pick(qs_clash(r, s), i, qs_partner(rest, r, 1n+i))

# d is one of ds
def qs_mem(ds: List<&2, Nat>, +d: Nat) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case e <> rest:
      Bool.or(Nat.is_eq(e, d), qs_mem(rest, d))

def qs_dir(r: If.Rule) -> Nat:
  match r:
    case If.Rule{l, t, d, v}:
      d

# the verdict on a rule whose directive is known (or not) and whose first
# later clash is p: 1 unknown; 0 fine; 2 then the index of the clash
def spell_verdict(known: Bool, p: Maybe<&2, Nat>, rest: String) -> String:
  match known:
    case False{}:
      Wr.put_nat(1n, rest)
    case True{}:
      match p:
        case None{}:
          Wr.put_nat(0n, rest)
        case Some{j}:
          Wr.put_nat(2n, Wr.put_nat(j, rest))

# the verdicts on the rules of rs, the first at index i
def spell_verdicts.items(rs: List<&2, If.Rule>, +known: List<&2, Nat>, +i: Nat) -> String:
  match rs:
    case Nil{}:
      ""
    case +r <> +rest:
      spell_verdict(qs_mem(known, qs_dir(r)), qs_partner(rest, r, 1n+i), spell_verdicts.items(rest, known, 1n+i))

# the verdicts on the rules of rs, as a list
def spell_verdicts(+known: List<&2, Nat>, +rs: List<&2, If.Rule>) -> String:
  Wr.put_nat(List.length(&2, If.Rule, rs), spell_verdicts.items(rs, known, 0n))

# the state an open keeps: the rulebook when it compiles
def qs_kept(ok: Bool, rs: List<&2, If.Rule>) -> FQ.St:
  match ok:
    case True{}:
      FQ.Book{rs}
    case False{}:
      FQ.Shut{}

# the answer of a lookup: 0 Unknown, 1 then the value
def spell_ans(a: If.Ans) -> String:
  match a:
    case If.Unknown{}:
      Wr.put_nat(0n, "")
    case If.Known{v}:
      Wr.put_nat(1n, Wr.put_nat(v, ""))

# The terms the model's laws read, as a spec
# ------------------------------------------

# a layer's precedence: host over model over family
def qs_rank(l: If.Lay) -> Nat:
  match l:
    case If.Fam{}:
      0n
    case If.Mod{}:
      1n
    case If.Host{}:
      2n

def qs_rule_rank(r: If.Rule) -> Nat:
  match r:
    case If.Rule{l, t, d, v}:
      qs_rank(l)

def qs_val(r: If.Rule) -> Nat:
  match r:
    case If.Rule{l, t, d, v}:
      v

# the target a query names at a layer
def qs_target(q: If.Query, l: If.Lay) -> Nat:
  match q:
    case If.Query{f, m, h}:
      match l:
        case If.Fam{}:
          f
        case If.Mod{}:
          m
        case If.Host{}:
          h

# a rule applies to a query: its target is the one the query names at its
# layer
def qs_applies(q: If.Query, r: If.Rule) -> Bool:
  match r:
    case If.Rule{l, t, d, v}:
      Nat.is_eq(t, qs_target(q, l))

# The lookup, as a spec
# ---------------------

def qs_first.is(same: Bool, v: Nat, later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match same:
    case True{}:
      Some{v}
    case False{}:
      later

# hit: rule r applies to the query with the directive looked up
def qs_first.at(hit: Bool, +r: If.Rule, later: Maybe<&2, Nat>, +k: Nat) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      qs_first.is(Nat.is_eq(qs_rule_rank(r), k), qs_val(r), later)
    case False{}:
      later

# the value of the first rule of rs that applies to q with directive d at
# precedence exactly k
def qs_first(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +k: Nat) -> Maybe<&2, Nat>:
  match rs:
    case Nil{}:
      None{}
    case +r <> rest:
      qs_first.at(Bool.and(qs_applies(q, r), Nat.is_eq(qs_dir(r), d)), r, qs_first(rest, q, d, k), k)

# the first of two optional values
def qs_or(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case None{}:
      b
    case Some{v}:
      Some{v}

def qs_answer(m: Maybe<&2, Nat>) -> If.Ans:
  match m:
    case None{}:
      If.Unknown{}
    case Some{v}:
      If.Known{v}

# the answer of a lookup (R3): the value of a rule of the highest
# precedence that applies (host 2 over model 1 over family 0), the first
# such rule; Unknown when none applies. In a rulebook that compiles every
# rule of one precedence that applies has one value (no clash), so
# "first" decides only for a rulebook that does not compile, which no
# open keeps.
def qs_lookup(+rs: List<&2, If.Rule>, +q: If.Query, +d: Nat) -> If.Ans:
  qs_answer(qs_or(qs_first(rs, q, d, 2n), qs_or(qs_first(rs, q, d, 1n), qs_first(rs, q, d, 0n))))

# The verdicts, by their properties
# ---------------------------------

# the verdict m says the rule's directive is known (fine, or a clash); no
# verdict says nothing
def qs_heard(m: Maybe<&2, If.Verdict>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      match v:
        case If.Fine{}:
          True{}
        case If.Unheard{}:
          False{}
        case If.ClashAt{j}:
          True{}

# rule r clashes with the rule m holds (no rule: no clash)
def qs_clash_at(r: If.Rule, m: Maybe<&2, If.Rule>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      qs_clash(r, s)

# how many verdicts of vs are not fine
def qs_faults(vs: List<&2, If.Verdict>) -> Nat:
  match vs:
    case Nil{}:
      0n
    case v <> rest:
      match v:
        case If.Fine{}:
          qs_faults(rest)
        case If.Unheard{}:
          1n+qs_faults(rest)
        case If.ClashAt{j}:
          1n+qs_faults(rest)

# The stepper's run
# -----------------

# an open's reply says the rulebook compiles: it opens with T
def qs_says_compiles(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, 'T')

# the reply r, then the replies of the stepper fed the lookups ins, one
# step each from the state of r
def qs_feed(ins: List<&2, String>, r: FQ.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> qs_feed(t, FQ.step(st, i))

# Laws
# ----

# LAW quirks_open_answers: an open Rust writes answers whether the rulebook compiles (the
# model's `compiles`) and the verdict on each rule, in order, and keeps the
# rulebook exactly when it compiles
# EXCLUDES: a rulebook kept that does not compile (or dropped that does), a
#   verdict lost, added, reordered or pointing at another rule, an unknown
#   directive reported as a clash, rules or fields misread
law quirks_open_answers:
  for +known: List<&2, Nat>
  for +rs: List<&2, If.Rule>
  for fits: {open_fits(known, rs) == True{} : Bool}
  {FQ.open(spell_open(known, rs)) == (qs_kept(If.compiles(known, rs), rs), Wr.put_bool(If.compiles(known, rs), spell_verdicts(known, rs))) : FQ.St & String}

# LAW quirks_faults_iff_rejected (R2): of the model's verdicts (the ones
# the entry spells), none is a fault (unknown directive or clash) exactly
# when the rulebook compiles
# EXCLUDES: a rejection with no reason, a reason given for a rulebook that
#   compiles
law quirks_faults_iff_rejected:
  for +known: List<&2, Nat>
  for +rs: List<&2, If.Rule>
  {Nat.is_eq(qs_faults(If.verdicts(known, rs)), 0n) == If.compiles(known, rs) : Bool}

# LAW quirks_verdicts_count (R1): the model gives one verdict per rule
# EXCLUDES: a verdict lost or added
law quirks_verdicts_count:
  for +known: List<&2, Nat>
  for +rs: List<&2, If.Rule>
  {List.length(&2, If.Verdict, If.verdicts(known, rs)) == List.length(&2, If.Rule, rs) : Nat}

# LAW quirks_verdict_heard (R1): the verdict on rule i says its directive
# is unknown (Unheard) exactly when the directive is not one of the known
# EXCLUDES: an unknown directive reported fine or as a clash, a known one
#   reported unknown, verdicts shifted against the rules
law quirks_verdict_heard:
  for +known: List<&2, Nat>
  for +rs: List<&2, If.Rule>
  for +i: Nat
  for +r: If.Rule
  for at: {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>}
  {qs_heard(List.get(&2, If.Verdict, If.verdicts(known, rs), i)) == qs_mem(known, qs_dir(r)) : Bool}

# LAW quirks_verdict_fine (R1): a rule i reported fine clashes (qs_clash:
# one layer, target and directive, another value) with no later rule j
# EXCLUDES: a clash with a later rule reported fine
law quirks_verdict_fine:
  for +known: List<&2, Nat>
  for +rs: List<&2, If.Rule>
  for +i: Nat
  for +j: Nat
  for +r: If.Rule
  for +s: If.Rule
  for at: {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>}
  for fine: {List.get(&2, If.Verdict, If.verdicts(known, rs), i) == Some{If.Fine{}} : Maybe<&2, If.Verdict>}
  for later: {List.get(&2, If.Rule, rs, j) == Some{s} : Maybe<&2, If.Rule>}
  for after: {Nat.is_lt(i, j) == True{} : Bool}
  {qs_clash(r, s) == False{} : Bool}

# LAW quirks_verdict_clash (R1): a rule i reported as clashing at j clashes
# with rule j, a later rule
# EXCLUDES: a clash pointing at an earlier rule, at itself, past the last
#   rule, or at a rule it does not clash with (an index off by one)
law quirks_verdict_clash:
  for +known: List<&2, Nat>
  for +rs: List<&2, If.Rule>
  for +i: Nat
  for +j: Nat
  for +r: If.Rule
  for at: {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>}
  for clash: {List.get(&2, If.Verdict, If.verdicts(known, rs), i) == Some{If.ClashAt{j}} : Maybe<&2, If.Verdict>}
  {Nat.is_lt(i, j) == True{} : Bool} & {qs_clash_at(r, List.get(&2, If.Rule, rs, j)) == True{} : Bool}

# LAW quirks_verdict_first (R1): a rule i reported as clashing at j clashes
# with no rule k between them: j is the first later rule it clashes with
# EXCLUDES: a clash reported at the last or any other later clashing rule
#   but the first
law quirks_verdict_first:
  for +known: List<&2, Nat>
  for +rs: List<&2, If.Rule>
  for +i: Nat
  for +j: Nat
  for +k: Nat
  for +r: If.Rule
  for +s: If.Rule
  for at: {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>}
  for clash: {List.get(&2, If.Verdict, If.verdicts(known, rs), i) == Some{If.ClashAt{j}} : Maybe<&2, If.Verdict>}
  for mid: {List.get(&2, If.Rule, rs, k) == Some{s} : Maybe<&2, If.Rule>}
  for after: {Nat.is_lt(i, k) == True{} : Bool}
  for before: {Nat.is_lt(k, j) == True{} : Bool}
  {qs_clash(r, s) == False{} : Bool}

# LAW quirks_open_reads (R4): every open the entry does not answer with
# the error form (a reply that opens with 'E') is an open Rust writes: the
# known directives and the rules spelled by spell_open, every number within
# the wire
# EXCLUDES: an answer (and a rulebook kept) for input that is no open:
#   input left over, a layer tag past 2, a rule cut short, a list shorter
#   than its count, a number past the wire's 14 digits
law quirks_open_reads:
  for +s: String
  for ok: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open(s))) == False{} : Bool}
  exs known: List<&2, Nat>
  exs rs: List<&2, If.Rule>
  {s == spell_open(known, rs) : String} & {open_fits(known, rs) == True{} : Bool}

# LAW quirks_open_refuses (R4): an open the entry answers with the error
# form keeps no rulebook and answers exactly 'E ', then "quirks: malformed
# rulebook"
# EXCLUDES: a default rulebook kept for a malformed open, an error text that
#   varies with the input
law quirks_open_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open(s))) == True{} : Bool}
  {FQ.open(s) == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String}

# LAW quirks_lookup_reads (R4): in a kept rulebook, every lookup the entry
# does not answer with the error form is a lookup Rust writes (four Nats:
# family, model, host, directive), every number within the wire
# EXCLUDES: a guessed query for a list of another length, input left over,
#   a malformed number
law quirks_lookup_reads:
  for +rs: List<&2, If.Rule>
  for +s: String
  for ok: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.step(FQ.Book{rs}, s))) == False{} : Bool}
  exs q: If.Query
  exs d: Nat
  {s == spell_lookup(q, d) : String} & {lookup_fits(q, d) == True{} : Bool}

# LAW quirks_lookup_refuses (R4): in a kept rulebook, a lookup answered
# with the error form keeps the rulebook and answers exactly 'E ', then
# "quirks: malformed lookup"
# EXCLUDES: a rulebook dropped or changed by a bad lookup, another error
#   text
law quirks_lookup_refuses:
  for +rs: List<&2, If.Rule>
  for +s: String
  for bad: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.step(FQ.Book{rs}, s))) == True{} : Bool}
  {FQ.step(FQ.Book{rs}, s) == (FQ.Book{rs}, SCon{'E', SCon{' ', "quirks: malformed lookup"}}) : FQ.St & String}

# LAW quirks_rejected_run (R1, R4): after an open whose reply does not say
# the rulebook compiles (it opens with F, or is the error form), the
# stepper answers that reply, then every lookup, whatever its input,
# exactly 'E ', then "quirks: no rulebook"
# EXCLUDES: answers from a rulebook that does not compile, or from a
#   malformed open (a default or partly read rulebook)
law quirks_rejected_run:
  for +s: String
  for +ins: List<&2, String>
  for no: {qs_says_compiles(Pair.snd(FQ.St, String, FQ.open(s))) == False{} : Bool}
  {qs_feed(ins, FQ.open(s)) == Pair.snd(FQ.St, String, FQ.open(s)) <> List.replicate(String, List.length(&2, String, ins), SCon{'E', SCon{' ', "quirks: no rulebook"}}) : List<&2, String>}

# LAW quirks_lookup_answers: a lookup Rust writes, in a kept rulebook, answers the model's
# lookup and keeps the rulebook
# EXCLUDES: another layer's rule, a guess for no rule, the query's fields
#   swapped, a rulebook changed by a lookup
law quirks_lookup_answers:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for fits: {lookup_fits(q, d) == True{} : Bool}
  {FQ.step(FQ.Book{rs}, spell_lookup(q, d)) == (FQ.Book{rs}, spell_ans(If.lookup(rs, q, d))) : FQ.St & String}

# LAW quirks_lookup_exact: the model's lookup is the spec's for every rulebook, query and
# directive: the value of the first rule of the highest precedence that
# applies, Unknown when none does
# EXCLUDES: a lookup wrong on a rulebook the model's laws (quirk_highest_wins
#   and its premises) leave free, an entry law that holds through a model
#   function no law fixes for every input
law quirks_lookup_exact:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  {If.lookup(rs, q, d) == qs_lookup(rs, q, d) : If.Ans}

# LAW quirks_any_at_found (R3): the model's `any_at` (which the model's
# laws quirk_unknown_when_none, quirk_known_when_some and
# quirk_highest_wins read) says yes whenever some rule i of the rulebook
# applies to the query (its target is the one the query names at its
# layer, qs_target), has the directive and a layer of precedence k or
# above (host 2, model 1, family 0)
# EXCLUDES: an any_at that misses a rule (the last, a rule of a higher
#   layer, a rule at exactly precedence k), making those laws' premises
#   hold where a rule applies
law quirks_any_at_found:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for +k: Nat
  for +i: Nat
  for +r: If.Rule
  for at: {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>}
  for hit: {qs_applies(q, r) == True{} : Bool}
  for dir: {Nat.is_eq(qs_dir(r), d) == True{} : Bool}
  for high: {Nat.is_le(k, qs_rule_rank(r)) == True{} : Bool}
  {If.any_at(rs, q, d, k) == True{} : Bool}

# LAW quirks_any_at_witness (R3): the model's `any_at` says yes only when
# some rule i of the rulebook applies to the query, has the directive and a
# layer of precedence k or above
# EXCLUDES: an any_at that says yes for no rule (a rule of another target,
#   directive or a lower layer counted), making those laws vacuous
law quirks_any_at_witness:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for +k: Nat
  for yes: {If.any_at(rs, q, d, k) == True{} : Bool}
  exs i: Nat
  exs r: If.Rule
  {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>} & ({qs_applies(q, r) == True{} : Bool} & ({Nat.is_eq(qs_dir(r), d) == True{} : Bool} & {Nat.is_le(k, qs_rule_rank(r)) == True{} : Bool}))

# LAW quirks_open_example: anchor: the strings Rust sends and reads: a rulebook of a family and a
# model rule compiles; one with two clashing model rules and an unknown
# directive does not (the first rule names the second; the third is
# unknown)
# EXCLUDES: a codec that reads other fields or writes another reply
law quirks_open_example:
  {FQ.open("2,0,1,8,0,1,0,5,1,2,0,7,") == (FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}, If.Rule{If.Mod{}, 2n, 0n, 7n}]}, "T2,0,0,") : FQ.St & String} & {FQ.open("1,0,12,1,2,0,7,1,2,0,8,2,3,4,1,") == (FQ.Shut{}, "F3,2,1,0,1,") : FQ.St & String}

# LAW quirks_lookup_example: anchor: the lookups Rust sends: the model rule over the family
# rule, the family rule alone, no rule
# EXCLUDES: a lookup that reads the query's fields in another order
law quirks_lookup_example:
  {FQ.step(FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}, If.Rule{If.Mod{}, 2n, 0n, 7n}]}, "4,1,2,0,0,") == (FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}, If.Rule{If.Mod{}, 2n, 0n, 7n}]}, "1,7,") : FQ.St & String} & {FQ.step(FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}]}, "4,1,9,0,0,") == (FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}]}, "1,5,") : FQ.St & String} & {FQ.step(FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}]}, "4,1,9,0,1,") == (FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}]}, "0,") : FQ.St & String}

# LAW quirks_malformed_example: anchor: the entry refuses malformed input (a layer tag of 3, a
# rule cut short, input left over, a lookup of three Nats)
# EXCLUDES: a vacuous quirks_open_refuses or quirks_lookup_refuses
law quirks_malformed_example:
  {FQ.open("1,0,4,3,1,0,5,") == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String} & ({FQ.open("1,0,3,0,1,0,") == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String} & ({FQ.open("1,0,0,x") == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String} & {FQ.step(FQ.Book{[]}, "3,1,2,0,") == (FQ.Book{[]}, SCon{'E', SCon{' ', "quirks: malformed lookup"}}) : FQ.St & String}))

# LAW quirks_premises_example: witness: an open and a lookup that fit the wire exist, a rule at
# index 1 is reported clashing (with rule 2), a rejected open is
# followed by a lookup, and any_at says yes for a rule that applies
# EXCLUDES: a vacuous quirks_open_answers, quirks_lookup_answers,
#   quirks_verdict_clash, quirks_verdict_first, quirks_rejected_run or
#   quirks_any_at_witness
law quirks_premises_example:
  {open_fits([0n], [If.Rule{If.Host{}, 1n, 0n, 5n}]) == True{} : Bool} & {lookup_fits(If.Query{1n, 2n, 3n}, 0n) == True{} : Bool} & {If.verdicts([0n], [If.Rule{If.Fam{}, 1n, 0n, 5n}, If.Rule{If.Mod{}, 2n, 0n, 7n}, If.Rule{If.Mod{}, 2n, 0n, 8n}]) == [If.Fine{}, If.ClashAt{2n}, If.Fine{}] : List<&2, If.Verdict>} & {qs_says_compiles(Pair.snd(FQ.St, String, FQ.open("1,0,4,3,1,0,5,"))) == False{} : Bool} & {If.any_at([If.Rule{If.Fam{}, 1n, 0n, 5n}], If.Query{1n, 2n, 3n}, 0n, 0n) == True{} : Bool}

# LAW quirks_host_wins_example: anchor: with a family, a model and a host rule that all apply,
# the host rule answers
# EXCLUDES: a lower layer winning over a host rule
law quirks_host_wins_example:
  {FQ.step(FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}, If.Rule{If.Mod{}, 2n, 0n, 7n}, If.Rule{If.Host{}, 3n, 0n, 9n}]}, "4,1,2,3,0,") == (FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}, If.Rule{If.Mod{}, 2n, 0n, 7n}, If.Rule{If.Host{}, 3n, 0n, 9n}]}, "1,9,") : FQ.St & String} & {FQ.open("1,0,12,0,1,0,5,1,2,0,7,2,3,0,9,") == (FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}, If.Rule{If.Mod{}, 2n, 0n, 7n}, If.Rule{If.Host{}, 3n, 0n, 9n}]}, "T3,0,0,0,") : FQ.St & String}

# the answer is a value
def qs_known(a: If.Ans) -> Bool:
  match a:
    case If.Known{v}:
      True{}
    case If.Unknown{}:
      False{}

# LAW quirks_known_exact: the model's is_known (which quirk_known_when_some reads) says Known
# exactly for a Known answer
# EXCLUDES: an is_known that always says yes, making quirk_known_when_some
#   vacuous (a mutant's)
law quirks_known_exact:
  for a: If.Ans
  {If.is_known(a) == qs_known(a) : Bool}
