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

# every verdict is fine: every directive known, no rule clashes with a
# later one
def qs_all_fine(rs: List<&2, If.Rule>, +known: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +r <> +rest:
      Bool.and(Bool.and(qs_mem(known, qs_dir(r)), Maybe.is_none(&2, Nat, qs_partner(rest, r, 0n))), qs_all_fine(rest, known))

# the answer of a lookup: 0 Unknown, 1 then the value
def spell_ans(a: If.Ans) -> String:
  match a:
    case If.Unknown{}:
      Wr.put_nat(0n, "")
    case If.Known{v}:
      Wr.put_nat(1n, Wr.put_nat(v, ""))

# the answer is a value
def qs_known(a: If.Ans) -> Bool:
  match a:
    case If.Known{v}:
      True{}
    case If.Unknown{}:
      False{}

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

# some rule of rs applies to q with directive d at a precedence of k or
# above
def qs_any_at(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +k: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +r <> rest:
      Bool.or(Bool.and(Bool.and(qs_applies(q, r), Nat.is_eq(qs_dir(r), d)), Nat.is_le(k, qs_rule_rank(r))), qs_any_at(rest, q, d, k))

# Readers: the inputs the entry accepts, read with the wire primitives
# --------------------------------------------------------------------

# an open: the known directives and the rules
type QsOpen is Data:
  QsOpen{known: List<&2, Nat>, rs: List<&2, If.Rule>}

# a lookup: the query and the directive
type QsLookup is Data:
  QsLookup{q: If.Query, d: Nat}

def read_lay(n: Nat) -> Maybe<&2, If.Lay>:
  match n:
    case 0n:
      Some{If.Fam{}}
    case 1n:
      Some{If.Mod{}}
    case 2n:
      Some{If.Host{}}
    case 3n+p:
      None{}

def read_rules.cons(m: Maybe<&2, If.Lay>, t: Nat, d: Nat, v: Nat, r: Maybe<&2, List<&2, If.Rule>>) -> Maybe<&2, List<&2, If.Rule>>:
  match m:
    case None{}:
      None{}
    case Some{l}:
      match r:
        case None{}:
          None{}
        case Some{rs}:
          Some{If.Rule{l, t, d, v} <> rs}

# the rules four Nats each spell
def read_rules(xs: List<&2, Nat>) -> Maybe<&2, List<&2, If.Rule>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case l <> a:
      match a:
        case Nil{}:
          None{}
        case t <> b:
          match b:
            case Nil{}:
              None{}
            case d <> c:
              match c:
                case Nil{}:
                  None{}
                case v <> rest:
                  read_rules.cons(read_lay(l), t, d, v, read_rules(rest))

def read_open.pair(known: List<&2, Nat>, m: Maybe<&2, List<&2, If.Rule>>) -> Maybe<&2, QsOpen>:
  match m:
    case None{}:
      None{}
    case Some{rs}:
      Some{QsOpen{known, rs}}

def read_open.end(whole: Bool, known: List<&2, Nat>, xs: List<&2, Nat>) -> Maybe<&2, QsOpen>:
  match whole:
    case True{}:
      read_open.pair(known, read_rules(xs))
    case False{}:
      None{}

def read_open.rules(known: List<&2, Nat>, d: Wr.Dec<List<&2, Nat>>) -> Maybe<&2, QsOpen>:
  match d:
    case Wr.Got{xs, s}:
      read_open.end(Wr.end(s), known, xs)
    case Wr.Bad{}:
      None{}

def read_open.known(d: Wr.Dec<List<&2, Nat>>) -> Maybe<&2, QsOpen>:
  match d:
    case Wr.Got{known, s}:
      read_open.rules(known, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      None{}

# the open s spells: the known directives and the rules
def read_open(s: String) -> Maybe<&2, QsOpen>:
  read_open.known(Wr.get_list(~Nat, ~Wr.get_nat, s))

# the lookup four Nats spell
def read_four(xs: List<&2, Nat>) -> Maybe<&2, QsLookup>:
  match xs:
    case Nil{}:
      None{}
    case f <> a:
      match a:
        case Nil{}:
          None{}
        case m <> b:
          match b:
            case Nil{}:
              None{}
            case h <> c:
              match c:
                case Nil{}:
                  None{}
                case d <> e:
                  match e:
                    case Nil{}:
                      Some{QsLookup{If.Query{f, m, h}, d}}
                    case x <> y:
                      None{}

def read_lookup.end(whole: Bool, xs: List<&2, Nat>) -> Maybe<&2, QsLookup>:
  match whole:
    case True{}:
      read_four(xs)
    case False{}:
      None{}

def read_lookup.got(d: Wr.Dec<List<&2, Nat>>) -> Maybe<&2, QsLookup>:
  match d:
    case Wr.Got{xs, s}:
      read_lookup.end(Wr.end(s), xs)
    case Wr.Bad{}:
      None{}

# the lookup s spells
def read_lookup(s: String) -> Maybe<&2, QsLookup>:
  read_lookup.got(Wr.get_list(~Nat, ~Wr.get_nat, s))

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

# LAW quirks_faults_iff_rejected: every verdict is fine exactly when the rulebook compiles
# EXCLUDES: a rejection with no reason, a reason given for a rulebook that
#   compiles
law quirks_faults_iff_rejected:
  for +known: List<&2, Nat>
  for +rs: List<&2, If.Rule>
  {qs_all_fine(rs, known) == If.compiles(known, rs) : Bool}

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

# LAW quirks_open_malformed: an open that is not exactly an open Rust writes answers exactly the
# error form 'E ' then "quirks: malformed rulebook", and keeps no rulebook
# EXCLUDES: a default rulebook, input left over or a layer tag past 2 read
law quirks_open_malformed:
  for +s: String
  for no: {read_open(s) == None{} : Maybe<&2, QsOpen>}
  {FQ.open(s) == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String}

# LAW quirks_lookup_malformed: a lookup that is not exactly four Nats answers exactly the error
# form 'E ' then "quirks: malformed lookup", and keeps the rulebook
# EXCLUDES: a guessed query, a rulebook dropped or changed by a bad lookup
law quirks_lookup_malformed:
  for +rs: List<&2, If.Rule>
  for +s: String
  for no: {read_lookup(s) == None{} : Maybe<&2, QsLookup>}
  {FQ.step(FQ.Book{rs}, s) == (FQ.Book{rs}, SCon{'E', SCon{' ', "quirks: malformed lookup"}}) : FQ.St & String}

# LAW quirks_shut_refuses: a rulebook that was not kept answers every lookup with exactly the
# error form 'E ' then "quirks: no rulebook"
# EXCLUDES: answers from a rulebook that does not compile, or from none
law quirks_shut_refuses:
  for +s: String
  {FQ.step(FQ.Shut{}, s) == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: no rulebook"}}) : FQ.St & String}

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

# LAW quirks_malformed_example: witness: malformed inputs exist (a layer tag of 3, a rule cut
# short, input left over, a lookup of three Nats)
# EXCLUDES: a vacuous quirks_open_malformed or quirks_lookup_malformed
law quirks_malformed_example:
  {[read_open("1,0,4,3,1,0,5,"), read_open("1,0,3,0,1,0,"), read_open("1,0,0,x")] == [None{}, None{}, None{}] : List<&2, Maybe<&2, QsOpen>>} & {read_lookup("3,1,2,0,") == None{} : Maybe<&2, QsLookup>}

# LAW quirks_known_exact: the model's is_known (which quirk_known_when_some reads) says Known
# exactly for a Known answer
# EXCLUDES: an is_known that always says yes, making quirk_known_when_some
#   vacuous (a mutant's)
law quirks_known_exact:
  for a: If.Ans
  {If.is_known(a) == qs_known(a) : Bool}

# LAW quirks_premises_example: witness: an open and a lookup that fit the wire exist, and an
# open with a layer tag of 3 reads as no open
# EXCLUDES: a vacuous quirks_open_answers, quirks_lookup_answers or
#   quirks_open_malformed
law quirks_premises_example:
  {open_fits([0n], [If.Rule{If.Host{}, 1n, 0n, 5n}]) == True{} : Bool} & {lookup_fits(If.Query{1n, 2n, 3n}, 0n) == True{} : Bool} & {read_open("1,0,4,3,1,0,5,") == None{} : Maybe<&2, QsOpen>}

# LAW quirks_rule_terms_exact: the rank, directive and value the model's laws read of a rule
# are the spec's: host over model over family
# EXCLUDES: layers ranked in another order (a fresh adversary's host ranked
#   below family and model passed quirk_highest_wins, whose rank the code
#   defined)
law quirks_rule_terms_exact:
  for r: If.Rule
  {If.Rule.rank(r) == qs_rule_rank(r) : Nat} & {If.Rule.dir(r) == qs_dir(r) : Nat} & {If.Rule.val(r) == qs_val(r) : Nat}

# LAW quirks_applies_exact: a rule applies to a query exactly when its target is the one
# the query names at its layer
# EXCLUDES: a rule applied for another layer's target, or never applied
law quirks_applies_exact:
  for q: If.Query
  for r: If.Rule
  {If.applies(q, r) == qs_applies(q, r) : Bool}

# LAW quirks_any_at_exact: the model's "some rule applies at precedence k or above" is the
# spec's
# EXCLUDES: quirk_highest_wins or quirk_unknown_when_none made vacuous or
#   wrong by a test that ignores rules, layers or the directive
law quirks_any_at_exact:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for +k: Nat
  {If.any_at(rs, q, d, k) == qs_any_at(rs, q, d, k) : Bool}

# LAW quirks_host_wins_example: anchor: with a family, a model and a host rule that all apply,
# the host rule answers
# EXCLUDES: a lower layer winning over a host rule
law quirks_host_wins_example:
  {FQ.step(FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}, If.Rule{If.Mod{}, 2n, 0n, 7n}, If.Rule{If.Host{}, 3n, 0n, 9n}]}, "4,1,2,3,0,") == (FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}, If.Rule{If.Mod{}, 2n, 0n, 7n}, If.Rule{If.Host{}, 3n, 0n, 9n}]}, "1,9,") : FQ.St & String} & {FQ.open("1,0,12,0,1,0,5,1,2,0,7,2,3,0,9,") == (FQ.Book{[If.Rule{If.Fam{}, 1n, 0n, 5n}, If.Rule{If.Mod{}, 2n, 0n, 7n}, If.Rule{If.Host{}, 3n, 0n, 9n}]}, "T3,0,0,0,") : FQ.St & String}
