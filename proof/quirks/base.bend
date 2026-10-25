# eukhe: lemmas the proofs of area quirks share

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/quirks.bend as Quirks

# Logic
# -----

def qp.MD(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# Some is never None
def qp.some_none(-A: Data, -a: A, -G: Type, e: {Some{a} == None{} : Maybe<&2, A>}) -> G:
  %Equal.sym(Maybe<&2, A>, Some{a}, None{}, e) : qp.MD(A, _, G)
  Unit{}

def qp.BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# True is never False
def qp.true_false(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %Equal.sym(Bool, True{}, False{}, e) : qp.BD(_, G)
  Unit{}

# a three-way and of known, no clash and the rest, as the model folds it
def qp.and4(a: Bool, b: Bool, c: Bool, d: Bool) -> {Bool.and(Bool.and(a, Bool.not(c)), Bool.and(b, Bool.not(d))) == Bool.and(Bool.and(a, b), Bool.not(Bool.or(c, d))) : Bool}:
  match a b c d:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

# Rules
# -----

# the model's layer test is the spec's
def qp.lay_eq(a: If.Lay, b: If.Lay) -> {If.Lay.eq(a, b) == Quirks.qs_lay_same(a, b) : Bool}:
  match a b:
    case If.Fam{} If.Fam{}:
      {==}
    case If.Fam{} If.Mod{}:
      {==}
    case If.Fam{} If.Host{}:
      {==}
    case If.Mod{} If.Fam{}:
      {==}
    case If.Mod{} If.Mod{}:
      {==}
    case If.Mod{} If.Host{}:
      {==}
    case If.Host{} If.Fam{}:
      {==}
    case If.Host{} If.Mod{}:
      {==}
    case If.Host{} If.Host{}:
      {==}

# the model's clash is the spec's
def qp.clash_eq(a: If.Rule, b: If.Rule) -> {If.clash(a, b) == Quirks.qs_clash(a, b) : Bool}:
  match a b:
    case If.Rule{+la, ta, da, va} If.Rule{+lb, tb, db, vb}:
      %qp.lay_eq(la, lb) : {If.clash(If.Rule{la, ta, da, va}, If.Rule{lb, tb, db, vb}) == Bool.and(_, Bool.and(Nat.is_eq(ta, tb), Bool.and(Nat.is_eq(da, db), Bool.not(Nat.is_eq(va, vb))))) : Bool}
      {==}

# a step of the model's scan, for any test b of its first rule
def qp.partner_pick(b: Bool, s: If.Rule, rest: List<&2, If.Rule>, +r: If.Rule, +i: Nat) -> {If.clash.go(s <> rest, r, i, b) == Quirks.qs_pick(b, i, If.clash.go(rest, r, 1n+i, If.clash.head(r, rest))) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's first clash is the spec's
def qp.partner(rs: List<&2, If.Rule>, +r: If.Rule, +i: Nat) -> {If.clash.go(rs, r, i, If.clash.head(r, rs)) == Quirks.qs_partner(rs, r, i) : Maybe<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case +s <> +rest:
      %qp.partner(rest, r, 1n+i) : {If.clash.go(s <> rest, r, i, If.clash(r, s)) == Quirks.qs_pick(Quirks.qs_clash(r, s), i, _) : Maybe<&2, Nat>}
      %qp.clash_eq(r, s) : {If.clash.go(s <> rest, r, i, If.clash(r, s)) == Quirks.qs_pick(_, i, If.clash.go(rest, r, 1n+i, If.clash.head(r, rest))) : Maybe<&2, Nat>}
      qp.partner_pick(If.clash(r, s), s, rest, r, i)

# no first clash exactly when r clashes with no rule of rs, from any index
def qp.none_pick(b: Bool, +i: Nat, +m: Maybe<&2, Nat>, +c: Bool, ih: {Maybe.is_none(&2, Nat, m) == Bool.not(c) : Bool}) -> {Maybe.is_none(&2, Nat, Quirks.qs_pick(b, i, m)) == Bool.not(Bool.or(b, c)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def qp.partner_none(rs: List<&2, If.Rule>, +r: If.Rule, +i: Nat) -> {Maybe.is_none(&2, Nat, Quirks.qs_partner(rs, r, i)) == Bool.not(If.clashes(r, rs)) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +s <> +rest:
      %qp.clash_eq(r, s) : {Maybe.is_none(&2, Nat, Quirks.qs_pick(_, i, Quirks.qs_partner(rest, r, 1n+i))) == Bool.not(Bool.or(If.clash(r, s), If.clashes(r, rest))) : Bool}
      qp.none_pick(If.clash(r, s), i, Quirks.qs_partner(rest, r, 1n+i), If.clashes(r, rest), qp.partner_none(rest, r, 1n+i))

# the model's membership is the spec's
def qp.mem(ds: List<&2, Nat>, +d: Nat) -> {If.elem(ds, d) == Quirks.qs_mem(ds, d) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case e <> rest:
      %qp.mem(rest, d) : {If.elem(e <> rest, d) == Bool.or(Nat.is_eq(e, d), _) : Bool}
      {==}

def qp.dir(r: If.Rule) -> {If.Rule.dir(r) == Quirks.qs_dir(r) : Nat}:
  match r:
    case If.Rule{l, t, d, v}:
      {==}

# the spec's verdicts compile exactly when the model compiles
def qp.all_fine(rs: List<&2, If.Rule>, +known: List<&2, Nat>) -> {Quirks.qs_all_fine(rs, known) == If.compiles(known, rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %Equal.sym(Bool, Maybe.is_none(&2, Nat, Quirks.qs_partner(rest, r, 0n)), Bool.not(If.clashes(r, rest)), qp.partner_none(rest, r, 0n)) : {Bool.and(Bool.and(Quirks.qs_mem(known, Quirks.qs_dir(r)), _), Quirks.qs_all_fine(rest, known)) == If.compiles(known, r <> rest) : Bool}
      %Equal.sym(Bool, Quirks.qs_all_fine(rest, known), If.compiles(known, rest), qp.all_fine(rest, known)) : {Bool.and(Bool.and(Quirks.qs_mem(known, Quirks.qs_dir(r)), Bool.not(If.clashes(r, rest))), _) == If.compiles(known, r <> rest) : Bool}
      %qp.dir(r) : {Bool.and(Bool.and(Quirks.qs_mem(known, _), Bool.not(If.clashes(r, rest))), If.compiles(known, rest)) == If.compiles(known, r <> rest) : Bool}
      %qp.mem(known, If.Rule.dir(r)) : {Bool.and(Bool.and(_, Bool.not(If.clashes(r, rest))), If.compiles(known, rest)) == If.compiles(known, r <> rest) : Bool}
      qp.and4(If.elem(known, If.Rule.dir(r)), If.known_all(rest, known), If.clashes(r, rest), If.ambiguous(rest))

# The entry
# ---------

def qp.verdict_fine(k: Bool, c: Maybe<&2, Nat>) -> {If.Verdict.fine(If.verdict(k, c)) == Bool.and(k, Maybe.is_none(&2, Nat, c)) : Bool}:
  match k:
    case False{}:
      {==}
    case True{}:
      match c:
        case None{}:
          {==}
        case Some{j}:
          {==}

# the entry's verdicts are all fine exactly when the spec's are
def qp.fine_all(rs: List<&2, If.Rule>, +known: List<&2, Nat>, +i: Nat) -> {If.fine_all(If.verdicts.go(rs, known, i)) == Quirks.qs_all_fine(rs, known) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %qp.fine_all(rest, known, 1n+i) : {If.fine_all(If.verdicts.go(r <> rest, known, i)) == Bool.and(Bool.and(Quirks.qs_mem(known, Quirks.qs_dir(r)), Maybe.is_none(&2, Nat, Quirks.qs_partner(rest, r, 0n))), _) : Bool}
      %qp.dir(r) : {If.fine_all(If.verdicts.go(r <> rest, known, i)) == Bool.and(Bool.and(Quirks.qs_mem(known, _), Maybe.is_none(&2, Nat, Quirks.qs_partner(rest, r, 0n))), If.fine_all(If.verdicts.go(rest, known, 1n+i))) : Bool}
      %qp.mem(known, If.Rule.dir(r)) : {If.fine_all(If.verdicts.go(r <> rest, known, i)) == Bool.and(Bool.and(_, Maybe.is_none(&2, Nat, Quirks.qs_partner(rest, r, 0n))), If.fine_all(If.verdicts.go(rest, known, 1n+i))) : Bool}
      %Equal.sym(Bool, Maybe.is_none(&2, Nat, Quirks.qs_partner(rest, r, 0n)), Bool.not(If.clashes(r, rest)), qp.partner_none(rest, r, 0n)) : {If.fine_all(If.verdicts.go(r <> rest, known, i)) == Bool.and(Bool.and(If.elem(known, If.Rule.dir(r)), _), If.fine_all(If.verdicts.go(rest, known, 1n+i))) : Bool}
      %qp.partner_none(rest, r, 1n+i) : {If.fine_all(If.verdicts.go(r <> rest, known, i)) == Bool.and(Bool.and(If.elem(known, If.Rule.dir(r)), _), If.fine_all(If.verdicts.go(rest, known, 1n+i))) : Bool}
      %qp.partner(rest, r, 1n+i) : {If.fine_all(If.verdicts.go(r <> rest, known, i)) == Bool.and(Bool.and(If.elem(known, If.Rule.dir(r)), Maybe.is_none(&2, Nat, _)), If.fine_all(If.verdicts.go(rest, known, 1n+i))) : Bool}
      %qp.verdict_fine(If.elem(known, If.Rule.dir(r)), If.clash.go(rest, r, 1n+i, If.clash.head(r, rest))) : {If.fine_all(If.verdicts.go(r <> rest, known, i)) == Bool.and(_, If.fine_all(If.verdicts.go(rest, known, 1n+i))) : Bool}
      {==}

# the entry spells a verdict as the spec does
def qp.put_verdict(k: Bool, c: Maybe<&2, Nat>, rest: String) -> {FQ.put_verdict(If.verdict(k, c), rest) == Quirks.spell_verdict(k, c, rest) : String}:
  match k:
    case False{}:
      {==}
    case True{}:
      match c:
        case None{}:
          {==}
        case Some{j}:
          {==}

# the items of a list of verdicts, then rest
def qp.items(vs: List<&2, If.Verdict>, rest: String) -> String:
  match vs:
    case Nil{}:
      rest
    case v <> t:
      FQ.put_verdict(v, qp.items(t, rest))

def qp.put_go(vs: List<&2, If.Verdict>, -rest: String) ->
  {Wr.put_list.go(~If.Verdict, ~FQ.put_verdict, vs, rest) == (List.length(&2, If.Verdict, vs), qp.items(vs, rest)) : Nat & String}:
  match vs:
    case Nil{}:
      {==}
    case v <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~If.Verdict, ~FQ.put_verdict, t, rest), (List.length(&2, If.Verdict, t), qp.items(t, rest)), qp.put_go(t, rest)) : {Wr.put_list.step(~If.Verdict, ~FQ.put_verdict, v, _) == (1n+List.length(&2, If.Verdict, t), FQ.put_verdict(v, qp.items(t, rest))) : Nat & String}
      {==}

# a list of verdicts is its count, then its items
def qp.put(+vs: List<&2, If.Verdict>, -rest: String) ->
  {Wr.put_list(~If.Verdict, ~FQ.put_verdict, vs, rest) == Wr.put_nat(List.length(&2, If.Verdict, vs), qp.items(vs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~If.Verdict, ~FQ.put_verdict, vs, rest), (List.length(&2, If.Verdict, vs), qp.items(vs, rest)), qp.put_go(vs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, If.Verdict, vs), qp.items(vs, rest)) : String}
  {==}

# one verdict per rule
def qp.len(rs: List<&2, If.Rule>, +known: List<&2, Nat>, +i: Nat) -> {List.length(&2, If.Verdict, If.verdicts.go(rs, known, i)) == List.length(&2, If.Rule, rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %qp.len(rest, known, 1n+i) : {List.length(&2, If.Verdict, If.verdicts.go(r <> rest, known, i)) == 1n+_ : Nat}
      {==}

# the entry's verdict items are the spec's
def qp.items_eq(rs: List<&2, If.Rule>, +known: List<&2, Nat>, +i: Nat) -> {qp.items(If.verdicts.go(rs, known, i), "") == Quirks.spell_verdicts.items(rs, known, i) : String}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %qp.items_eq(rest, known, 1n+i) : {qp.items(If.verdicts.go(r <> rest, known, i), "") == Quirks.spell_verdict(Quirks.qs_mem(known, Quirks.qs_dir(r)), Quirks.qs_partner(rest, r, 1n+i), _) : String}
      %qp.partner(rest, r, 1n+i) : {qp.items(If.verdicts.go(r <> rest, known, i), "") == Quirks.spell_verdict(Quirks.qs_mem(known, Quirks.qs_dir(r)), _, qp.items(If.verdicts.go(rest, known, 1n+i), "")) : String}
      %qp.dir(r) : {qp.items(If.verdicts.go(r <> rest, known, i), "") == Quirks.spell_verdict(Quirks.qs_mem(known, _), If.clash.go(rest, r, 1n+i, If.clash.head(r, rest)), qp.items(If.verdicts.go(rest, known, 1n+i), "")) : String}
      %qp.mem(known, If.Rule.dir(r)) : {qp.items(If.verdicts.go(r <> rest, known, i), "") == Quirks.spell_verdict(_, If.clash.go(rest, r, 1n+i, If.clash.head(r, rest)), qp.items(If.verdicts.go(rest, known, 1n+i), "")) : String}
      %qp.put_verdict(If.elem(known, If.Rule.dir(r)), If.clash.go(rest, r, 1n+i, If.clash.head(r, rest)), qp.items(If.verdicts.go(rest, known, 1n+i), "")) : {qp.items(If.verdicts.go(r <> rest, known, i), "") == _ : String}
      {==}

# the entry spells the verdicts as the spec does
def qp.verdicts(+known: List<&2, Nat>, +rs: List<&2, If.Rule>) -> {Wr.put_list(~If.Verdict, ~FQ.put_verdict, If.verdicts(known, rs), "") == Quirks.spell_verdicts(known, rs) : String}:
  %Equal.sym(String, Wr.put_list(~If.Verdict, ~FQ.put_verdict, If.verdicts(known, rs), ""), Wr.put_nat(List.length(&2, If.Verdict, If.verdicts(known, rs)), qp.items(If.verdicts(known, rs), "")), qp.put(If.verdicts(known, rs), "")) : {_ == Quirks.spell_verdicts(known, rs) : String}
  %qp.items_eq(rs, known, 0n) : {Wr.put_nat(List.length(&2, If.Verdict, If.verdicts(known, rs)), qp.items(If.verdicts(known, rs), "")) == Wr.put_nat(List.length(&2, If.Rule, rs), _) : String}
  %qp.len(rs, known, 0n) : {Wr.put_nat(List.length(&2, If.Verdict, If.verdicts(known, rs)), qp.items(If.verdicts(known, rs), "")) == Wr.put_nat(_, qp.items(If.verdicts(known, rs), "")) : String}
  {==}

def qp.lay_flat(l: If.Lay) -> {FQ.lay(Quirks.qs_lay(l)) == Some{l} : Maybe<&2, If.Lay>}:
  match l:
    case If.Fam{}:
      {==}
    case If.Mod{}:
      {==}
    case If.Host{}:
      {==}

# the rules read back from their flat list
def qp.rules(rs: List<&2, If.Rule>) -> {FQ.rules(Quirks.qs_flat(rs)) == Some{rs} : Maybe<&2, List<&2, If.Rule>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case If.Rule{+l, t, d, v}:
          %Equal.sym(Maybe<&2, List<&2, If.Rule>>, FQ.rules(Quirks.qs_flat(rest)), Some{rest}, qp.rules(rest)) : {FQ.rules.cons(FQ.lay(Quirks.qs_lay(l)), t, d, v, _) == Some{If.Rule{l, t, d, v} <> rest} : Maybe<&2, List<&2, If.Rule>>}
          %Equal.sym(Maybe<&2, If.Lay>, FQ.lay(Quirks.qs_lay(l)), Some{l}, qp.lay_flat(l)) : {FQ.rules.cons(_, t, d, v, Some{rest}) == Some{If.Rule{l, t, d, v} <> rest} : Maybe<&2, List<&2, If.Rule>>}
          {==}

def qp.lay_read(n: Nat) -> {FQ.lay(n) == Quirks.read_lay(n) : Maybe<&2, If.Lay>}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+p:
      {==}

def qp.cons_read(m: Maybe<&2, If.Lay>, t: Nat, d: Nat, v: Nat, r: Maybe<&2, List<&2, If.Rule>>) -> {FQ.rules.cons(m, t, d, v, r) == Quirks.read_rules.cons(m, t, d, v, r) : Maybe<&2, List<&2, If.Rule>>}:
  match m:
    case None{}:
      {==}
    case Some{l}:
      match r:
        case None{}:
          {==}
        case Some{rs}:
          {==}

# the entry reads rules as the spec's reader does
def qp.rules_read(xs: List<&2, Nat>) -> {FQ.rules(xs) == Quirks.read_rules(xs) : Maybe<&2, List<&2, If.Rule>>}:
  match xs:
    case Nil{}:
      {==}
    case +l <> a:
      match a:
        case Nil{}:
          {==}
        case +t <> b:
          match b:
            case Nil{}:
              {==}
            case +d <> c:
              match c:
                case Nil{}:
                  {==}
                case +v <> +rest:
                  %qp.rules_read(rest) : {FQ.rules(l <> t <> d <> v <> rest) == Quirks.read_rules.cons(Quirks.read_lay(l), t, d, v, _) : Maybe<&2, List<&2, If.Rule>>}
                  %qp.lay_read(l) : {FQ.rules(l <> t <> d <> v <> rest) == Quirks.read_rules.cons(_, t, d, v, FQ.rules(rest)) : Maybe<&2, List<&2, If.Rule>>}
                  qp.cons_read(FQ.lay(l), t, d, v, FQ.rules(rest))

# a lookup's answer, spelled
def qp.ans(a: If.Ans) -> {FQ.put_ans(a, "") == Quirks.spell_ans(a) : String}:
  match a:
    case If.Unknown{}:
      {==}
    case If.Known{v}:
      {==}

# an open's reply, for either verdict of the compiler
def qp.reply(b: Bool, rs: List<&2, If.Rule>, vs: List<&2, If.Verdict>) -> {FQ.open.reply(b, rs, vs) == (Quirks.qs_kept(b, rs), Wr.put_bool(b, Wr.put_list(~If.Verdict, ~FQ.put_verdict, vs, ""))) : FQ.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
