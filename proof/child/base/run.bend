# eukhe: lemmas the proofs of the child step and run laws share
# (laws/child/run.bend)

import Base
import ../../../bend/child.bend as Ch
import ../../../laws/child/run.bend as ChildRun
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/nat.bend as LNat

# neither side of a false `or` holds
def pcr.or_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

def pcr.or_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pc.absurd_tf({b == False{} : Bool}, h)
    case False{}:
      h

# an inbox with no submission n has no fate for n
def pcr.none(inbox: List<&2, Ch.Sub>, +n: Nat, +h: {ChildRun.chr_has(inbox, n) == False{} : Bool}) -> {Ch.fate(inbox, n) == None{} : Maybe<&2, Ch.Fate>}:
  match inbox:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Ch.Sub{+i, f}:
          %Equal.sym(Bool, Nat.is_eq(i, n), False{}, pcr.or_l(Nat.is_eq(i, n), ChildRun.chr_has(rest, n), h)) : {Maybe.or(&2, Ch.Fate, Ch.fate.here(_, f), Ch.fate(rest, n)) == None{} : Maybe<&2, Ch.Fate>}
          pcr.none(rest, n, pcr.or_r(Nat.is_eq(i, n), ChildRun.chr_has(rest, n), h))

# the fate of n is that of the first submission n: no submission before
# it (pre) has id n
def pcr.finds(pre: List<&2, Ch.Sub>, +n: Nat, +f: Ch.Fate, +rest: List<&2, Ch.Sub>, +h: {ChildRun.chr_has(pre, n) == False{} : Bool}) -> {Ch.fate(List.append(&2, Ch.Sub, pre, Ch.Sub{n, f} <> rest), n) == Some{f} : Maybe<&2, Ch.Fate>}:
  match pre:
    case Nil{}:
      %LNat.child.pc.eq_refl(n) : {Maybe.or(&2, Ch.Fate, Ch.fate.here(Nat.is_eq(n, n), f), Ch.fate(rest, n)) == Maybe.or(&2, Ch.Fate, Ch.fate.here(_, f), Ch.fate(rest, n)) : Maybe<&2, Ch.Fate>}
      {==}
    case s <> p:
      match s:
        case Ch.Sub{+i, g}:
          %Equal.sym(Bool, Nat.is_eq(i, n), False{}, pcr.or_l(Nat.is_eq(i, n), ChildRun.chr_has(p, n), h)) : {Maybe.or(&2, Ch.Fate, Ch.fate.here(_, g), Ch.fate(List.append(&2, Ch.Sub, p, Ch.Sub{n, f} <> rest), n)) == Some{f} : Maybe<&2, Ch.Fate>}
          pcr.finds(p, n, f, rest, pcr.or_r(Nat.is_eq(i, n), ChildRun.chr_has(p, n), h))

# a parent's act settles each submission by itself
def pcr.act_app(xs: List<&2, Ch.Sub>, +ys: List<&2, Ch.Sub>, +a: Ch.Act) -> {Ch.act(List.append(&2, Ch.Sub, xs, ys), a) == List.append(&2, Ch.Sub, Ch.act(xs, a), Ch.act(ys, a)) : List<&2, Ch.Sub>}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      match x:
        case Ch.Sub{+i, +f}:
          %pcr.act_app(r, ys, a) : {Ch.Sub{i, Ch.Fate.act(a, i, f)} <> Ch.act(List.append(&2, Ch.Sub, r, ys), a) == Ch.Sub{i, Ch.Fate.act(a, i, f)} <> _ : List<&2, Ch.Sub>}
          {==}

# an act that names the id i gives a queued submission i the act's fate
def pcr.named(+i: Nat, +f: Ch.Fate) -> {[Ch.Sub{i, Ch.Act.hit(Nat.is_eq(i, i), f)}] == [Ch.Sub{i, f}] : List<&2, Ch.Sub>}:
  %LNat.child.pc.eq_refl(i) : {[Ch.Sub{i, Ch.Act.hit(Nat.is_eq(i, i), f)}] == [Ch.Sub{i, Ch.Act.hit(_, f)}] : List<&2, Ch.Sub>}
  {==}

# the read of report n on the newest submission, when it is n
def pcr.read_at(+n: Nat, +f: Ch.Fate, +rest: List<&2, Ch.Sub>) -> {Ch.read.at(Nat.is_eq(n, n), n, Ch.Sub{n, f}, rest) == Ch.Sub{n, Ch.Fate.read(f)} <> rest : List<&2, Ch.Sub>}:
  %LNat.child.pc.eq_refl(n) : {Ch.read.at(Nat.is_eq(n, n), n, Ch.Sub{n, f}, rest) == Ch.read.at(_, n, Ch.Sub{n, f}, rest) : List<&2, Ch.Sub>}
  {==}
