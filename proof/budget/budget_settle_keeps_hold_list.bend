# eukhe: the proof of LAW budget_settle_keeps_hold_list
#
# PROOF: the holds are xs, the hold under the id, ys, so the id is held
# (bkl.has_mid) and the settlement leaves the code's others of them
# (BS.bs.open). The others drop exactly the holds under the id: none in
# xs (before) or ys (after), the one between them, so xs then ys stay
# (bkl.others_mid, induction on xs; bkl.others_none, induction on ys).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/settle.bend as BS

def bkl.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      bkl.eq_refl(p)

def bkl.or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bkl.or_false_r(b: Bool, -c: Bool, e: {Bool.or(b, c) == False{} : Bool}) -> {c == False{} : Bool}:
  match b:
    case True{}:
      BS.bs.absurd_tf({c == False{} : Bool}, e)
    case False{}:
      e

# the holds xs, the hold under the id, ys hold the id
def bkl.has_mid(+id: Nat, +x: B.Amt, xs: List<&2, B.Hold>, +ys: List<&2, B.Hold>) -> {S.has(id, List.append(&2, B.Hold, xs, B.Hold{id, x} <> ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(id, id), True{}, bkl.eq_refl(id)) : {Bool.or(_, S.has(id, ys)) == True{} : Bool}
      {==}
    case Con{h, t}:
      match h:
        case B.Hold{i, y}:
          %Equal.sym(Bool, S.has(id, List.append(&2, B.Hold, t, B.Hold{id, x} <> ys)), True{}, bkl.has_mid(id, x, t, ys)) : {Bool.or(Nat.is_eq(i, id), _) == True{} : Bool}
          bkl.or_true(Nat.is_eq(i, id))

def bkl.keep_none(same: Bool, -id: Nat, -i: Nat, -y: B.Amt, -r: List<&2, B.Hold>, -t: List<&2, B.Hold>, -k: List<&2, B.Hold>, e: {Bool.or(same, S.has(id, k)) == False{} : Bool}, ih: {r == t : List<&2, B.Hold>}) -> {B.others.keep(same, B.Hold{i, y}, r) == B.Hold{i, y} <> t : List<&2, B.Hold>}:
  match same:
    case True{}:
      BS.bs.absurd_tf({r == B.Hold{i, y} <> t : List<&2, B.Hold>}, e)
    case False{}:
      %Equal.sym(List<&2, B.Hold>, r, t, ih) : {B.Hold{i, y} <> _ == B.Hold{i, y} <> t : List<&2, B.Hold>}
      {==}

# holds that do not hold the id are all the others of the id
def bkl.others_none(+id: Nat, hs: List<&2, B.Hold>, +e: {S.has(id, hs) == False{} : Bool}) -> {B.others(id, hs) == hs : List<&2, B.Hold>}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      match h:
        case B.Hold{+i, +y}:
          bkl.keep_none(Nat.is_eq(i, id), id, i, y, B.others(id, t), t, t, e, bkl.others_none(id, t, bkl.or_false_r(Nat.is_eq(i, id), S.has(id, t), e)))

# the others of the id in xs, the hold under the id, ys are xs then ys
def bkl.others_mid(+id: Nat, +x: B.Amt, xs: List<&2, B.Hold>, +ys: List<&2, B.Hold>, +before: {S.has(id, xs) == False{} : Bool}, after: {S.has(id, ys) == False{} : Bool}) -> {B.others(id, List.append(&2, B.Hold, xs, B.Hold{id, x} <> ys)) == List.append(&2, B.Hold, xs, ys) : List<&2, B.Hold>}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(id, id), True{}, bkl.eq_refl(id)) : {B.others.keep(_, B.Hold{id, x}, B.others(id, ys)) == ys : List<&2, B.Hold>}
      bkl.others_none(id, ys, after)
    case Con{h, +t}:
      match h:
        case B.Hold{+i, +y}:
          bkl.keep_none(Nat.is_eq(i, id), id, i, y, B.others(id, List.append(&2, B.Hold, t, B.Hold{id, x} <> ys)), List.append(&2, B.Hold, t, ys), t, before, bkl.others_mid(id, x, t, ys, bkl.or_false_r(Nat.is_eq(i, id), S.has(id, t), before), after))

def Budget.budget_settle_keeps_hold_list(id, act, a, xs, x, ys, split, before, after):
  match a:
    case B.Acct{f, s, l, o, hs, u}:
      +mid = {List.append(&2, B.Hold, xs, B.Hold{id, x} <> ys) : List<&2, B.Hold>}
      %Equal.sym(List<&2, B.Hold>, hs, mid, split) : {S.holds(B.settle(id, act, B.Acct{f, s, l, o, _, u})) == List.append(&2, B.Hold, xs, ys) : List<&2, B.Hold>}
      %BS.bs.open(id, act, f, s, l, o, mid, u, bkl.has_mid(id, x, xs, ys)) : {S.holds(_) == List.append(&2, B.Hold, xs, ys) : List<&2, B.Hold>}
      bkl.others_mid(id, x, xs, ys, before, after)
