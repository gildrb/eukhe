# eukhe: lemmas the proofs of two or more areas share: bool

import Base
import ../../bend/tree.bend as Tr
import ../../laws/command/paths.bend as Command
import ./logic/bool.bend as LLogicBool
import ./logic/list.bend as LLogicList
import ./logic/logic.bend as LLogicLogic

def pf.or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      {==}

def pf.bool_cmp_refl(b: Bool) -> {EQ{} == Bool.cmp(b, b) : Cmp}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def pc.or_true(a: Bool) -> {Bool.or(True{}, a) == True{} : Bool}:
  {==}

def pt.not_t(+b: Bool, h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

# a true right side makes the or true
def ppr.or_r(a: Bool, +b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ppr.or_l(a: Bool, b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.ppr.absurdF({b == True{} : Bool}, h)

# Loading
# -------

# a head of a true or keeps it true: or(a, or(A, B)) from or(A, B), in the
# loaded place and in the reported place
def ppr.or_in_l(a: Bool, +x: Bool, +y: Bool, h: {Bool.or(x, y) == True{} : Bool}) -> {Bool.or(Bool.or(a, x), y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ppr.or_in_r(a: Bool, x: Bool, +y: Bool, h: {Bool.or(x, y) == True{} : Bool}) -> {Bool.or(x, Bool.or(a, y)) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      ppr.or_r(a, y, h)

# a true or with a false-making implication
def ppr.or_mono(a: Bool, +x: Bool, +y: Bool, f: {x == True{} : Bool} -> {y == True{} : Bool}, h: {Bool.or(a, x) == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

# Bools
# -----

def rp.or_l(a: Bool, -b: Bool, ea: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.rp.absurdF({Bool.or(False{}, b) == True{} : Bool}, ea)

def rp.or_r(a: Bool, -b: Bool, eb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      eb

def rp.not_of_false(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      LLogicLogic.rp.absurdT({Bool.not(True{}) == True{} : Bool}, e)
    case False{}:
      {==}

def rp.not_eq_move(+to: Nat, -a: Nat, -b: Nat, e: {a == b : Nat}, h: {Bool.not(Nat.is_eq(to, a)) == True{} : Bool}) -> {Bool.not(Nat.is_eq(to, b)) == True{} : Bool}:
  %e : {Bool.not(Nat.is_eq(to, _)) == True{} : Bool}
  h

def wn_and_intro(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool})
  -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def cb_and_intro(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def tree.pt.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def tc.bst_rest(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LLogicBool.tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Bool.and(LLogicBool.tc.bst(r), Bool.and(LLogicBool.tc.lt(Tr.KMap.read(l), mid), LLogicBool.tc.ge(Tr.KMap.read(r), mid))) == True{} : Bool}:
  LLogicBool.tree.pt.and_r(LLogicBool.tc.bst(l), Bool.and(LLogicBool.tc.bst(r), Bool.and(LLogicBool.tc.lt(Tr.KMap.read(l), mid), LLogicBool.tc.ge(Tr.KMap.read(r), mid))), h)

def supervisor.ps.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LLogicLogic.supervisor.ps.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

def pu.and_t(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def rp.and_tt(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LLogicLogic.rp.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

def documents.ps.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.lt_cons(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}, +t: {LLogicBool.tc.lt(r, b) == True{} : Bool}) -> {LLogicBool.tc.lt(e <> r, b) == True{} : Bool}:
  tree.pt.and_t(Nat.is_lt(Tr.Ent.k(e), b), LLogicBool.tc.lt(r, b), h, t)

def tc.ge_cons(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}, +t: {LLogicBool.tc.ge(r, b) == True{} : Bool}) -> {LLogicBool.tc.ge(e <> r, b) == True{} : Bool}:
  tree.pt.and_t(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), LLogicBool.tc.ge(r, b), pt.not_t(Nat.is_lt(Tr.Ent.k(e), b), h), t)

def cb_names_app_l(a: List<&2, List<&2, Nat>>, -b: List<&2, List<&2, Nat>>, +h: {Command.cmd_names_ok(List.append(&2, List<&2, Nat>, a, b)) == True{} : Bool}) -> {Command.cmd_names_ok(a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+w, +r}:
      cb_and_intro(Command.cmd_name_ok(w), Command.cmd_names_ok(r), LLogicBool.cb_and_l(Command.cmd_name_ok(w), Command.cmd_names_ok(List.append(&2, List<&2, Nat>, r, b)), h), cb_names_app_l(r, b, LLogicBool.cb_and_r(Command.cmd_name_ok(w), Command.cmd_names_ok(List.append(&2, List<&2, Nat>, r, b)), h)))

def tc.pair_lt(c: Bool, +a: Tr.Ent, +b: Tr.Ent, +B: Nat, +ha: {Nat.is_lt(Tr.Ent.k(a), B) == True{} : Bool}, +hb: {Nat.is_lt(Tr.Ent.k(b), B) == True{} : Bool}) -> {LLogicBool.tc.lt(LLogicList.tc.pair(c, a, b), B) == True{} : Bool}:
  match c:
    case True{}:
      tc.lt_cons(a, [b], B, ha, tc.lt_cons(b, Nil{}, B, hb, {==}))
    case False{}:
      tc.lt_cons(b, [a], B, hb, tc.lt_cons(a, Nil{}, B, ha, {==}))

def tc.pair_ge(c: Bool, +a: Tr.Ent, +b: Tr.Ent, +B: Nat, +ha: {Nat.is_lt(Tr.Ent.k(a), B) == False{} : Bool}, +hb: {Nat.is_lt(Tr.Ent.k(b), B) == False{} : Bool}) -> {LLogicBool.tc.ge(LLogicList.tc.pair(c, a, b), B) == True{} : Bool}:
  match c:
    case True{}:
      tc.ge_cons(a, [b], B, ha, tc.ge_cons(b, Nil{}, B, hb, {==}))
    case False{}:
      tc.ge_cons(b, [a], B, hb, tc.ge_cons(a, Nil{}, B, ha, {==}))

def tc.bst_r(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LLogicBool.tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {LLogicBool.tc.bst(r) == True{} : Bool}:
  LLogicBool.tree.pt.and_l(LLogicBool.tc.bst(r), Bool.and(LLogicBool.tc.lt(Tr.KMap.read(l), mid), LLogicBool.tc.ge(Tr.KMap.read(r), mid)), tc.bst_rest(mid, mp, l, r, h))
