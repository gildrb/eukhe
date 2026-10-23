# eukhe: lemmas the proofs of area tree share: bool

import Base
import ../../../bend/tree.bend as Tr
import ../../../laws/tree.bend as Tree
import ../../base/bool/and.bend as LBoolAnd
import ../../base/bool/misc.bend as LBoolMisc
import ./logic.bend as LALogic

def pt.or_l(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LBoolMisc.pt.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pt.or_r(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LBoolMisc.pt.absurd({b == False{} : Bool}, h)
    case False{}:
      h

def pt.or_tl(+a: Bool, +b: Bool, ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.or(_, b) == True{} : Bool}
  {==}

def pt.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def pt.flip(-a: Bool, h: {a == True{} : Bool}, g: {a == False{} : Bool}) -> Empty:
  LBoolMisc.pt.absurd(Empty, Equal.trans(Bool, True{}, a, False{}, Equal.sym(Bool, a, True{}, h), g))

def tree.pt.or_false_r(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pt.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# an or whose right side is false holds by its left side
def pt.or_l_true(a: Bool, +b: Bool, +h: {Bool.or(a, b) == True{} : Bool}, nb: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LALogic.pt.void({False{} == True{} : Bool}, pt.flip(b, h, nb))

# every node of pre is kept in b, or its key is gone
def pt.cov(pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +gone: List<&2, Nat>) -> Bool:
  match pre:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Bool.or(Tr.has(b, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.k(e))), pt.cov(rest, b, gone))

# every node of s hangs under the root, a node of pre, or a node before it
def pt.upl(s: List<&2, Tr.Ent>, +pre: List<&2, Tr.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Tr.ok(pre, Tr.Ent.k(e), Tr.Ent.p(e)), pt.upl(rest, List.append(&2, Tr.Ent, pre, [e])))

def pt.or_mono_elem(c: Bool, +g: List<&2, Nat>, +y: Nat, +x: Nat, h: {Bool.or(c, Tr.elem(g, x)) == True{} : Bool}) -> {Bool.or(c, Tr.elem(y <> g, x)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pt.or_tr(Nat.is_eq(y, x), Tr.elem(g, x), h)

def pt.cov_gone(A: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +g: List<&2, Nat>, +y: Nat, +ca: {pt.cov(A, b, g) == True{} : Bool}) -> {pt.cov(A, b, y <> g) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +i = Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(g, Tr.Ent.k(a)))
      LBoolAnd.tree.pt.and_t(Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(y <> g, Tr.Ent.k(a))), pt.cov(r, b, y <> g), pt.or_mono_elem(Tr.has(b, Tr.Ent.k(a)), g, y, Tr.Ent.k(a), LBoolAnd.tree.pt.and_l(i, pt.cov(r, b, g), ca)), pt.cov_gone(r, b, g, y, LBoolAnd.tree.pt.and_r(i, pt.cov(r, b, g), ca)))

# Rewind: still, minimal
# ----------------------

# b has the key of every node of s
def pt.allhas(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Tr.has(b, Tr.Ent.k(e)), pt.allhas(rest, b))

# Delete

# every key of gone is x or more
def tc.nall(gone: List<&2, Nat>, +x: Nat) -> Bool:
  match gone:
    case Nil{}:
      True{}
    case +g <> rest:
      Bool.and(Bool.not(Nat.is_lt(g, x)), tc.nall(rest, x))

# every node of s is above its parent
def tc.desc(s: List<&2, Tr.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), tc.desc(rest))

def tc.or_ff(a: Bool, b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      LBoolMisc.pt.absurd({Bool.or(True{}, b) == False{} : Bool}, ha)
    case False{}:
      hb

# every fork's largest parent key is at least each side's
def tc.mpok(m: Tr.KMap) -> Bool:
  match m:
    case Tr.KNil{}:
      True{}
    case Tr.KOne{e}:
      True{}
    case Tr.KFork{+mid, +mp, +l, +r}:
      Bool.and(tc.mpok(l), Bool.and(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))))

def tc.mpok_rest(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Bool.and(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))) == True{} : Bool}:
  LBoolAnd.tree.pt.and_r(tc.mpok(l), Bool.and(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))), h)

# every parent key of t is at most b
def tc.ple(t: List<&2, Tr.Ent>, +b: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(Nat.is_ge(b, Tr.Ent.p(e)), tc.ple(r, b))

# no key of t is x
def tc.nokey(t: List<&2, Tr.Ent>, +x: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), tc.nokey(r, x))

def tc.not_ff(b: Bool, h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.pt.absurd({False{} == True{} : Bool}, h)

def tc.or_fl(a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  pt.or_l(a, b, h)

# every key of gone is x, or below every key of s
def tc.gb(gone: List<&2, Nat>, +x: Nat, +s: List<&2, Tr.Ent>) -> Bool:
  match gone:
    case Nil{}:
      True{}
    case +z <> rest:
      Bool.and(Bool.or(Nat.is_eq(z, x), Tr.above(z, s)), tc.gb(rest, x, s))

# every key of ks is above k
def tc.gtall(ks: List<&2, Nat>, +k: Nat) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case +z <> rest:
      Bool.and(Nat.is_lt(k, z), tc.gtall(rest, k))

# The stack in the tree: order
# ----------------------------

# every key of t is less than m
def pd.lt_all(t: List<&2, Tr.Ent>, +m: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(Nat.is_lt(Tr.Ent.k(e), m), pd.lt_all(rest, m))

# the ops of a rewind
# ------------------

def tf.fit_l(+o: Tr.Op, -ops: List<&2, Tr.Op>, h: {Tree.tree.ops_fit(o <> ops) == True{} : Bool}) -> {Tree.tree.op_fits(o) == True{} : Bool}:
  LBoolAnd.wr_and_l(Tree.tree.op_fits(o), Tree.tree.ops_fit(ops), h)

def tf.fit_r(+o: Tr.Op, -ops: List<&2, Tr.Op>, h: {Tree.tree.ops_fit(o <> ops) == True{} : Bool}) -> {Tree.tree.ops_fit(ops) == True{} : Bool}:
  LBoolAnd.wr_and_r(Tree.tree.op_fits(o), Tree.tree.ops_fit(ops), h)
