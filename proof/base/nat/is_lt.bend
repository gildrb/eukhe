# eukhe: lemmas the proofs of two or more areas share: nat/is_lt

import Base
import ../../../bend/tree.bend as Tr
import ../bool/and.bend as LBoolAnd
import ../bool/misc.bend as LBoolMisc
import ./is_eq.bend as LNatIsEq

# nothing is below 0
def pc.lt_zero(-A: Type, a: Nat, e: {Nat.is_lt(a, 0n) == True{} : Bool}) -> A:
  match a:
    case 0n:
      LBoolMisc.pc.absurd_ft(A, e)
    case 1n+p:
      LBoolMisc.pc.absurd_ft(A, e)

# (H2) The settle
# ---------------

def pc.lt_to_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      pc.lt_zero({Nat.is_le(p, 0n) == True{} : Bool}, p, e)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pc.lt_to_le(p, q, e)

def pc.le_lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case p q 0n:
      pc.lt_zero({Nat.is_lt(p, 0n) == True{} : Bool}, q, bc)
    case 0n q 1n+r:
      {==}
    case 1n+p 0n 1n+r:
      LBoolMisc.pc.absurd_ft({Nat.is_lt(1n+p, 1n+r) == True{} : Bool}, ab)
    case 1n+p 1n+q 1n+r:
      pc.le_lt_trans(p, q, r, ab, bc)

def pt.lt_irrefl(k: Nat) -> {Nat.is_lt(k, k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pt.lt_irrefl(p)

def pt.lt_zero(-A: Type, p: Nat, lt: {Nat.is_lt(p, 0n) == True{} : Bool}) -> A:
  match p:
    case 0n:
      LBoolMisc.tree.pt.absurdF(A, lt)
    case 1n+q:
      LBoolMisc.tree.pt.absurdF(A, lt)

# Numbers

def tc.lt_le(a: Nat, b: Nat, c: Nat, +ab: {Nat.is_lt(a, b) == True{} : Bool}, +cb: {Nat.is_lt(c, b) == False{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      LBoolMisc.tree.pt.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      LBoolMisc.pt.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, cb)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      tc.lt_le(p, q, r, ab, cb)

def tc.lt_asym(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      LBoolMisc.tree.pt.absurdF({Nat.is_lt(0n, a) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      tc.lt_asym(p, q, h)

def tc.lt_total(a: Nat, b: Nat, +nl: {Nat.is_lt(a, b) == False{} : Bool}, +ne: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      LBoolMisc.pt.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ne)
    case 0n 1n+q:
      LBoolMisc.pt.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, nl)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      tc.lt_total(p, q, nl, ne)

def tc.lt_head(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {LBoolMisc.tc.lt(e <> r, b) == True{} : Bool}) -> {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}:
  LBoolAnd.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), b), LBoolMisc.tc.lt(r, b), h)

def tc.ge_head(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {LBoolMisc.tc.ge(e <> r, b) == True{} : Bool}) -> {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}:
  LBoolMisc.pt.not_f(Nat.is_lt(Tr.Ent.k(e), b), LBoolAnd.tree.pt.and_l(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), LBoolMisc.tc.ge(r, b), h))

def tc.lt_cons(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}, +t: {LBoolMisc.tc.lt(r, b) == True{} : Bool}) -> {LBoolMisc.tc.lt(e <> r, b) == True{} : Bool}:
  LBoolAnd.tree.pt.and_t(Nat.is_lt(Tr.Ent.k(e), b), LBoolMisc.tc.lt(r, b), h, t)

def tc.ge_cons(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}, +t: {LBoolMisc.tc.ge(r, b) == True{} : Bool}) -> {LBoolMisc.tc.ge(e <> r, b) == True{} : Bool}:
  LBoolAnd.tree.pt.and_t(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), LBoolMisc.tc.ge(r, b), LBoolMisc.pt.not_t(Nat.is_lt(Tr.Ent.k(e), b), h), t)

# a key at or above b is no key of a list below b
def tc.lt_miss(+e: Tr.Ent, +b: Nat, +x: Nat, +lk: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == False{} : Bool}) -> {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}:
  LNatIsEq.pt.lt_ne(Tr.Ent.k(e), x, tc.lt_le(Tr.Ent.k(e), b, x, lk, xb))

# a key below b is no key of a list at or above b
def tc.ge_miss(+e: Tr.Ent, +b: Nat, +x: Nat, +ge: {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}:
  LNatIsEq.pt.lt_ne_r(x, Tr.Ent.k(e), tc.lt_le(x, b, Tr.Ent.k(e), xb, ge))

# ---- director ----

# proof_director: the Director stack laws (S5), about bend/director.bend.
#
# The bound: a decision under `above` layers keeps above + len(stack) at
# most cap (`pd.go_bounded`), with room telling whether above + len(s)
# is below cap (the whole stack's length, fixed for the decision). A
# layer that keeps its place keeps the length; a deferring layer, or one
# that leads and stays, goes back on the stack of the layers below
# (`pd.under_ok`), which is bounded under one more layer; a Leave, or a
# Lead that leaves, drops it (`pd.le_pred`); a Stack adds a layer only
# with room (`pd.push_ok`). Each loop step is one decision, and its kept
# stack (leads staying) is a decision too (`pd.tick_bounded`).
#
# The loop: `pd.ok(l, k)` says the loop has ended, or has fewer than k
# global steps left. A tick takes one step off (`pd.tick_ok`), so after k
# steps the loop has ended (`pd.ends_go`). An ended loop never changes.
#
# The rule: each verdict law unfolds decide.go once (`pd.on_top` matches
# the model's `under` with the spec's `dir_on_top`); each tick law settles
# one outcome (`pd.settle_cont0`, `pd.settle_hand`, `pd.settle_failed`).
#
# Leads: a decision where leads leave equals the decision on the verdicts
# with each Lead read as a Leave (`pd.leave_as`), one where they stay the
# decision with each read as a Defer (`pd.defer_as`), and both have the
# same outcome (`pd.out_stay`). A step that goes on does not read the kept
# stack (`pd.settle_on`); one that ends reads only the outcome and the
# kept stack (`pd.settle_end`).
#
# The tree: layer i of a stack (0 = bottom) is the nodes 2i + 1 and
# 2i + 2, appended after the nodes of the layers below. So every key of
# encode(s) is at most 2 len(s) (`pd.enc_lt`), the nodes stay sorted
# (`pd.enc_sorted`), and each kind node hangs under the root or the kind
# node of the layer below (`pd.parent_ok`), each budget node under its
# kind node (`pd.enc_rooted`). decode reads the pairs back in order
# (`pd.dec_go`), and a rewind reaches the encoded tree (proof_tree's
# `rewind_reaches`), so it restores the stack.

# Numbers
# -------

def pd.lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pd.lt_succ(p)

def pu.lt_zero_f(+q: Nat) -> {False{} == Nat.is_lt(q, 0n) : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      {==}

def rp.lt_succ(+last: Nat, +a: Nat, h: {Nat.is_lt(last, a) == True{} : Bool}) -> {Nat.is_lt(last, 1n+a) == True{} : Bool}:
  match last a:
    case 0n a:
      {==}
    case 1n+q 0n:
      LBoolMisc.rp.absurdF({Nat.is_lt(1n+q, 1n) == True{} : Bool}, h)
    case 1n+q 1n+p:
      rp.lt_succ(q, p, h)

def rp.lt_self(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      rp.lt_self(p)
