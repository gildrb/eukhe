# eukhe: lemmas the proofs of two or more areas share: bool/and

import Base
import ../../../bend/tree.bend as Tr
import ./misc.bend as LBoolMisc

def wn_and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      LBoolMisc.wn_absurd({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def wn_and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      LBoolMisc.wn_absurd({b == True{} : Bool}, e)
    case True{}:
      e

def wn_and_intro(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool})
  -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# Bool.and == True splits
def wr_and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      {==}

def wr_and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      LBoolMisc.wr_absurd({b == True{} : Bool}, e)
    case True{}:
      e

def cb_and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      LBoolMisc.cb_absurd({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def cb_and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      LBoolMisc.cb_absurd({b == True{} : Bool}, e)
    case True{}:
      e

def cb_and_intro(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def pf.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      LBoolMisc.pf.absurd_ft({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def pf.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      LBoolMisc.pf.absurd_ft({b == True{} : Bool}, e)
    case True{}:
      e

def tree.pt.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.tree.pt.absurdF({False{} == True{} : Bool}, h)

def tree.pt.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LBoolMisc.tree.pt.absurdF({b == True{} : Bool}, h)

def tree.pt.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def tc.bst_rest(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LBoolMisc.tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Bool.and(LBoolMisc.tc.bst(r), Bool.and(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid))) == True{} : Bool}:
  tree.pt.and_r(LBoolMisc.tc.bst(l), Bool.and(LBoolMisc.tc.bst(r), Bool.and(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid))), h)

def tc.lt_tail(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {LBoolMisc.tc.lt(e <> r, b) == True{} : Bool}) -> {LBoolMisc.tc.lt(r, b) == True{} : Bool}:
  tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), b), LBoolMisc.tc.lt(r, b), h)

def tc.ge_tail(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {LBoolMisc.tc.ge(e <> r, b) == True{} : Bool}) -> {LBoolMisc.tc.ge(r, b) == True{} : Bool}:
  tree.pt.and_r(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), LBoolMisc.tc.ge(r, b), h)

def pq.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.pq.absurdF({False{} == True{} : Bool}, h)

def pq.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LBoolMisc.pq.absurdF({b == True{} : Bool}, h)

def pl.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.tools.pl.absurdF({False{} == True{} : Bool}, h)

def pl.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LBoolMisc.tools.pl.absurdF({b == True{} : Bool}, h)

def semver.ps.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.semver.ps.absurdF({False{} == True{} : Bool}, h)

def semver.ps.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LBoolMisc.semver.ps.absurdF({b == True{} : Bool}, h)

def ppr.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.ppr.absurdF({False{} == True{} : Bool}, h)

def ppr.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LBoolMisc.ppr.absurdF({b == True{} : Bool}, h)

def supervisor.ps.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LBoolMisc.supervisor.ps.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

def pu.and_t(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def rp.and_tt(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LBoolMisc.rp.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

def rp.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.rp.absurdF({False{} == True{} : Bool}, e)

def rp.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LBoolMisc.rp.absurdF({b == True{} : Bool}, e)

def documents.ps.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}
