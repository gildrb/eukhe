# eukhe: lemmas the proofs of two or more areas share: logic/bool

import Base
import ../../../bend/replace.bend as Rp
import ../../../bend/retry.bend as R
import ../../../bend/semver.bend as Sv
import ../../../bend/tree.bend as Tr
import ./logic.bend as LLogicLogic

# ---- Nat.divmod by 10 ----

def wn_lt10(d: Nat) -> Bool:
  match d:
    case 0n:
      True{}
    case 1n:
      True{}
    case 2n:
      True{}
    case 3n:
      True{}
    case 4n:
      True{}
    case 5n:
      True{}
    case 6n:
      True{}
    case 7n:
      True{}
    case 8n:
      True{}
    case 9n:
      True{}
    case 10n+p:
      False{}

def wn_nz10(d: Nat) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+p:
      wn_lt10(1n+p)

# d <> t is a canonical digit list: digits below 10, the last (highest) not 0
def wn_okc(t: List<&2, Nat>, d: Nat) -> Bool:
  match t:
    case Nil{}:
      wn_nz10(d)
    case Con{e, u}:
      Bool.and(wn_lt10(d), wn_okc(u, e))

def wn_canon(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      wn_okc(t, d)

def pt.not_f(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LLogicLogic.tree.pt.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# Bounds

# every key of t is below b
def tc.lt(t: List<&2, Tr.Ent>, +b: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(Nat.is_lt(Tr.Ent.k(e), b), tc.lt(r, b))

# every key of t is b or more
def tc.ge(t: List<&2, Tr.Ent>, +b: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), tc.ge(r, b))

# a fork's left keys are below its split, its right keys at or above it
def tc.bst(m: Tr.KMap) -> Bool:
  match m:
    case Tr.KNil{}:
      True{}
    case Tr.KOne{e}:
      True{}
    case Tr.KFork{+mid, +mp, +l, +r}:
      Bool.and(tc.bst(l), Bool.and(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid))))

def ppr.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LLogicLogic.ppr.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# the most significant of the digits is not 0 (there is one)
def rk.nz(ds: List<&2, Sv.Dig>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> rest:
      Bool.not(Rp.zero(Rp.top(rest, d)))

def rk.not_true(b: Bool, f: {b == True{} : Bool} -> Empty) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, f({==}))
    case False{}:
      {==}

# (R3) The failover walk
# ----------------------

# what pick.fresh guarantees of its switch: no wait, not the last
# provider, not tried
def rp.fresh_ok(m: Maybe<&2, R.Switch>, +last: Nat, +ts: List<&2, R.Tried>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case R.Switch{+to, d}:
          Bool.and(Nat.is_eq(d, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))))

# Order
# -----

# last is no element of xs
def rp.notin(+last: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest))

# what pick.back guarantees of its switch: the wait is the backoff, and
# never less than its server's wait; not the last provider; the wait is
# positive and at most max
def rp.back_ok(m: Maybe<&2, R.Switch>, +last: Nat, +ts: List<&2, R.Tried>, +backoff: Nat, +max: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case R.Switch{+to, +d}:
          Bool.and(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, max))))

def wn_and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      LLogicLogic.wn_absurd({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def wn_and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      LLogicLogic.wn_absurd({b == True{} : Bool}, e)
    case True{}:
      e

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
      LLogicLogic.wr_absurd({b == True{} : Bool}, e)
    case True{}:
      e

def cb_and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      LLogicLogic.cb_absurd({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def cb_and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      LLogicLogic.cb_absurd({b == True{} : Bool}, e)
    case True{}:
      e

def pf.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      LLogicLogic.pf.absurd_ft({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def pf.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      LLogicLogic.pf.absurd_ft({b == True{} : Bool}, e)
    case True{}:
      e

def tree.pt.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.tree.pt.absurdF({False{} == True{} : Bool}, h)

def tree.pt.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LLogicLogic.tree.pt.absurdF({b == True{} : Bool}, h)

def tc.lt_tail(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {tc.lt(e <> r, b) == True{} : Bool}) -> {tc.lt(r, b) == True{} : Bool}:
  tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), b), tc.lt(r, b), h)

def tc.ge_tail(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {tc.ge(e <> r, b) == True{} : Bool}) -> {tc.ge(r, b) == True{} : Bool}:
  tree.pt.and_r(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), tc.ge(r, b), h)

def pq.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.pq.absurdF({False{} == True{} : Bool}, h)

def pq.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LLogicLogic.pq.absurdF({b == True{} : Bool}, h)

def pl.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.tools.pl.absurdF({False{} == True{} : Bool}, h)

def pl.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LLogicLogic.tools.pl.absurdF({b == True{} : Bool}, h)

def semver.ps.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.semver.ps.absurdF({False{} == True{} : Bool}, h)

def semver.ps.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LLogicLogic.semver.ps.absurdF({b == True{} : Bool}, h)

def ppr.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.ppr.absurdF({False{} == True{} : Bool}, h)

def ppr.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LLogicLogic.ppr.absurdF({b == True{} : Bool}, h)

def rp.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.rp.absurdF({False{} == True{} : Bool}, e)

def rp.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LLogicLogic.rp.absurdF({b == True{} : Bool}, e)

def tc.bst_l(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {tc.bst(l) == True{} : Bool}:
  tree.pt.and_l(tc.bst(l), Bool.and(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid))), h)
