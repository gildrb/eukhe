# eukhe: the proof of LAW notice_real_refines

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice
import ./base.bend as LA

# The scenario runs the rule on the stored notices at positions 0, 1, ..
# (stamp i is i chars, Notice.nt_stamp). The invariant `nr.Inv` ties the
# scenario's record and counts to the model's notices: the counts are the
# model's, the record holds the stamp of position i exactly when the model
# says notice i is seen (`nr.flags`), and every stamp it holds is shorter
# than the number of stored notices (`nr.low`, so a new notice is not held).
# Each event keeps it: a restore adds an unseen notice; a live notice
# records the newest stamp when it shows (the others differ:
# `nr.same_stamp`); an attach records every stored notice the record did
# not hold (`nr.scan_has`), so after it each is held.

# Numbers
# -------

def nr.lt(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      False{}
    case 0n 1n+q:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      nr.lt(p, q)

def nr.le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+q:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      nr.le(p, q)

def nr.eqn(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+q:
      False{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      nr.eqn(p, q)

def nr.no(-G: Type, e: {False{} == True{} : Bool}) -> G:
  LA.notice.pn.absurdF(G, e)

def nr.lt_self(i: Nat) -> {nr.lt(i, 1n+i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      nr.lt_self(p)

def nr.le_zero(j: Nat) -> {nr.le(0n, j) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      {==}

def nr.le_refl(i: Nat) -> {nr.le(i, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      nr.le_refl(p)

def nr.lt_succ(j: Nat, i: Nat, h: {nr.lt(j, i) == True{} : Bool}) -> {nr.lt(j, 1n+i) == True{} : Bool}:
  match j i:
    case 0n 0n:
      nr.no({nr.lt(0n, 1n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      nr.no({nr.lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      nr.lt_succ(p, q, h)

def nr.lt_pred(i: Nat, x: Nat, h: {nr.lt(1n+i, x) == True{} : Bool}) -> {nr.lt(i, x) == True{} : Bool}:
  match i x:
    case 0n 0n:
      nr.no({nr.lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      nr.no({nr.lt(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      nr.lt_pred(p, q, h)

def nr.lt_ne(j: Nat, i: Nat, h: {nr.lt(j, i) == True{} : Bool}) -> {nr.eqn(i, j) == False{} : Bool}:
  match j i:
    case 0n 0n:
      nr.no({nr.eqn(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      nr.no({nr.eqn(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      nr.lt_ne(p, q, h)

def nr.lt_le(a: Nat, b: Nat, c: Nat, h1: {nr.lt(a, b) == True{} : Bool}, h2: {nr.le(b, c) == True{} : Bool}) -> {nr.lt(a, c) == True{} : Bool}:
  match a b:
    case 0n 0n:
      nr.no({nr.lt(0n, c) == True{} : Bool}, h1)
    case 0n 1n+q:
      match c:
        case 0n:
          nr.no({nr.lt(0n, 0n) == True{} : Bool}, h2)
        case 1n+r:
          {==}
    case 1n+p 0n:
      nr.no({nr.lt(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q:
      match c:
        case 0n:
          nr.no({nr.lt(1n+p, 0n) == True{} : Bool}, h2)
        case 1n+r:
          nr.lt_le(p, q, r, h1, h2)

def nr.le_lt(-G: Type, i: Nat, j: Nat, hle: {nr.le(i, j) == True{} : Bool}, hlt: {nr.lt(j, i) == True{} : Bool}) -> G:
  match i j:
    case 0n 0n:
      nr.no(G, hlt)
    case 0n 1n+q:
      nr.no(G, hlt)
    case 1n+p 0n:
      nr.no(G, hle)
    case 1n+p 1n+q:
      nr.le_lt(G, p, q, hle, hlt)

def nr.eqn_sound(i: Nat, j: Nat, e: {nr.eqn(i, j) == True{} : Bool}) -> {i == j : Nat}:
  match i j:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      nr.no({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      nr.no({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, nr.eqn_sound(p, q, e))

def nr.eqn_refl(i: Nat) -> {nr.eqn(i, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      nr.eqn_refl(p)

def nr.le_next(i: Nat, j: Nat, hle: {nr.le(i, j) == True{} : Bool}, hne: {nr.eqn(i, j) == False{} : Bool}) -> {nr.le(1n+i, j) == True{} : Bool}:
  match i j:
    case 0n 0n:
      nr.no({nr.le(1n, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, hne))
    case 0n 1n+q:
      nr.le_zero(q)
    case 1n+p 0n:
      nr.no({nr.le(2n+p, 0n) == True{} : Bool}, hle)
    case 1n+p 1n+q:
      nr.le_next(p, q, hle, hne)

# Positions and stamps
# --------------------

# the position after the notices ns, from position i
def nr.pos(ns: List<&2, No.N>, i: Nat) -> Nat:
  match ns:
    case Nil{}:
      i
    case n <> t:
      nr.pos(t, 1n+i)

def nr.pos_snoc(ns: List<&2, No.N>, +i: Nat, +x: No.N) -> {nr.pos(List.append(&2, No.N, ns, [x]), i) == 1n+nr.pos(ns, i) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case n <> t:
      nr.pos_snoc(t, 1n+i, x)

def nr.pos_live_at(t: List<&2, No.N>, n: No.N, +i: Nat) -> {nr.pos(No.live.at(t, n), i) == nr.pos(t, 1n+i) : Nat}:
  match t:
    case Nil{}:
      {==}
    case m <> u:
      nr.pos_live_at(u, m, 1n+i)

def nr.pos_rebuild(ns: List<&2, No.N>, +i: Nat) -> {nr.pos(No.rebuild(ns), i) == nr.pos(ns, i) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case n <> t:
      nr.pos_rebuild(t, 1n+i)

def nr.lt_pos_succ(t: List<&2, No.N>, +i: Nat) -> {nr.lt(nr.pos(t, i), nr.pos(t, 1n+i)) == True{} : Bool}:
  match t:
    case Nil{}:
      nr.lt_self(i)
    case m <> u:
      nr.lt_pos_succ(u, 1n+i)

def nr.lt_pos(t: List<&2, No.N>, +i: Nat) -> {nr.lt(i, nr.pos(t, 1n+i)) == True{} : Bool}:
  match t:
    case Nil{}:
      nr.lt_self(i)
    case m <> +u:
      nr.lt_pred(i, nr.pos(u, 2n+i), nr.lt_pos(u, 1n+i))

def nr.pos_ne(u: List<&2, No.N>, +i: Nat, +j: Nat, h: {nr.lt(j, i) == True{} : Bool}) -> {nr.eqn(nr.pos(u, i), j) == False{} : Bool}:
  match u:
    case Nil{}:
      nr.lt_ne(j, i, h)
    case m <> w:
      nr.pos_ne(w, 1n+i, j, nr.lt_succ(j, i, h))

# the stamps of positions k and j are the same exactly when k is j
def nr.same_stamp(k: Nat, j: Nat) -> {No.same(Notice.nt_stamp(k), Notice.nt_stamp(j)) == nr.eqn(k, j) : Bool}:
  match k j:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nr.same_stamp(p, q)

def nr.eq_stamp(k: Nat, j: Nat) -> {Notice.nt_eq(Notice.nt_stamp(k), Notice.nt_stamp(j)) == nr.eqn(k, j) : Bool}:
  match k j:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nr.eq_stamp(p, q)

# b is shorter than n chars
def nr.below(b: String, n: Nat) -> Bool:
  match b n:
    case SNil{} 0n:
      False{}
    case SNil{} 1n+p:
      True{}
    case SCon{c, t} 0n:
      False{}
    case SCon{c, t} 1n+p:
      nr.below(t, p)

def nr.below_stamp(k: Nat, n: Nat) -> {nr.below(Notice.nt_stamp(k), n) == nr.lt(k, n) : Bool}:
  match k n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nr.below_stamp(p, q)

def nr.below_succ(b: String, n: Nat, h: {nr.below(b, n) == True{} : Bool}) -> {nr.below(b, 1n+n) == True{} : Bool}:
  match b n:
    case SNil{} 0n:
      nr.no({nr.below(SNil{}, 1n) == True{} : Bool}, h)
    case SNil{} 1n+p:
      {==}
    case SCon{c, t} 0n:
      nr.no({nr.below(SCon{c, t}, 1n) == True{} : Bool}, h)
    case SCon{c, t} 1n+p:
      nr.below_succ(t, p, h)

# a stamp shorter than n chars is not the stamp of position n
def nr.same_below(b: String, n: Nat, h: {nr.below(b, n) == True{} : Bool}) -> {No.same(b, Notice.nt_stamp(n)) == False{} : Bool}:
  match b n:
    case SNil{} 0n:
      nr.no({No.same(SNil{}, SNil{}) == False{} : Bool}, h)
    case SNil{} 1n+p:
      {==}
    case SCon{c, t} 0n:
      nr.no({No.same(SCon{c, t}, SNil{}) == False{} : Bool}, h)
    case SCon{+c, +t} 1n+p:
      %Equal.sym(Bool, No.same(t, Notice.nt_stamp(p)), False{}, nr.same_below(t, p, h)) : {Bool.and(Char.is_eq(c, '1'), _) == False{} : Bool}
      LA.nt.and_false(Char.is_eq(c, '1'))

# The record
# ----------

# the record holds the stamp of position i (in the scenario's session)
def nr.H(rs: List<&2, No.Seen>, +i: Nat) -> Bool:
  No.held(rs, Notice.nt_sid(), Notice.nt_stamp(i))

def nr.beq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def nr.beq_eq(a: Bool, b: Bool, h: {nr.beq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      nr.no({True{} == False{} : Bool}, h)
    case False{} True{}:
      nr.no({False{} == True{} : Bool}, h)
    case False{} False{}:
      {==}

def nr.flags.go(ns: List<&2, No.N>, +rs: List<&2, No.Seen>, +i: Nat) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case n <> t:
      match n:
        case No.N{s, c}:
          Bool.and(nr.beq(nr.H(rs, i), s), nr.flags.go(t, rs, 1n+i))

# from position i on, the record holds the stamp of each notice exactly
# when the model says it is seen
def nr.flags(rs: List<&2, No.Seen>, i: Nat, ns: List<&2, No.N>) -> Bool:
  nr.flags.go(ns, rs, i)

# every stamp the record holds is shorter than n chars
def nr.low(rs: List<&2, No.Seen>, +n: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      match r:
        case No.Seen{a, b}:
          Bool.and(nr.below(b, n), nr.low(t, n))

def nr.low_succ(rs: List<&2, No.Seen>, +n: Nat, +h: {nr.low(rs, n) == True{} : Bool}) -> {nr.low(rs, 1n+n) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case No.Seen{a, +b}:
          LA.notice.pn.and_t(nr.below(b, 1n+n), nr.low(t, 1n+n), nr.below_succ(b, n, LA.notice.pn.and_l(nr.below(b, n), nr.low(t, n), h)), nr.low_succ(t, n, LA.notice.pn.and_r(nr.below(b, n), nr.low(t, n), h)))

# a record whose stamps are shorter than n does not hold the stamp of position n
def nr.held_low(rs: List<&2, No.Seen>, +n: Nat, +q: String, +h: {nr.low(rs, n) == True{} : Bool}) -> {No.held(rs, q, Notice.nt_stamp(n)) == False{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case No.Seen{+a, +b}:
          %Equal.sym(Bool, No.same(b, Notice.nt_stamp(n)), False{}, nr.same_below(b, n, LA.notice.pn.and_l(nr.below(b, n), nr.low(t, n), h))) : {Bool.or(Bool.and(No.same(a, q), _), No.held(t, q, Notice.nt_stamp(n))) == False{} : Bool}
          %Equal.sym(Bool, Bool.and(No.same(a, q), False{}), False{}, LA.nt.and_false(No.same(a, q))) : {Bool.or(_, No.held(t, q, Notice.nt_stamp(n))) == False{} : Bool}
          nr.held_low(t, n, q, LA.notice.pn.and_r(nr.below(b, n), nr.low(t, n), h))

# the record, with the stamp of position k when b
def nr.add_if(b: Bool, rs: List<&2, No.Seen>, +k: Nat) -> List<&2, No.Seen>:
  match b:
    case True{}:
      No.Seen{Notice.nt_sid(), Notice.nt_stamp(k)} <> rs
    case False{}:
      rs

def nr.H_add_if(b: Bool, +rs: List<&2, No.Seen>, +k: Nat, +i: Nat, hne: {nr.eqn(k, i) == False{} : Bool}) -> {nr.H(nr.add_if(b, rs, k), i) == nr.H(rs, i) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, No.same(Notice.nt_stamp(k), Notice.nt_stamp(i)), nr.eqn(k, i), nr.same_stamp(k, i)) : {Bool.or(Bool.and(No.same(Notice.nt_sid(), Notice.nt_sid()), _), nr.H(rs, i)) == nr.H(rs, i) : Bool}
      %Equal.sym(Bool, nr.eqn(k, i), False{}, hne) : {Bool.or(Bool.and(No.same(Notice.nt_sid(), Notice.nt_sid()), _), nr.H(rs, i)) == nr.H(rs, i) : Bool}
      {==}
    case False{}:
      {==}

def nr.H_self(+rs: List<&2, No.Seen>, +i: Nat) -> {nr.H(No.Seen{Notice.nt_sid(), Notice.nt_stamp(i)} <> rs, i) == True{} : Bool}:
  %Equal.sym(Bool, No.same(Notice.nt_stamp(i), Notice.nt_stamp(i)), True{}, LA.nt.same_refl(Notice.nt_stamp(i))) : {Bool.or(Bool.and(No.same(Notice.nt_sid(), Notice.nt_sid()), _), nr.H(rs, i)) == True{} : Bool}
  {==}

def nr.low_add_if(b: Bool, +rs: List<&2, No.Seen>, +k: Nat, +n: Nat, hr: {nr.low(rs, n) == True{} : Bool}, hk: {nr.lt(k, n) == True{} : Bool}) -> {nr.low(nr.add_if(b, rs, k), n) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, nr.below(Notice.nt_stamp(k), n), nr.lt(k, n), nr.below_stamp(k, n)) : {Bool.and(_, nr.low(rs, n)) == True{} : Bool}
      LA.notice.pn.and_t(nr.lt(k, n), nr.low(rs, n), hk, hr)
    case False{}:
      hr

# what a record of messages k keeps short
def nr.mlow(m: No.Msg, +n: Nat) -> Bool:
  match m:
    case No.Other{}:
      True{}
    case No.Custom{k, t}:
      nr.below(t, n)

def nr.klow(ms: List<&2, No.Msg>, +n: Nat) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      Bool.and(nr.mlow(m, n), nr.klow(t, n))

def nr.low_of(b: Bool, +t: String, +sid: String, +rs: List<&2, No.Seen>, +n: Nat, ht: {nr.below(t, n) == True{} : Bool}, hr: {nr.low(rs, n) == True{} : Bool}) -> {nr.low(No.record.one(No.notice.of(b, t), sid, rs), n) == True{} : Bool}:
  match b:
    case True{}:
      LA.notice.pn.and_t(nr.below(t, n), nr.low(rs, n), ht, hr)
    case False{}:
      hr

def nr.low_one(m: No.Msg, +sid: String, +rs: List<&2, No.Seen>, +n: Nat, hm: {nr.mlow(m, n) == True{} : Bool}, hr: {nr.low(rs, n) == True{} : Bool}) -> {nr.low(No.record.one(No.notice(m), sid, rs), n) == True{} : Bool}:
  match m:
    case No.Other{}:
      hr
    case No.Custom{+k, +t}:
      nr.low_of(No.same(k, No.restore_kind()), t, sid, rs, n, hm, hr)

def nr.low_rec(ms: List<&2, No.Msg>, +sid: String, +rs: List<&2, No.Seen>, +n: Nat, +hk: {nr.klow(ms, n) == True{} : Bool}, hr: {nr.low(rs, n) == True{} : Bool}) -> {nr.low(No.record.go(ms, sid, rs), n) == True{} : Bool}:
  match ms:
    case Nil{}:
      hr
    case +m <> +t:
      nr.low_rec(t, sid, No.record.one(No.notice(m), sid, rs), n, LA.notice.pn.and_r(nr.mlow(m, n), nr.klow(t, n), hk), nr.low_one(m, sid, rs, n, LA.notice.pn.and_l(nr.mlow(m, n), nr.klow(t, n), hk), hr))

# The invariant
# -------------

def nr.recs(p: List<&2, No.Seen> & List<&2, Nat>) -> List<&2, No.Seen>:
  (rs, cs) = p
  rs

def nr.Inv(p: List<&2, No.Seen> & List<&2, Nat>, ns: List<&2, No.N>) -> Type:
  {Notice.nt_counts(p) == Notice.nt_shown(ns) : List<&2, Nat>} & ({nr.flags(nr.recs(p), 0n, ns) == True{} : Bool} & {nr.low(nr.recs(p), nr.pos(ns, 0n)) == True{} : Bool})

# A restore
# ---------

def nr.shown_snoc(ns: List<&2, No.N>, +s: Bool, +c: Nat) -> {List.append(&2, Nat, Notice.nt_shown(ns), [c]) == Notice.nt_shown(List.append(&2, No.N, ns, [No.N{s, c}])) : List<&2, Nat>}:
  match ns:
    case Nil{}:
      {==}
    case n <> t:
      match n:
        case No.N{s2, +c2}:
          %nr.shown_snoc(t, s, c) : {c2 <> List.append(&2, Nat, Notice.nt_shown(t), [c]) == c2 <> _ : List<&2, Nat>}
          {==}

def nr.flags_snoc(ns: List<&2, No.N>, +i: Nat, +rs: List<&2, No.Seen>, +s: Bool, +c: Nat, +hb: {nr.flags(rs, i, ns) == True{} : Bool}, hx: {nr.beq(nr.H(rs, nr.pos(ns, i)), s) == True{} : Bool}) -> {nr.flags(rs, i, List.append(&2, No.N, ns, [No.N{s, c}])) == True{} : Bool}:
  match ns:
    case Nil{}:
      LA.notice.pn.and_t(nr.beq(nr.H(rs, i), s), True{}, hx, {==})
    case n <> t:
      match n:
        case No.N{+s2, c2}:
          +a = nr.beq(nr.H(rs, i), s2)
          LA.notice.pn.and_t(a, nr.flags(rs, 1n+i, List.append(&2, No.N, t, [No.N{s, c}])), LA.notice.pn.and_l(a, nr.flags(rs, 1n+i, t), hb), nr.flags_snoc(t, 1n+i, rs, s, c, LA.notice.pn.and_r(a, nr.flags(rs, 1n+i, t), hb), hx))

def nr.restore_go(+rs: List<&2, No.Seen>, +cs: List<&2, Nat>, +ns: List<&2, No.N>, ha: {cs == Notice.nt_shown(ns) : List<&2, Nat>}, hb: {nr.flags(rs, 0n, ns) == True{} : Bool}, +hc: {nr.low(rs, nr.pos(ns, 0n)) == True{} : Bool}) -> nr.Inv(Notice.nt_step(No.Restore{}, (rs, cs)), No.step(ns, No.Restore{})):
  +n0 = nr.pos(ns, 0n)
  +x = {No.N{False{}, 0n} : No.N}
  +ea = Equal.trans(List<&2, Nat>, List.append(&2, Nat, cs, [0n]), List.append(&2, Nat, Notice.nt_shown(ns), [0n]), Notice.nt_shown(List.append(&2, No.N, ns, [x])), Equal.cong(List<&2, Nat>, List<&2, Nat>, y => List.append(&2, Nat, y, [0n]), cs, Notice.nt_shown(ns), ha), nr.shown_snoc(ns, False{}, 0n))
  +hx = Equal.cong(Bool, Bool, y => nr.beq(y, False{}), nr.H(rs, n0), False{}, nr.held_low(rs, n0, Notice.nt_sid(), hc))
  +el = Equal.trans(Bool, nr.low(rs, nr.pos(List.append(&2, No.N, ns, [x]), 0n)), nr.low(rs, 1n+n0), True{}, Equal.cong(Nat, Bool, y => nr.low(rs, y), nr.pos(List.append(&2, No.N, ns, [x]), 0n), 1n+n0, nr.pos_snoc(ns, 0n, x)), nr.low_succ(rs, n0, hc))
  (ea, (nr.flags_snoc(ns, 0n, rs, False{}, 0n, hb, hx), el))

def nr.restore_inv(+rs: List<&2, No.Seen>, +cs: List<&2, Nat>, +ns: List<&2, No.N>, inv: nr.Inv((rs, cs), ns)) -> nr.Inv(Notice.nt_step(No.Restore{}, (rs, cs)), No.step(ns, No.Restore{})):
  (ha, more) = inv
  (hb, hc) = more
  nr.restore_go(rs, cs, ns, ha, hb, hc)

# A live notice
# -------------

def nr.cons_recs(c: Nat, r: List<&2, No.Seen> & List<&2, Nat>) -> {nr.recs(Notice.nt_live.cons(c, r)) == nr.recs(r) : List<&2, No.Seen>}:
  (a, b) = r
  {==}

def nr.cons_counts(c: Nat, r: List<&2, No.Seen> & List<&2, Nat>) -> {Notice.nt_counts(Notice.nt_live.cons(c, r)) == c <> Notice.nt_counts(r) : List<&2, Nat>}:
  (a, b) = r
  {==}

def nr.last_recs(b: Bool, rs: List<&2, No.Seen>, c: Nat, +i: Nat) -> {nr.recs(Notice.nt_live.last(b, rs, c, i)) == nr.add_if(b, rs, i) : List<&2, No.Seen>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the record after a live notice: the stamp of the newest added when it showed
def nr.la_recs(t: List<&2, No.N>, c: Nat, +i: Nat, +rs: List<&2, No.Seen>) -> {nr.recs(Notice.nt_live.at(Notice.nt_shown(t), c, i, rs)) == nr.add_if(Bool.not(nr.H(rs, nr.pos(t, i))), rs, nr.pos(t, i)) : List<&2, No.Seen>}:
  match t:
    case Nil{}:
      nr.last_recs(No.visible(rs, Notice.nt_sid(), Notice.nt_note(i)), rs, c, i)
    case n <> +u:
      match n:
        case No.N{s2, +c2}:
          Equal.trans(List<&2, No.Seen>, nr.recs(Notice.nt_live.cons(c, Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs))), nr.recs(Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs)), nr.add_if(Bool.not(nr.H(rs, nr.pos(u, 1n+i))), rs, nr.pos(u, 1n+i)), nr.cons_recs(c, Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs)), nr.la_recs(u, c2, 1n+i, rs))

def nr.last_counts(s: Bool, +c: Nat, +rs: List<&2, No.Seen>, +i: Nat) -> {Notice.nt_counts(Notice.nt_live.last(Bool.not(s), rs, c, i)) == Notice.nt_shown(No.live.at(Nil{}, No.N{s, c})) : List<&2, Nat>}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

# the counts after a live notice are the model's
def nr.la_counts(t: List<&2, No.N>, +s: Bool, +c: Nat, +i: Nat, +rs: List<&2, No.Seen>, +hb: {nr.flags(rs, i, No.N{s, c} <> t) == True{} : Bool}) -> {Notice.nt_counts(Notice.nt_live.at(Notice.nt_shown(t), c, i, rs)) == Notice.nt_shown(No.live.at(t, No.N{s, c})) : List<&2, Nat>}:
  match t:
    case Nil{}:
      +e = nr.beq_eq(nr.H(rs, i), s, LA.notice.pn.and_l(nr.beq(nr.H(rs, i), s), True{}, hb))
      %Equal.sym(Bool, nr.H(rs, i), s, e) : {Notice.nt_counts(Notice.nt_live.last(Bool.not(_), rs, c, i)) == Notice.nt_shown(No.live.at(Nil{}, No.N{s, c})) : List<&2, Nat>}
      nr.last_counts(s, c, rs, i)
    case n <> +u:
      match n:
        case No.N{+s2, +c2}:
          +ih = nr.la_counts(u, s2, c2, 1n+i, rs, LA.notice.pn.and_r(nr.beq(nr.H(rs, i), s), nr.flags(rs, 1n+i, No.N{s2, c2} <> u), hb))
          Equal.trans(List<&2, Nat>, Notice.nt_counts(Notice.nt_live.cons(c, Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs))), c <> Notice.nt_counts(Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs)), c <> Notice.nt_shown(No.live.at(u, No.N{s2, c2})), nr.cons_counts(c, Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs)), Equal.cong(List<&2, Nat>, List<&2, Nat>, y => c <> y, Notice.nt_counts(Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs)), Notice.nt_shown(No.live.at(u, No.N{s2, c2})), ih))

def nr.last_flags(s: Bool, +c: Nat, +i: Nat, +rs: List<&2, No.Seen>, +e: {nr.H(rs, i) == s : Bool}) -> {nr.flags(nr.add_if(Bool.not(nr.H(rs, i)), rs, i), i, No.live.at(Nil{}, No.N{s, c})) == True{} : Bool}:
  match s:
    case True{}:
      %Equal.sym(Bool, nr.H(rs, i), True{}, e) : {nr.flags(nr.add_if(Bool.not(_), rs, i), i, [No.N{True{}, c}]) == True{} : Bool}
      %Equal.sym(Bool, nr.H(rs, i), True{}, e) : {Bool.and(nr.beq(_, True{}), True{}) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, nr.H(rs, i), False{}, e) : {nr.flags(nr.add_if(Bool.not(_), rs, i), i, [No.N{True{}, 1n+c}]) == True{} : Bool}
      %Equal.sym(Bool, nr.H(No.Seen{Notice.nt_sid(), Notice.nt_stamp(i)} <> rs, i), True{}, nr.H_self(rs, i)) : {Bool.and(nr.beq(_, True{}), True{}) == True{} : Bool}
      {==}

# the record after a live notice holds the model's seen notices
def nr.la_flags(t: List<&2, No.N>, +s: Bool, +c: Nat, +i: Nat, +rs: List<&2, No.Seen>, +hb: {nr.flags(rs, i, No.N{s, c} <> t) == True{} : Bool}) -> {nr.flags(nr.recs(Notice.nt_live.at(Notice.nt_shown(t), c, i, rs)), i, No.live.at(t, No.N{s, c})) == True{} : Bool}:
  match t:
    case Nil{}:
      %Equal.sym(List<&2, No.Seen>, nr.recs(Notice.nt_live.at(Nil{}, c, i, rs)), nr.add_if(Bool.not(nr.H(rs, i)), rs, i), nr.la_recs(Nil{}, c, i, rs)) : {nr.flags(_, i, No.live.at(Nil{}, No.N{s, c})) == True{} : Bool}
      nr.last_flags(s, c, i, rs, nr.beq_eq(nr.H(rs, i), s, LA.notice.pn.and_l(nr.beq(nr.H(rs, i), s), True{}, hb)))
    case n <> +u:
      match n:
        case No.N{+s2, +c2}:
          +l = nr.pos(u, 1n+i)
          +f = nr.flags(nr.recs(Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs)), 1n+i, No.live.at(u, No.N{s2, c2}))
          +hh = LA.notice.pn.and_l(nr.beq(nr.H(rs, i), s), nr.flags(rs, 1n+i, No.N{s2, c2} <> u), hb)
          +ht = LA.notice.pn.and_r(nr.beq(nr.H(rs, i), s), nr.flags(rs, 1n+i, No.N{s2, c2} <> u), hb)
          %Equal.sym(List<&2, No.Seen>, nr.recs(Notice.nt_live.cons(c, Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs))), nr.recs(Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs)), nr.cons_recs(c, Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs))) : {Bool.and(nr.beq(nr.H(_, i), s), nr.flags(_, 1n+i, No.live.at(u, No.N{s2, c2}))) == True{} : Bool}
          %Equal.sym(List<&2, No.Seen>, nr.recs(Notice.nt_live.at(Notice.nt_shown(u), c2, 1n+i, rs)), nr.add_if(Bool.not(nr.H(rs, l)), rs, l), nr.la_recs(u, c2, 1n+i, rs)) : {Bool.and(nr.beq(nr.H(_, i), s), f) == True{} : Bool}
          %Equal.sym(Bool, nr.H(nr.add_if(Bool.not(nr.H(rs, l)), rs, l), i), nr.H(rs, i), nr.H_add_if(Bool.not(nr.H(rs, l)), rs, l, i, nr.pos_ne(u, 1n+i, i, nr.lt_self(i)))) : {Bool.and(nr.beq(_, s), f) == True{} : Bool}
          LA.notice.pn.and_t(nr.beq(nr.H(rs, i), s), f, hh, nr.la_flags(u, s2, c2, 1n+i, rs, ht))

def nr.live_top(+t: List<&2, No.N>, +s: Bool, +c: Nat, +rs: List<&2, No.Seen>, +hb: {nr.flags(rs, 0n, No.N{s, c} <> t) == True{} : Bool}, hc: {nr.low(rs, nr.pos(t, 1n)) == True{} : Bool}) -> nr.Inv(Notice.nt_live.at(Notice.nt_shown(t), c, 0n, rs), No.live.at(t, No.N{s, c})):
  +l = nr.pos(t, 0n)
  +el = nr.la_recs(t, c, 0n, rs)
  +hl = nr.low_add_if(Bool.not(nr.H(rs, l)), rs, l, nr.pos(t, 1n), hc, nr.lt_pos_succ(t, 0n))
  +lw = Equal.trans(Bool, nr.low(nr.recs(Notice.nt_live.at(Notice.nt_shown(t), c, 0n, rs)), nr.pos(No.live.at(t, No.N{s, c}), 0n)), nr.low(nr.add_if(Bool.not(nr.H(rs, l)), rs, l), nr.pos(t, 1n)), True{}, Equal.trans(Bool, nr.low(nr.recs(Notice.nt_live.at(Notice.nt_shown(t), c, 0n, rs)), nr.pos(No.live.at(t, No.N{s, c}), 0n)), nr.low(nr.recs(Notice.nt_live.at(Notice.nt_shown(t), c, 0n, rs)), nr.pos(t, 1n)), nr.low(nr.add_if(Bool.not(nr.H(rs, l)), rs, l), nr.pos(t, 1n)), Equal.cong(Nat, Bool, y => nr.low(nr.recs(Notice.nt_live.at(Notice.nt_shown(t), c, 0n, rs)), y), nr.pos(No.live.at(t, No.N{s, c}), 0n), nr.pos(t, 1n), nr.pos_live_at(t, No.N{s, c}, 0n)), Equal.cong(List<&2, No.Seen>, Bool, y => nr.low(y, nr.pos(t, 1n)), nr.recs(Notice.nt_live.at(Notice.nt_shown(t), c, 0n, rs)), nr.add_if(Bool.not(nr.H(rs, l)), rs, l), el)), hl)
  (nr.la_counts(t, s, c, 0n, rs, hb), (nr.la_flags(t, s, c, 0n, rs, hb), lw))

def nr.live_ns(ns: List<&2, No.N>, +rs: List<&2, No.Seen>, hb: {nr.flags(rs, 0n, ns) == True{} : Bool}, hc: {nr.low(rs, nr.pos(ns, 0n)) == True{} : Bool}) -> nr.Inv(Notice.nt_live(Notice.nt_shown(ns), rs), No.live(ns)):
  match ns:
    case Nil{}:
      ({==}, ({==}, hc))
    case n <> t:
      match n:
        case No.N{+s, +c}:
          nr.live_top(t, s, c, rs, hb, hc)

def nr.live_inv(+rs: List<&2, No.Seen>, +cs: List<&2, Nat>, +ns: List<&2, No.N>, inv: nr.Inv((rs, cs), ns)) -> nr.Inv(Notice.nt_step(No.Live{}, (rs, cs)), No.step(ns, No.Live{})):
  (ha, more) = inv
  (hb, hc) = more
  %Equal.sym(List<&2, Nat>, cs, Notice.nt_shown(ns), ha) : nr.Inv(Notice.nt_live(_, rs), No.live(ns))
  nr.live_ns(ns, rs, hb, hc)

# An attach
# ---------

def nr.keep(r: List<&2, No.Msg> & List<&2, Nat>) -> List<&2, No.Msg>:
  (ks, cs) = r
  ks

def nr.cnt(r: List<&2, No.Msg> & List<&2, Nat>) -> List<&2, Nat>:
  (ks, cs) = r
  cs

def nr.attach_eq(+rs: List<&2, No.Seen>, r: List<&2, No.Msg> & List<&2, Nat>) -> {Notice.nt_attach(rs, r) == (No.record(rs, Notice.nt_sid(), nr.keep(r)), nr.cnt(r)) : List<&2, No.Seen> & List<&2, Nat>}:
  (ks, cs) = r
  {==}

def nr.cons_cnt(vo: Bool, vn: Bool, +i: Nat, c: Nat, r: List<&2, No.Msg> & List<&2, Nat>) -> {nr.cnt(Notice.nt_scan.cons(vo, vn, i, c, r)) == Notice.nt_bump(vn, c) <> nr.cnt(r) : List<&2, Nat>}:
  (ks, cs) = r
  {==}

def nr.cons_keep(vo: Bool, vn: Bool, +i: Nat, c: Nat, r: List<&2, No.Msg> & List<&2, Nat>) -> {nr.keep(Notice.nt_scan.cons(vo, vn, i, c, r)) == Notice.nt_keep.if(vo, No.Other{}, Notice.nt_keep.if(vn, Notice.nt_note(i), nr.keep(r))) : List<&2, No.Msg>}:
  (ks, cs) = r
  {==}

def nr.head_cnt(s: Bool, +c: Nat, -y: List<&2, Nat>, -z: List<&2, No.N>, ey: {y == Notice.nt_shown(z) : List<&2, Nat>}) -> {Notice.nt_bump(Bool.not(s), c) <> y == Notice.nt_shown(No.show(No.N{s, c}) <> z) : List<&2, Nat>}:
  match s:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, x => c <> x, y, Notice.nt_shown(z), ey)
    case False{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, x => (1n+c) <> x, y, Notice.nt_shown(z), ey)

# the counts after an attach are the model's
def nr.scan_cnt(ns: List<&2, No.N>, +i: Nat, +rs: List<&2, No.Seen>, +hb: {nr.flags(rs, i, ns) == True{} : Bool}) -> {nr.cnt(Notice.nt_scan(Notice.nt_shown(ns), i, rs)) == Notice.nt_shown(No.rebuild(ns)) : List<&2, Nat>}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      match n:
        case No.N{+s, +c}:
          +vn = No.visible(rs, Notice.nt_sid(), Notice.nt_note(i))
          +e = nr.beq_eq(nr.H(rs, i), s, LA.notice.pn.and_l(nr.beq(nr.H(rs, i), s), nr.flags(rs, 1n+i, t), hb))
          +ih = nr.scan_cnt(t, 1n+i, rs, LA.notice.pn.and_r(nr.beq(nr.H(rs, i), s), nr.flags(rs, 1n+i, t), hb))
          %Equal.sym(List<&2, Nat>, nr.cnt(Notice.nt_scan.cons(No.visible(rs, Notice.nt_sid(), No.Other{}), vn, i, c, Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs))), Notice.nt_bump(vn, c) <> nr.cnt(Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs)), nr.cons_cnt(No.visible(rs, Notice.nt_sid(), No.Other{}), vn, i, c, Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs))) : {_ == Notice.nt_shown(No.rebuild(No.N{s, c} <> t)) : List<&2, Nat>}
          %Equal.sym(Bool, nr.H(rs, i), s, e) : {Notice.nt_bump(Bool.not(_), c) <> nr.cnt(Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs)) == Notice.nt_shown(No.rebuild(No.N{s, c} <> t)) : List<&2, Nat>}
          nr.head_cnt(s, c, nr.cnt(Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs)), No.rebuild(t), ih)

def nr.has_if(b: Bool, +x: No.Msg, +xs: List<&2, No.Msg>, +s: String, h: {Notice.nt_has(xs, s) == True{} : Bool}) -> {Notice.nt_has(Notice.nt_keep.if(b, x, xs), s) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Notice.nt_has(xs, s), True{}, h) : {Bool.or(Notice.nt_is(x, s), _) == True{} : Bool}
      LA.nt.or_true(Notice.nt_is(x, s))
    case False{}:
      h

def nr.sh_case(b: Bool, +i: Nat, +j: Nat, +rs: List<&2, No.Seen>, +k: List<&2, No.Msg>, +eb: {nr.eqn(i, j) == b : Bool}, hle: {nr.le(i, j) == True{} : Bool}, hh: {nr.H(rs, j) == False{} : Bool}, ih: {nr.le(1n+i, j) == True{} : Bool} -> {Notice.nt_has(k, Notice.nt_stamp(j)) == True{} : Bool}) -> {Notice.nt_has(Notice.nt_keep.if(Bool.not(nr.H(rs, i)), Notice.nt_note(i), k), Notice.nt_stamp(j)) == True{} : Bool}:
  match b:
    case True{}:
      +ij = nr.eqn_sound(i, j, eb)
      %Equal.sym(Bool, nr.H(rs, i), nr.H(rs, j), Equal.cong(Nat, Bool, y => nr.H(rs, y), i, j, ij)) : {Notice.nt_has(Notice.nt_keep.if(Bool.not(_), Notice.nt_note(i), k), Notice.nt_stamp(j)) == True{} : Bool}
      %Equal.sym(Bool, nr.H(rs, j), False{}, hh) : {Notice.nt_has(Notice.nt_keep.if(Bool.not(_), Notice.nt_note(i), k), Notice.nt_stamp(j)) == True{} : Bool}
      %Equal.sym(Bool, Notice.nt_eq(Notice.nt_stamp(i), Notice.nt_stamp(j)), nr.eqn(i, j), nr.eq_stamp(i, j)) : {Bool.or(Bool.and(Notice.nt_eq(Notice.nt_kind(), Notice.nt_kind()), _), Notice.nt_has(k, Notice.nt_stamp(j))) == True{} : Bool}
      %Equal.sym(Bool, nr.eqn(i, j), True{}, eb) : {Bool.or(Bool.and(Notice.nt_eq(Notice.nt_kind(), Notice.nt_kind()), _), Notice.nt_has(k, Notice.nt_stamp(j))) == True{} : Bool}
      {==}
    case False{}:
      nr.has_if(Bool.not(nr.H(rs, i)), Notice.nt_note(i), k, Notice.nt_stamp(j), ih(nr.le_next(i, j, hle, eb)))

# an attach keeps the notice of every position j from i on that the record did not hold
def nr.scan_has(ns: List<&2, No.N>, +i: Nat, +rs: List<&2, No.Seen>, +j: Nat, hle: {nr.le(i, j) == True{} : Bool}, hlt: {nr.lt(j, nr.pos(ns, i)) == True{} : Bool}, +hh: {nr.H(rs, j) == False{} : Bool}) -> {Notice.nt_has(nr.keep(Notice.nt_scan(Notice.nt_shown(ns), i, rs)), Notice.nt_stamp(j)) == True{} : Bool}:
  match ns:
    case Nil{}:
      nr.le_lt({Notice.nt_has(Nil{}, Notice.nt_stamp(j)) == True{} : Bool}, i, j, hle, hlt)
    case n <> +t:
      match n:
        case No.N{s, +c}:
          +vo = No.visible(rs, Notice.nt_sid(), No.Other{})
          +vn = No.visible(rs, Notice.nt_sid(), Notice.nt_note(i))
          %Equal.sym(List<&2, No.Msg>, nr.keep(Notice.nt_scan.cons(vo, vn, i, c, Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs))), Notice.nt_keep.if(vo, No.Other{}, Notice.nt_keep.if(vn, Notice.nt_note(i), nr.keep(Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs)))), nr.cons_keep(vo, vn, i, c, Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs))) : {Notice.nt_has(_, Notice.nt_stamp(j)) == True{} : Bool}
          nr.sh_case(nr.eqn(i, j), i, j, rs, nr.keep(Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs)), {==}, hle, hh, h2 => nr.scan_has(t, 1n+i, rs, j, h2, hlt, hh))

def nr.klow_if(b: Bool, +x: No.Msg, +xs: List<&2, No.Msg>, +n: Nat, hx: {nr.mlow(x, n) == True{} : Bool}, h: {nr.klow(xs, n) == True{} : Bool}) -> {nr.klow(Notice.nt_keep.if(b, x, xs), n) == True{} : Bool}:
  match b:
    case True{}:
      LA.notice.pn.and_t(nr.mlow(x, n), nr.klow(xs, n), hx, h)
    case False{}:
      h

# what an attach keeps is shorter than n
def nr.scan_klow(ns: List<&2, No.N>, +i: Nat, +rs: List<&2, No.Seen>, +n: Nat, +hp: {nr.le(nr.pos(ns, i), n) == True{} : Bool}) -> {nr.klow(nr.keep(Notice.nt_scan(Notice.nt_shown(ns), i, rs)), n) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case No.N{s, +c}:
          +vo = No.visible(rs, Notice.nt_sid(), No.Other{})
          +vn = No.visible(rs, Notice.nt_sid(), Notice.nt_note(i))
          +hi = nr.lt_le(i, nr.pos(t, 1n+i), n, nr.lt_pos(t, i), hp)
          %Equal.sym(List<&2, No.Msg>, nr.keep(Notice.nt_scan.cons(vo, vn, i, c, Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs))), Notice.nt_keep.if(vo, No.Other{}, Notice.nt_keep.if(vn, Notice.nt_note(i), nr.keep(Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs)))), nr.cons_keep(vo, vn, i, c, Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs))) : {nr.klow(_, n) == True{} : Bool}
          nr.klow_if(vn, Notice.nt_note(i), nr.keep(Notice.nt_scan(Notice.nt_shown(t), 1n+i, rs)), n, Equal.trans(Bool, nr.below(Notice.nt_stamp(i), n), nr.lt(i, n), True{}, nr.below_stamp(i, n), hi), nr.scan_klow(t, 1n+i, rs, n, hp))

def nr.re_held2(hv: Bool, +rs: List<&2, No.Seen>, +k: List<&2, No.Msg>, +j: Nat, eh: {nr.H(rs, j) == hv : Bool}, has: {nr.H(rs, j) == False{} : Bool} -> {Notice.nt_has(k, Notice.nt_stamp(j)) == True{} : Bool}) -> {Bool.or(Bool.and(No.same(Notice.nt_sid(), Notice.nt_sid()), Notice.nt_has(k, Notice.nt_stamp(j))), nr.H(rs, j)) == True{} : Bool}:
  match hv:
    case True{}:
      %Equal.sym(Bool, nr.H(rs, j), True{}, eh) : {Bool.or(Bool.and(No.same(Notice.nt_sid(), Notice.nt_sid()), Notice.nt_has(k, Notice.nt_stamp(j))), _) == True{} : Bool}
      LA.nt.or_true(Bool.and(No.same(Notice.nt_sid(), Notice.nt_sid()), Notice.nt_has(k, Notice.nt_stamp(j))))
    case False{}:
      %Equal.sym(Bool, Notice.nt_has(k, Notice.nt_stamp(j)), True{}, has(eh)) : {Bool.or(Bool.and(No.same(Notice.nt_sid(), Notice.nt_sid()), _), nr.H(rs, j)) == True{} : Bool}
      {==}

# after an attach the record holds every stored notice
def nr.re_held(+ns0: List<&2, No.N>, +rs: List<&2, No.Seen>, +j: Nat, +hj: {nr.lt(j, nr.pos(ns0, 0n)) == True{} : Bool}) -> {nr.H(No.record(rs, Notice.nt_sid(), nr.keep(Notice.nt_scan(Notice.nt_shown(ns0), 0n, rs))), j) == True{} : Bool}:
  +k = nr.keep(Notice.nt_scan(Notice.nt_shown(ns0), 0n, rs))
  %Equal.sym(Bool, No.held(No.record.go(k, Notice.nt_sid(), rs), Notice.nt_sid(), Notice.nt_stamp(j)), Bool.or(Bool.and(No.same(Notice.nt_sid(), Notice.nt_sid()), Notice.nt_has(k, Notice.nt_stamp(j))), nr.H(rs, j)), LA.nt.held_rec(k, Notice.nt_sid(), rs, Notice.nt_sid(), Notice.nt_stamp(j))) : {_ == True{} : Bool}
  nr.re_held2(nr.H(rs, j), rs, k, j, {==}, hh => nr.scan_has(ns0, 0n, rs, j, nr.le_zero(j), hj, hh))

def nr.re_head(s: Bool, +c: Nat, +rr: List<&2, No.Seen>, +i: Nat, -t: List<&2, No.N>, hh: {nr.H(rr, i) == True{} : Bool}, ih: {nr.flags(rr, 1n+i, No.rebuild(t)) == True{} : Bool}) -> {nr.flags(rr, i, No.rebuild(No.N{s, c} <> t)) == True{} : Bool}:
  match s:
    case True{}:
      %Equal.sym(Bool, nr.H(rr, i), True{}, hh) : {Bool.and(nr.beq(_, True{}), nr.flags(rr, 1n+i, No.rebuild(t))) == True{} : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, nr.H(rr, i), True{}, hh) : {Bool.and(nr.beq(_, True{}), nr.flags(rr, 1n+i, No.rebuild(t))) == True{} : Bool}
      ih

def nr.re_flags(ns: List<&2, No.N>, +i: Nat, +rs: List<&2, No.Seen>, +ns0: List<&2, No.N>, +e: {nr.pos(ns, i) == nr.pos(ns0, 0n) : Nat}) -> {nr.flags(No.record(rs, Notice.nt_sid(), nr.keep(Notice.nt_scan(Notice.nt_shown(ns0), 0n, rs))), i, No.rebuild(ns)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      match n:
        case No.N{s, c}:
          +rr = No.record(rs, Notice.nt_sid(), nr.keep(Notice.nt_scan(Notice.nt_shown(ns0), 0n, rs)))
          +hi = Equal.trans(Bool, nr.lt(i, nr.pos(ns0, 0n)), nr.lt(i, nr.pos(t, 1n+i)), True{}, Equal.cong(Nat, Bool, y => nr.lt(i, y), nr.pos(ns0, 0n), nr.pos(t, 1n+i), Equal.sym(Nat, nr.pos(t, 1n+i), nr.pos(ns0, 0n), e)), nr.lt_pos(t, i))
          nr.re_head(s, c, rr, i, t, nr.re_held(ns0, rs, i, hi), nr.re_flags(t, 1n+i, rs, ns0, e))

def nr.re_ns(+ns: List<&2, No.N>, +rs: List<&2, No.Seen>, +hb: {nr.flags(rs, 0n, ns) == True{} : Bool}, hc: {nr.low(rs, nr.pos(ns, 0n)) == True{} : Bool}) -> nr.Inv(Notice.nt_reattach(rs, Notice.nt_shown(ns)), No.rebuild(ns)):
  +n0 = nr.pos(ns, 0n)
  %Equal.sym(List<&2, No.Seen> & List<&2, Nat>, Notice.nt_attach(rs, Notice.nt_scan(Notice.nt_shown(ns), 0n, rs)), (No.record(rs, Notice.nt_sid(), nr.keep(Notice.nt_scan(Notice.nt_shown(ns), 0n, rs))), nr.cnt(Notice.nt_scan(Notice.nt_shown(ns), 0n, rs))), nr.attach_eq(rs, Notice.nt_scan(Notice.nt_shown(ns), 0n, rs))) : nr.Inv(_, No.rebuild(ns))
  +lw = nr.low_rec(nr.keep(Notice.nt_scan(Notice.nt_shown(ns), 0n, rs)), Notice.nt_sid(), rs, n0, nr.scan_klow(ns, 0n, rs, n0, nr.le_refl(n0)), hc)
  +el = Equal.trans(Bool, nr.low(No.record(rs, Notice.nt_sid(), nr.keep(Notice.nt_scan(Notice.nt_shown(ns), 0n, rs))), nr.pos(No.rebuild(ns), 0n)), nr.low(No.record(rs, Notice.nt_sid(), nr.keep(Notice.nt_scan(Notice.nt_shown(ns), 0n, rs))), n0), True{}, Equal.cong(Nat, Bool, y => nr.low(No.record(rs, Notice.nt_sid(), nr.keep(Notice.nt_scan(Notice.nt_shown(ns), 0n, rs))), y), nr.pos(No.rebuild(ns), 0n), n0, nr.pos_rebuild(ns, 0n)), lw)
  (nr.scan_cnt(ns, 0n, rs, hb), (nr.re_flags(ns, 0n, rs, ns, {==}), el))

def nr.re_inv(+rs: List<&2, No.Seen>, +cs: List<&2, Nat>, +ns: List<&2, No.N>, inv: nr.Inv((rs, cs), ns)) -> nr.Inv(Notice.nt_step(No.Reconnect{}, (rs, cs)), No.step(ns, No.Reconnect{})):
  (ha, more) = inv
  (hb, hc) = more
  %Equal.sym(List<&2, Nat>, cs, Notice.nt_shown(ns), ha) : nr.Inv(Notice.nt_reattach(rs, _), No.rebuild(ns))
  nr.re_ns(ns, rs, hb, hc)

# The run
# -------

def nr.step_inv(e: No.Ev, +rs: List<&2, No.Seen>, +cs: List<&2, Nat>, +ns: List<&2, No.N>, inv: nr.Inv((rs, cs), ns)) -> nr.Inv(Notice.nt_step(e, (rs, cs)), No.step(ns, e)):
  match e:
    case No.Restore{}:
      nr.restore_inv(rs, cs, ns, inv)
    case No.Live{}:
      nr.live_inv(rs, cs, ns, inv)
    case No.Reconnect{}:
      nr.re_inv(rs, cs, ns, inv)

def nr.go(evs: List<&2, No.Ev>, p: List<&2, No.Seen> & List<&2, Nat>, +ns: List<&2, No.N>, inv: nr.Inv(p, ns)) -> {Notice.nt_counts(Notice.nt_go(evs, p)) == Notice.nt_shown(No.go(evs, ns)) : List<&2, Nat>}:
  match evs:
    case Nil{}:
      (ha, more) = inv
      ha
    case +e <> rest:
      (+rs, +cs) = p
      nr.go(rest, Notice.nt_step(e, (rs, cs)), No.step(ns, e), nr.step_inv(e, rs, cs, ns, inv))

def Notice.notice_real_refines(evs):
  nr.go(evs, (Nil{}, Nil{}), Nil{}, ({==}, ({==}, {==})))
