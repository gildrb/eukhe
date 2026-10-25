# eukhe: the proof of LAW work_counts_distinct
# The ledger after reading p holds exactly the acts that occur in p
# (wc.mem_g); so reading one more act grows it by one exactly when the act
# did not occur before (wc.go).

import Base
import ../../bend/progress.bend as Pr
import ../../laws/progress.bend as Progress
import ../base/logic/nat.bend as LLogicNat
import ../base/nat.bend as LNat
import ./base.bend as LA

# Bool.or
# -------

def wc.or_f(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wc.or_comm(a: Bool, b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def wc.or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# What the ledger holds
# ---------------------

def wc.hit(c: Bool, +h: Nat, +y: Nat, +s: List<&2, Nat>, ec: {Nat.is_eq(h, y) == c : Bool}, m: {Pr.mem(h, s) == True{} : Bool}) -> {Pr.mem(y, s) == Bool.or(Pr.mem(y, s), c) : Bool}:
  match c:
    case True{}:
      my = Equal.trans(Bool, Pr.mem(y, s), Pr.mem(h, s), True{}, Equal.cong(Nat, Bool, v => Pr.mem(v, s), y, h, Equal.sym(Nat, h, y, LLogicNat.cb_nat_eq(h, y, ec))), m)
      Equal.trans(Bool, Pr.mem(y, s), True{}, Bool.or(Pr.mem(y, s), True{}), my, Equal.sym(Bool, Bool.or(Pr.mem(y, s), True{}), True{}, LA.pp.or_true_r(Pr.mem(y, s))))
    case False{}:
      Equal.sym(Bool, Bool.or(Pr.mem(y, s), False{}), Pr.mem(y, s), wc.or_f(Pr.mem(y, s)))

def wc.mem_put(b: Bool, +h: Nat, +y: Nat, +s: List<&2, Nat>, e: {Pr.mem(h, s) == b : Bool}) -> {Pr.mem(y, Pr.add.put(b, h, s)) == Bool.or(Pr.mem(y, s), Nat.is_eq(h, y)) : Bool}:
  match b:
    case True{}:
      wc.hit(Nat.is_eq(h, y), h, y, s, {==}, e)
    case False{}:
      wc.or_comm(Nat.is_eq(h, y), Pr.mem(y, s))

# after adding h, y is held when it was, or when it is h
def wc.mem_add(+y: Nat, +s: List<&2, Nat>, +h: Nat) -> {Pr.mem(y, Pr.add(s, h)) == Bool.or(Pr.mem(y, s), Nat.is_eq(h, y)) : Bool}:
  wc.mem_put(Pr.mem(h, s), h, y, s, {==})

# after reading p on top of s, y is held when it was, or when it occurs in p
def wc.mem_g(+y: Nat, p: List<&2, Nat>, +s: List<&2, Nat>) -> {Pr.mem(y, Pr.ledger(p, s)) == Bool.or(Pr.mem(y, s), Progress.wd_in(y, p)) : Bool}:
  match p:
    case Nil{}:
      Equal.sym(Bool, Bool.or(Pr.mem(y, s), False{}), Pr.mem(y, s), wc.or_f(Pr.mem(y, s)))
    case +h <> +t:
      +a = Pr.add(s, h)
      +ms = Pr.mem(y, s)
      +eq = Nat.is_eq(h, y)
      +it = Progress.wd_in(y, t)
      Equal.trans(Bool, Pr.mem(y, Pr.ledger(t, a)), Bool.or(Pr.mem(y, a), it), Bool.or(ms, Bool.or(eq, it)), wc.mem_g(y, t, a), Equal.trans(Bool, Bool.or(Pr.mem(y, a), it), Bool.or(Bool.or(ms, eq), it), Bool.or(ms, Bool.or(eq, it)), Equal.cong(Bool, Bool, v => Bool.or(v, it), Pr.mem(y, a), Bool.or(ms, eq), wc.mem_add(y, s, h)), wc.or_assoc(ms, eq, it)))

# Counting
# --------

def wc.snoc(p: List<&2, Nat>, +y: Nat, +s: List<&2, Nat>) -> {Pr.ledger(List.append(&2, Nat, p, [y]), s) == Pr.add(Pr.ledger(p, s), y) : List<&2, Nat>}:
  match p:
    case Nil{}:
      {==}
    case +h <> t:
      wc.snoc(t, y, Pr.add(s, h))

def wc.len_put(b: Bool, -h: Nat, -l: List<&2, Nat>) -> {List.length(&2, Nat, Pr.add.put(b, h, l)) == Nat.add(Progress.wd_one(b), List.length(&2, Nat, l)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wc.swap(b: Bool, +n: Nat, +w: Nat) -> {Nat.add(Nat.add(Progress.wd_one(b), n), w) == Nat.add(n, Nat.add(Progress.wd_one(b), w)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.sym(Nat, Nat.add(n, 1n+w), 1n+Nat.add(n, w), LNat.add_succ(n, w))

# the ledger after p then xs is the ledger after p and the acts of xs that
# occur neither in p nor earlier in xs
def wc.go(xs: List<&2, Nat>, +p: List<&2, Nat>) -> {List.length(&2, Nat, Pr.ledger(xs, Pr.ledger(p, Nil{}))) == Nat.add(List.length(&2, Nat, Pr.ledger(p, Nil{})), Progress.wd_new(xs, p)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(List.length(&2, Nat, Pr.ledger(p, Nil{})), 0n), List.length(&2, Nat, Pr.ledger(p, Nil{})), LNat.add_zero(List.length(&2, Nat, Pr.ledger(p, Nil{}))))
    case +h <> +t:
      +l = Pr.ledger(p, Nil{})
      +q = List.append(&2, Nat, p, [h])
      +w = Progress.wd_new(t, q)
      +m = Pr.mem(h, l)
      +n = List.length(&2, Nat, l)
      +o = Progress.wd_in(h, p)
      +lq = Pr.ledger(q, Nil{})
      +al = Pr.add(l, h)
      e01 = Equal.cong(List<&2, Nat>, Nat, v => List.length(&2, Nat, Pr.ledger(t, v)), al, lq, Equal.sym(List<&2, Nat>, lq, al, wc.snoc(p, h, Nil{})))
      e23 = Equal.cong(List<&2, Nat>, Nat, v => Nat.add(List.length(&2, Nat, v), w), lq, al, wc.snoc(p, h, Nil{}))
      e34 = Equal.cong(Nat, Nat, v => Nat.add(v, w), List.length(&2, Nat, al), Nat.add(Progress.wd_one(m), n), wc.len_put(m, h, l))
      e45 = Equal.cong(Bool, Nat, b => Nat.add(Nat.add(Progress.wd_one(b), n), w), m, o, wc.mem_g(h, p, Nil{}))
      e36 = Equal.trans(Nat, Nat.add(List.length(&2, Nat, al), w), Nat.add(Nat.add(Progress.wd_one(o), n), w), Nat.add(n, Nat.add(Progress.wd_one(o), w)), Equal.trans(Nat, Nat.add(List.length(&2, Nat, al), w), Nat.add(Nat.add(Progress.wd_one(m), n), w), Nat.add(Nat.add(Progress.wd_one(o), n), w), e34, e45), wc.swap(o, n, w))
      e13 = Equal.trans(Nat, List.length(&2, Nat, Pr.ledger(t, lq)), Nat.add(List.length(&2, Nat, lq), w), Nat.add(List.length(&2, Nat, al), w), wc.go(t, q), e23)
      Equal.trans(Nat, List.length(&2, Nat, Pr.ledger(t, al)), List.length(&2, Nat, Pr.ledger(t, lq)), Nat.add(n, Nat.add(Progress.wd_one(o), w)), e01, Equal.trans(Nat, List.length(&2, Nat, Pr.ledger(t, lq)), Nat.add(List.length(&2, Nat, al), w), Nat.add(n, Nat.add(Progress.wd_one(o), w)), e13, e36))

def Progress.work_counts_distinct(xs):
  wc.go(xs, Nil{})
