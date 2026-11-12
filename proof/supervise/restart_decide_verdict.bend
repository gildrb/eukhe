# eukhe: the proof of LAW restart_decide_verdict
#
# PROOF: the count is the decided budget's (step unfolds). The pause: the code
# doubles base capped at max after every doubling (Su.backoff.go); a cap
# x -> min(x, m) is Nat.min (ps.rs_cap); capping before a doubling caps
# the same as after it (ps.rs_cap_dbl: past max both are max); so e capped
# doublings are min(base doubled e times, max) (ps.rs_go), and base doubled
# e times is 2^e * base (ps.rs_twice).

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise
import ../autoresearch/base/conf/nat.bend as CN

def ps.rs_cap_succ(b: Bool, p: Nat, q: Nat) -> {Su.backoff.cap(b, 1n+p, 1n+q) == 1n+Su.backoff.cap(b, p, q) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the cap is Nat.min
def ps.rs_cap(+x: Nat, +m: Nat) -> {Su.backoff.cap(Nat.is_le(x, m), x, m) == Nat.min(x, m) : Nat}:
  match x m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %Equal.sym(Nat, Su.backoff.cap(Nat.is_le(p, q), 1n+p, 1n+q), 1n+Su.backoff.cap(Nat.is_le(p, q), p, q), ps.rs_cap_succ(Nat.is_le(p, q), p, q)) : {_ == 1n+Nat.min(p, q) : Nat}
      %ps.rs_cap(p, q) : {1n+Su.backoff.cap(Nat.is_le(p, q), p, q) == 1n+_ : Nat}
      {==}

# not at most m stays not at most m one more up
def ps.rs_gt_succ(k: Nat, m: Nat, h: {Nat.is_le(k, m) == False{} : Bool}) -> {Nat.is_le(1n+k, m) == False{} : Bool}:
  match k m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      CN.ac.tf({Nat.is_le(1n, 1n+q) == False{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ps.rs_gt_succ(p, q, h)

# a + x is not at most m when x is not
def ps.rs_gt_add(a: Nat, +x: Nat, +m: Nat, h: {Nat.is_le(x, m) == False{} : Bool}) -> {Nat.is_le(Nat.add(a, x), m) == False{} : Bool}:
  match a:
    case 0n:
      h
    case 1n++p:
      ps.rs_gt_succ(Nat.add(p, x), m, ps.rs_gt_add(p, x, m, h))

def ps.rs_lt_succ(q: Nat) -> {Nat.is_le(1n+q, q) == False{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      ps.rs_lt_succ(r)

# max doubled is max, capped at max
def ps.rs_max(m: Nat) -> {Su.backoff.cap(Nat.is_le(Nat.add(m, m), m), Nat.add(m, m), m) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++q:
      %Equal.sym(Bool, Nat.is_le(Nat.add(q, 1n+q), q), False{}, ps.rs_gt_add(q, 1n+q, q, ps.rs_lt_succ(q))) : {Su.backoff.cap(_, 1n+Nat.add(q, 1n+q), 1n+q) == 1n+q : Nat}
      {==}

def ps.rs_cap_dbl.at(b: Bool, +y: Nat, +m: Nat, e: {Nat.is_le(y, m) == b : Bool}) -> {Su.backoff.cap(Nat.is_le(Nat.add(Su.backoff.cap(b, y, m), Su.backoff.cap(b, y, m)), m), Nat.add(Su.backoff.cap(b, y, m), Su.backoff.cap(b, y, m)), m) == Su.backoff.cap(Nat.is_le(Nat.add(y, y), m), Nat.add(y, y), m) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(y, y), m), False{}, ps.rs_gt_add(y, y, m, e)) : {Su.backoff.cap(Nat.is_le(Nat.add(m, m), m), Nat.add(m, m), m) == Su.backoff.cap(_, Nat.add(y, y), m) : Nat}
      ps.rs_max(m)

# capping before a doubling caps as after it
def ps.rs_cap_dbl(+y: Nat, +m: Nat) -> {Su.backoff.cap(Nat.is_le(Nat.add(Su.backoff.cap(Nat.is_le(y, m), y, m), Su.backoff.cap(Nat.is_le(y, m), y, m)), m), Nat.add(Su.backoff.cap(Nat.is_le(y, m), y, m), Su.backoff.cap(Nat.is_le(y, m), y, m)), m) == Su.backoff.cap(Nat.is_le(Nat.add(y, y), m), Nat.add(y, y), m) : Nat}:
  ps.rs_cap_dbl.at(Nat.is_le(y, m), y, m, {==})

# y doubled e times
def ps.rs_dbl(e: Nat, +y: Nat) -> Nat:
  match e:
    case 0n:
      y
    case 1n+p:
      ps.rs_dbl(p, Nat.add(y, y))

# e capped doublings of y capped are min(y doubled e times, m)
def ps.rs_go(e: Nat, +m: Nat, +y: Nat) -> {Su.backoff.go(e, m, Su.backoff.cap(Nat.is_le(y, m), y, m)) == Nat.min(ps.rs_dbl(e, y), m) : Nat}:
  match e:
    case 0n:
      ps.rs_cap(y, m)
    case 1n+p:
      +c = Su.backoff.cap(Nat.is_le(y, m), y, m)
      %Equal.sym(Nat, Su.backoff.cap(Nat.is_le(Nat.add(c, c), m), Nat.add(c, c), m), Su.backoff.cap(Nat.is_le(Nat.add(y, y), m), Nat.add(y, y), m), ps.rs_cap_dbl(y, m)) : {Su.backoff.go(p, m, _) == Nat.min(ps.rs_dbl(p, Nat.add(y, y)), m) : Nat}
      ps.rs_go(p, m, Nat.add(y, y))

# P (b + b) = 2 P b
def ps.rs_two(+p: Nat, +b: Nat) -> {Nat.mul(p, Nat.add(b, b)) == Nat.mul(Nat.mul(2n, p), b) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(2n, p), b), Nat.mul(2n, Nat.mul(p, b)), CN.ac.mul_assoc(2n, p, b)) : {Nat.mul(p, Nat.add(b, b)) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(p, b), 0n), Nat.mul(p, b), CN.ac.add_zero(Nat.mul(p, b))) : {Nat.mul(p, Nat.add(b, b)) == Nat.add(Nat.mul(p, b), _) : Nat}
  %CN.ac.mul_comm(Nat.add(b, b), p) : {_ == Nat.add(Nat.mul(p, b), Nat.mul(p, b)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(b, b), p), Nat.add(Nat.mul(b, p), Nat.mul(b, p)), CN.ac.mul_add(b, b, p)) : {_ == Nat.add(Nat.mul(p, b), Nat.mul(p, b)) : Nat}
  %CN.ac.mul_comm(p, b) : {Nat.add(_, _) == Nat.add(Nat.mul(p, b), Nat.mul(p, b)) : Nat}
  {==}

# b doubled e times is 2^e b
def ps.rs_twice(e: Nat, +b: Nat) -> {ps.rs_dbl(e, b) == Nat.mul(Supervise.restart_pow2(e), b) : Nat}:
  match e:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, CN.ac.add_zero(b))
    case 1n++p:
      +q = Supervise.restart_pow2(p)
      Equal.trans(Nat, ps.rs_dbl(p, Nat.add(b, b)), Nat.mul(q, Nat.add(b, b)), Nat.mul(Nat.mul(2n, q), b), ps.rs_twice(p, Nat.add(b, b)), ps.rs_two(q, b))

def ps.rs_verdict(b: Bool, +c: Su.Cfg, +n: Nat) -> {Su.verdict.put(b, c, n) == Supervise.restart_verdict_put(b, c, n) : Su.Verdict}:
  match b:
    case True{}:
      {==}
    case False{}:
      match c:
        case Su.Cfg{k, w, +b0, +m}:
          +e = Nat.min(Nat.sub(n, 1n), 7n)
          %Equal.sym(Nat, Su.backoff.go(e, m, Su.backoff.cap(Nat.is_le(b0, m), b0, m)), Nat.min(ps.rs_dbl(e, b0), m), ps.rs_go(e, m, b0)) : {Su.Relaunch{n, _} == Su.Relaunch{n, Nat.min(Nat.mul(Supervise.restart_pow2(e), b0), m)} : Su.Verdict}
          %Equal.sym(Nat, ps.rs_dbl(e, b0), Nat.mul(Supervise.restart_pow2(e), b0), ps.rs_twice(e, b0)) : {Su.Relaunch{n, Nat.min(_, m)} == Su.Relaunch{n, Nat.min(Nat.mul(Supervise.restart_pow2(e), b0), m)} : Su.Verdict}
          {==}

def Supervise.restart_decide_verdict(c, s, g):
  match s:
    case Su.St{a, n}:
      ps.rs_verdict(Nat.is_lt(Su.Cfg.k(c), 1n+List.length(&2, Nat, Su.keep(Su.Cfg.w(c), Su.older(g, a)))), c, 1n+List.length(&2, Nat, Su.keep(Su.Cfg.w(c), Su.older(g, a))))
