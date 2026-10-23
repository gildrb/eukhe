# eukhe: the proof of LAW job_feed_fills

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ../base.bend as L
import ./base.bend as LA

# n == min(m, n) when n <= m
def pj.min_of_ge(m: Nat, n: Nat, h: {Nat.is_le(n, m) == True{} : Bool}) -> {n == Nat.min(m, n) : Nat}:
  match m n:
    case 0n 0n:
      {==}
    case 0n 1n+np:
      L.pj.absurdF({1n+np == Nat.min(0n, 1n+np) : Nat}, h)
    case 1n+mp 0n:
      {==}
    case 1n+mp 1n+np:
      %pj.min_of_ge(mp, np, h) : {1n+np == 1n+_ : Nat}
      {==}

def pj.lt_le(t: Nat, n: Nat, h: {Nat.is_lt(t, n) == True{} : Bool}) -> {Nat.is_le(t, n) == True{} : Bool}:
  match t n:
    case 0n 0n:
      L.pj.absurdF({Nat.is_le(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+np:
      {==}
    case 1n+tp 0n:
      L.pj.absurdF({Nat.is_le(1n+tp, 0n) == True{} : Bool}, h)
    case 1n+tp 1n+np:
      pj.lt_le(tp, np, h)

# t - a <= n when t < a + n
def pj.sub_le_of_lt(a: Nat, t: Nat, +n: Nat, h: {Nat.is_lt(t, Nat.add(a, n)) == True{} : Bool}) -> {Nat.is_le(Nat.sub(t, a), n) == True{} : Bool}:
  match a t:
    case 0n 0n:
      L.pj.le0(n)
    case 0n 1n+tp:
      pj.lt_le(1n+tp, n, h)
    case 1n+ap 0n:
      L.pj.le0(n)
    case 1n+ap 1n+tp:
      pj.sub_le_of_lt(ap, tp, n, h)

def pj.job_feed_fills(+t: Nat, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +n: Nat, below: {Nat.is_le(Nat.add(k, d), t) == True{} : Bool}, over: {Nat.is_lt(t, Nat.add(Nat.add(k, d), n)) == True{} : Bool}) -> {Jb.J.total(Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n})) == t : Nat}:
  +a = Nat.add(k, d)
  %LA.pj.out_total(cap, k, d, Nat.min(n, Nat.sub(Nat.sub(t, k), d))) : {_ == t : Nat}
  %LA.pj.sub_sub_r(t, k, d) : {Nat.add(a, Nat.min(n, _)) == t : Nat}
  %pj.min_of_ge(n, Nat.sub(t, a), pj.sub_le_of_lt(a, t, n, over)) : {Nat.add(a, _) == t : Nat}
  %LA.pj.add_sub(a, t, below) : {_ == t : Nat}
  {==}

def Job.job_feed_fills(t, cap, k, d, n, below, over):
  pj.job_feed_fills(t, cap, k, d, n, below, over)
