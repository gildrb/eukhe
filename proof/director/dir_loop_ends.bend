# eukhe: the proof of LAW dir_loop_ends

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat

# The loop
# --------

# the loop has ended, or has fewer than k steps left
def pd.ok(l: Dr.Loop, k: Nat) -> Bool:
  match l:
    case Dr.Loop{n, s, e}:
      match e:
        case None{}:
          Nat.is_lt(n, k)
        case Some{x}:
          True{}

def pd.goon_ok(n: Nat, t: List<&2, Dr.Layer>, +s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat, +k: Nat, h: {Nat.is_lt(n, 1n+k) == True{} : Bool}) -> {pd.ok(Dr.go.on(n, t, s, vs, cap), k) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      h

def pd.settle_ok(d: Dr.Dec, +n: Nat, +s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat, +k: Nat, h: {Nat.is_lt(n, 1n+k) == True{} : Bool}) -> {pd.ok(Dr.settle(d, n, s, vs, cap), k) == True{} : Bool}:
  match d:
    case Dr.Dec{o, t}:
      match o:
        case Dr.Cont{}:
          pd.goon_ok(n, t, s, vs, cap, k, h)
        case Dr.Hand{}:
          {==}
        case Dr.Failed{}:
          {==}

# a tick takes one step off the loop
def pd.tick_ok(+cap: Nat, l: Dr.Loop, +vs: List<&2, Dr.Verdict>, +k: Nat, h: {pd.ok(l, 1n+k) == True{} : Bool}) -> {pd.ok(Dr.tick(cap, l, vs), k) == True{} : Bool}:
  match l:
    case Dr.Loop{+n, +s, e}:
      match e:
        case None{}:
          pd.settle_ok(Dr.decide(s, vs, cap), n, s, vs, cap, k, h)
        case Some{x}:
          {==}

def pd.ok_zero(l: Dr.Loop, h: {pd.ok(l, 0n) == True{} : Bool}) -> {Dr.ended(l) == True{} : Bool}:
  match l:
    case Dr.Loop{+n, +s, e}:
      match e:
        case None{}:
          LLogicLogic.pt.lt_zero({Dr.ended(Dr.Loop{n, s, None{}}) == True{} : Bool}, n, h)
        case Some{x}:
          {==}

# a loop with fewer steps left than verdict lists has ended after them
def pd.ends_go(vss: List<&2, List<&2, Dr.Verdict>>, +cap: Nat, +l: Dr.Loop, h: {pd.ok(l, List.length(&2, List<&2, Dr.Verdict>, vss)) == True{} : Bool}) -> {Dr.ended(Dr.run(vss, cap, l)) == True{} : Bool}:
  match vss:
    case Nil{}:
      pd.ok_zero(l, h)
    case +vs <> +rest:
      pd.ends_go(rest, cap, Dr.tick(cap, l, vs), pd.tick_ok(cap, l, vs, List.length(&2, List<&2, Dr.Verdict>, rest), h))

def pd.lt_len(+n: Nat, +k: Nat, e: {k == 1n+n : Nat}) -> {Nat.is_lt(n, k) == True{} : Bool}:
  %Equal.sym(Nat, k, 1n+n, e) : {Nat.is_lt(n, _) == True{} : Bool}
  LNat.pd.lt_succ(n)

def pd.dir_loop_ends(+n: Nat, +s: List<&2, Dr.Layer>, +vss: List<&2, List<&2, Dr.Verdict>>, +cap: Nat, long: {List.length(&2, List<&2, Dr.Verdict>, vss) == 1n+n : Nat}) -> {Dr.ended(Dr.run(vss, cap, Dr.Loop{n, s, None{}})) == True{} : Bool}:
  pd.ends_go(vss, cap, Dr.Loop{n, s, None{}}, pd.lt_len(n, List.length(&2, List<&2, Dr.Verdict>, vss), long))

def Director.dir_loop_ends(n, s, vss, cap, long):
  pd.dir_loop_ends(n, s, vss, cap, long)
