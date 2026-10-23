# eukhe: the proof of LAW dir_loop_stack_bounded

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

# the stack a step that ends keeps is within cap too
def pd.kept_bounded(+s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat, fits: {Nat.is_le(List.length(&2, Dr.Layer, s), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.kept(s, vs, cap)), cap) == True{} : Bool}:
  LA.pd.go_bounded(s, vs, Nat.is_lt(List.length(&2, Dr.Layer, s), cap), True{}, cap, 0n, fits, {==})

def pd.goon_bounded(n: Nat, t: List<&2, Dr.Layer>, +s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat, ht: {Nat.is_le(List.length(&2, Dr.Layer, t), cap) == True{} : Bool}, hk: {Nat.is_le(List.length(&2, Dr.Layer, Dr.kept(s, vs, cap)), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(Dr.go.on(n, t, s, vs, cap))), cap) == True{} : Bool}:
  match n:
    case 0n:
      hk
    case 1n+m:
      ht

def pd.settle_bounded(d: Dr.Dec, +n: Nat, +s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat, hd: {Nat.is_le(List.length(&2, Dr.Layer, Dr.Dec.stack(d)), cap) == True{} : Bool}, hk: {Nat.is_le(List.length(&2, Dr.Layer, Dr.kept(s, vs, cap)), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(Dr.settle(d, n, s, vs, cap))), cap) == True{} : Bool}:
  match d:
    case Dr.Dec{o, t}:
      match o:
        case Dr.Cont{}:
          pd.goon_bounded(n, t, s, vs, cap, hd, hk)
        case Dr.Hand{}:
          hk
        case Dr.Failed{}:
          hk

# one loop step keeps the stack within cap
def pd.tick_bounded(+cap: Nat, l: Dr.Loop, +vs: List<&2, Dr.Verdict>, +h: {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(l)), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(Dr.tick(cap, l, vs))), cap) == True{} : Bool}:
  match l:
    case Dr.Loop{+n, +s, e}:
      match e:
        case None{}:
          pd.settle_bounded(Dr.decide(s, vs, cap), n, s, vs, cap, LA.pd.dir_stack_bounded(s, vs, cap, h), pd.kept_bounded(s, vs, cap, h))
        case Some{x}:
          h

def pd.dir_loop_stack_bounded(vss: List<&2, List<&2, Dr.Verdict>>, +cap: Nat, +l: Dr.Loop, fits: {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(l)), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(Dr.run(vss, cap, l))), cap) == True{} : Bool}:
  match vss:
    case Nil{}:
      fits
    case +vs <> rest:
      pd.dir_loop_stack_bounded(rest, cap, Dr.tick(cap, l, vs), pd.tick_bounded(cap, l, vs, fits))

def Director.dir_loop_stack_bounded(vss, cap, l, fits):
  pd.dir_loop_stack_bounded(vss, cap, l, fits)
