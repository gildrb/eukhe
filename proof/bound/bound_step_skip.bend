# eukhe: the proof of LAW bound_step_skip: the skip reads back whole; the reply is the clear's bit

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def sk.pair(r: Bd.St & Bool) -> {FBd.step.skip(r) == (FBd.Run{Bound.bd_fst.skip(r)}, Bound.bd_spell([Bound.bd_bit(Bound.bd_snd.skip(r))])) : FBd.St & String}:
  match r:
    case (s, a):
      match a:
        case True{}:
          {==}
        case False{}:
          {==}

def sk.ev(+s: Bd.St, +n: Nat, +k: Nat, o: Bool) -> {FBd.step.ev(FBd.Run{s}, FBd.ev([1n, n, k, Bound.bd_bit(o)])) == (FBd.Run{Bound.bd_fst.skip(Bd.skip(s, n, k, o))}, Bound.bd_spell([Bound.bd_bit(Bound.bd_snd.skip(Bd.skip(s, n, k, o)))])) : FBd.St & String}:
  match o:
    case False{}:
      sk.pair(Bd.skip(s, n, k, False{}))
    case True{}:
      sk.pair(Bd.skip(s, n, k, True{}))

def Bound.bound_step_skip(s, n, k, o, h):
  +xs = {[1n, n, k, Bound.bd_bit(o)] : List<&2, Nat>}
  %LBound.bnd.read(xs, h) : {FBd.step.got(FBd.Run{s}, _) == (FBd.Run{Bound.bd_fst.skip(Bd.skip(s, n, k, o))}, Bound.bd_spell([Bound.bd_bit(Bound.bd_snd.skip(Bd.skip(s, n, k, o)))])) : FBd.St & String}
  sk.ev(s, n, k, o)
