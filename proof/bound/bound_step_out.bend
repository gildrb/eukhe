# eukhe: the proof of LAW bound_step_out: the text reads back whole; the reply is the decision's number

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def so.pair(r: Bd.St & Bd.Act) -> {FBd.step.out(r) == (FBd.Run{Bound.bd_fst.act(r)}, Bound.bd_spell([Bound.bd_act(Bound.bd_snd.act(r))])) : FBd.St & String}:
  match r:
    case (s, a):
      match a:
        case Bd.Drop{}:
          {==}
        case Bd.Store{}:
          {==}
        case Bd.Trim{}:
          {==}

def so.ev(+s: Bd.St, +n: Nat, +k: Nat, o: Bool) -> {FBd.step.ev(FBd.Run{s}, FBd.ev([0n, n, k, Bound.bd_bit(o)])) == (FBd.Run{Bound.bd_fst.act(Bd.out(s, n, k, o))}, Bound.bd_spell([Bound.bd_act(Bound.bd_snd.act(Bd.out(s, n, k, o)))])) : FBd.St & String}:
  match o:
    case False{}:
      so.pair(Bd.out(s, n, k, False{}))
    case True{}:
      so.pair(Bd.out(s, n, k, True{}))

def Bound.bound_step_out(s, n, k, o, h):
  +xs = {[0n, n, k, Bound.bd_bit(o)] : List<&2, Nat>}
  %LBound.bnd.read(xs, h) : {FBd.step.got(FBd.Run{s}, _) == (FBd.Run{Bound.bd_fst.act(Bd.out(s, n, k, o))}, Bound.bd_spell([Bound.bd_act(Bound.bd_snd.act(Bd.out(s, n, k, o)))])) : FBd.St & String}
  so.ev(s, n, k, o)
