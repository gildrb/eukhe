# eukhe: the proof of LAW bound_shut_refuses: the refused state answers before it reads the event

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def shr.end(b: Bool, xs: List<&2, Nat>) -> {FBd.step.end(FBd.Shut{}, b, xs) == (FBd.Shut{}, Wr.err("bound: the open was refused")) : FBd.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def shr.got(r: Wr.Dec<List<&2, Nat>>) -> {FBd.step.got(FBd.Shut{}, r) == (FBd.Shut{}, Wr.err("bound: the open was refused")) : FBd.St & String}:
  match r:
    case Wr.Got{xs, rest}:
      shr.end(Wr.end(rest), xs)
    case Wr.Bad{}:
      {==}

def Bound.bound_shut_refuses(s):
  shr.got(Wr.get_list(~Nat, ~Wr.get_nat, s))
