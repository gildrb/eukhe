# eukhe: the proof of LAW bound_refused_open_refuses_all: a refused open opens the refused state (bound_open_refuses), which answers every event before it reads it and stays refused

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound
import ./bound_open_refuses.bend as PBoundOpenRefuses

def rr.end(b: Bool, xs: List<&2, Nat>) -> {FBd.step.end(FBd.Shut{}, b, xs) == (FBd.Shut{}, Wr.err("bound: the open was refused")) : FBd.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rr.got(r: Wr.Dec<List<&2, Nat>>) -> {FBd.step.got(FBd.Shut{}, r) == (FBd.Shut{}, Wr.err("bound: the open was refused")) : FBd.St & String}:
  match r:
    case Wr.Got{xs, rest}:
      rr.end(Wr.end(rest), xs)
    case Wr.Bad{}:
      {==}

def rr.all(es: List<&2, String>) -> {Bound.bd_steps(es, FBd.Shut{}) == Bound.bd_refused(es) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      %Equal.sym(FBd.St & String, FBd.step(FBd.Shut{}, e), (FBd.Shut{}, Wr.err("bound: the open was refused")), rr.got(Wr.get_list(~Nat, ~Wr.get_nat, e))) : {Bound.bd_snd.step(_) <> Bound.bd_steps(rest, Bound.bd_fst.step(_)) == Bound.bd_refused(e <> rest) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, ys => Wr.err("bound: the open was refused") <> ys, Bound.bd_steps(rest, FBd.Shut{}), Bound.bd_refused(rest), rr.all(rest))

def Bound.bound_refused_open_refuses_all(s, es, no):
  %Equal.sym(FBd.St & String, FBd.open(s), (FBd.Shut{}, Wr.err("bound: malformed open")), Bound.bound_open_refuses(s, no)) : {Bound.bd_steps(es, Bound.bd_fst.step(_)) == Bound.bd_refused(es) : List<&2, String>}
  rr.all(es)
