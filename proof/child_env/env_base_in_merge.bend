# eukhe: the proof of LAW env_base_in_merge

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv
import ./base.bend as LA

def pce.app_in_r(xs: List<&2, Env.Var>, +ys: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, ys)) -> Env.In(v, List.append(&2, Env.Var, xs, ys)):
  match xs:
    case Nil{}:
      i
    case +h <> t:
      Inr{pce.app_in_r(t, ys, v, i)}

def pce.under_put_in(b: Bool, +h: Env.Var, +r: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, r)) -> Env.In(v, Env.under.put(b, h, r)):
  match b:
    case True{}:
      i
    case False{}:
      Inr{i}

# a member of the base the overlay does not name is in the filtered base
def pce.under_in(base: List<&2, Env.Var>, +over: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, base), +free: {Env.named(Env.Var.name(v), over) == False{} : Bool}) -> Env.In(v, Env.under(base, over)):
  match base:
    case Nil{}:
      match i:
    case +h <> +t:
      match i:
        case Inl{eq}:
          %eq : Env.In(v, Env.under.put(Env.named(Env.Var.name(_), over), _, Env.under(t, over)))
          %Equal.sym(Bool, Env.named(Env.Var.name(v), over), False{}, free) : Env.In(v, Env.under.put(_, v, Env.under(t, over)))
          Inl{{==}}
        case Inr{it}:
          pce.under_put_in(Env.named(Env.Var.name(h), over), h, Env.under(t, over), v, pce.under_in(t, over, v, it, free))

def ChildEnv.env_base_in_merge(base, over, v, i, free):
  +n = Env.Var.name(v)
  pce.app_in_r(over, Env.under(base, over), v, pce.under_in(base, over, v, i, Equal.trans(Bool, Env.named(n, over), ChildEnv.env_named(n, over), False{}, Equal.sym(Bool, ChildEnv.env_named(n, over), Env.named(n, over), LA.pce.named_eq(n, over)), free)))
