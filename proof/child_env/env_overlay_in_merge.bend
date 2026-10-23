# eukhe: the proof of LAW env_overlay_in_merge

import Base
import ../../bend/child_env.bend as Env
import ../../LAWS.bend as Laws

# The overlay over the base
# -------------------------

def pce.app_in_l(xs: List<&2, Env.Var>, +ys: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, xs)) -> Env.In(v, List.append(&2, Env.Var, xs, ys)):
  match xs:
    case Nil{}:
      match i:
    case +h <> t:
      match i:
        case Inl{eq}:
          Inl{eq}
        case Inr{it}:
          Inr{pce.app_in_l(t, ys, v, it)}

def Laws.env_overlay_in_merge(base, over, v, i):
  pce.app_in_l(over, Env.under(base, over), v, i)
