# eukhe: the proof of LAW env_child_from_merge

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv

# a member of the filtered list is a member of the list
def pce.put_in(b: Bool, +h: Env.Var, +r: List<&2, Env.Var>, -t: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.keep.put(b, h, r)), ih: Env.In(v, r) -> Env.In(v, t)) -> Env.In(v, h <> t):
  match b:
    case True{}:
      match i:
        case Inl{eq}:
          Inl{eq}
        case Inr{it}:
          Inr{ih(it)}
    case False{}:
      Inr{ih(i)}

def pce.keep_in(+reg: List<&2, String>, +ks: List<&2, String>, xs: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.keep(reg, ks, xs))) -> Env.In(v, xs):
  match xs:
    case Nil{}:
      match i:
    case +h <> +t:
      pce.put_in(Env.passes(reg, ks, Env.Var.name(h)), h, Env.keep(reg, ks, t), t, v, i, x => pce.keep_in(reg, ks, t, v, x))

def ChildEnv.env_child_from_merge(reg, keep, base, over, v, i):
  pce.keep_in(reg, keep, Env.merge(base, over), v, i)
