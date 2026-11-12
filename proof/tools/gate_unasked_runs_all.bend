# eukhe: the proof of LAW gate_unasked_runs_all
# By induction on the script: each step runs unasked and takes no answer
# (LA.tgh.free), the rest runs whole.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pgu.all(ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, +ans: List<&2, Bool>, +free: {Tools.tg_all_free(ss, auto) == True{} : Bool}) -> {Tl.exec(ss, auto, ans) == Tl.Ran{ss, Tl.Finished{}} : Tl.Ran}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      Equal.trans(Tl.Ran, Tl.exec(s <> rest, auto, ans), Tl.ran.add(s, Tl.exec(rest, auto, ans)), Tl.Ran{s <> rest, Tl.Finished{}}, LA.tgh.free(s, rest, auto, ans, LA.tgh.and_l(Tools.tg_free(s, auto), Tools.tg_all_free(rest, auto), free)), Equal.cong(Tl.Ran, Tl.Ran, z => Tl.ran.add(s, z), Tl.exec(rest, auto, ans), Tl.Ran{rest, Tl.Finished{}}, pgu.all(rest, auto, ans, LA.tgh.and_r(Tools.tg_free(s, auto), Tools.tg_all_free(rest, auto), free))))

def Tools.gate_unasked_runs_all(ss, auto, ans, free):
  pgu.all(ss, auto, ans, free)
