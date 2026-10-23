# eukhe: the proof of LAW fit_merges_built

import Base
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/spec.bend as S
import ../../laws/optchat.bend as Optchat
import ./base.bend as LA

def pf.fst_cons(-n: ONode.Node, r: List<&2, ONode.Node> & List<&2, ONode.Node>) -> {n <> Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, r) == Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.cons(n, r)) : List<&2, ONode.Node>}:
  (ms, out) = r
  {==}

# A fit merges into built parents
# -------------------------------

def pf.built_step(-info: OInfo.Info, -v: List<&2, ONode.Node>, -a: ONode.Node, -rest: List<&2, ONode.Node>, cm: LA.pf.Cand(info, v, Some{a}), br: S.Built(info, rest)) -> S.Built(info, ONode.Node.parent(a) <> rest):
  (hs, bs) = cm
  (bs, br)

def pf.fit_built(fuel: Nat, c: Maybe<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, cm: LA.pf.Cand(info, v, c))
  -> S.Built(info, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(fuel, c, m, t, budget, ph, info, v))):
  match fuel c:
    case 0n _:
      Unit{}
    case 1n+f None{}:
      Unit{}
    case 1n++f Some{+a}:
      %pf.fst_cons(ONode.Node.parent(a), OFit.fit.go(f, OFit.choose(m, t, budget, ph, info, OFit.merge(info, v, a)), m, t, budget, ph, info, OFit.merge(info, v, a))) : S.Built(info, _)
      pf.built_step(info, v, a, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(f, OFit.choose(m, t, budget, ph, info, OFit.merge(info, v, a)), m, t, budget, ph, info, OFit.merge(info, v, a))), cm, pf.fit_built(f, OFit.choose(m, t, budget, ph, info, OFit.merge(info, v, a)), m, t, budget, ph, info, OFit.merge(info, v, a), LA.pf.choose_sound(m, t, budget, ph, info, OFit.merge(info, v, a))))

def fit_merges_built(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>)
  -> S.Built(info, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit(m, t, budget, ph, info, v))):
  pf.fit_built(List.length(&2, ONode.Node, v), OFit.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v, LA.pf.choose_sound(m, t, budget, ph, info, v))

def Optchat.fit_merges_built(m, t, budget, ph, info, v):
  fit_merges_built(m, t, budget, ph, info, v)
