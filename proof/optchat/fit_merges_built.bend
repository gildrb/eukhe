# eukhe: the proof of LAW fit_merges_built

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pf.fst_cons(-n: O.Node, r: List<&2, O.Node> & List<&2, O.Node>) -> {n <> Pair.fst(List<&2, O.Node>, List<&2, O.Node>, r) == Pair.fst(List<&2, O.Node>, List<&2, O.Node>, O.fit.cons(n, r)) : List<&2, O.Node>}:
  (ms, out) = r
  {==}

# A fit merges into built parents
# -------------------------------

def pf.built_step(-info: O.Info, -v: List<&2, O.Node>, -a: O.Node, -rest: List<&2, O.Node>, cm: LA.pf.Cand(info, v, Some{a}), br: S.Built(info, rest)) -> S.Built(info, O.Node.parent(a) <> rest):
  (hs, bs) = cm
  (bs, br)

def pf.fit_built(fuel: Nat, c: Maybe<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>, cm: LA.pf.Cand(info, v, c))
  -> S.Built(info, Pair.fst(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(fuel, c, m, t, budget, ph, info, v))):
  match fuel c:
    case 0n _:
      Unit{}
    case 1n+f None{}:
      Unit{}
    case 1n++f Some{+a}:
      %pf.fst_cons(O.Node.parent(a), O.fit.go(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a))) : S.Built(info, _)
      pf.built_step(info, v, a, Pair.fst(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a))), cm, pf.fit_built(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a), LA.pf.choose_sound(m, t, budget, ph, info, O.merge(info, v, a))))

def fit_merges_built(+m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>)
  -> S.Built(info, Pair.fst(List<&2, O.Node>, List<&2, O.Node>, O.fit(m, t, budget, ph, info, v))):
  pf.fit_built(List.length(&2, O.Node, v), O.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v, LA.pf.choose_sound(m, t, budget, ph, info, v))

def Laws.fit_merges_built(m, t, budget, ph, info, v):
  fit_merges_built(m, t, budget, ph, info, v)
