# eukhe: lemmas of the proof of LAW push_agrees_always: pair

import Base
import ../../../bend/optchat/fit.bend as OFit
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/node.bend as ONode

def pa.snd_cons(-n: ONode.Node, r: List<&2, ONode.Node> & List<&2, ONode.Node>) -> {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r) == Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.cons(n, r)) : List<&2, ONode.Node>}:
  (ms, out) = r
  {==}

# One step
# --------

def pa.fit_none(f: Nat, -t: List<&2, Bool>, -bud: Nat, -w: List<&2, ONode.Node>) -> {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(f, None{}, OFit.Last{}, t, bud, 0n, OInfo.All{1n}, w)) == w : List<&2, ONode.Node>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# a fit that merges a, then fits: one merge
def pa.base_fit(+f: Nat, +y: List<&2, ONode.Node>, +a: ONode.Node, +w: List<&2, ONode.Node>, +t: List<&2, Bool>, +bud: Nat,
  hc: {OFit.choose(OFit.Last{}, t, bud, 0n, OInfo.All{1n}, y) == Some{a} : Maybe<&2, ONode.Node>},
  hm: {OFit.merge(OInfo.All{1n}, y, a) == w : List<&2, ONode.Node>},
  hn: {OFit.choose(OFit.Last{}, t, bud, 0n, OInfo.All{1n}, w) == None{} : Maybe<&2, ONode.Node>})
  -> {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, OFit.choose(OFit.Last{}, t, bud, 0n, OInfo.All{1n}, y), OFit.Last{}, t, bud, 0n, OInfo.All{1n}, y)) == w : List<&2, ONode.Node>}:
  %Equal.sym(Maybe<&2, ONode.Node>, OFit.choose(OFit.Last{}, t, bud, 0n, OInfo.All{1n}, y), Some{a}, hc) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, _, OFit.Last{}, t, bud, 0n, OInfo.All{1n}, y)) == w : List<&2, ONode.Node>}
  %pa.snd_cons(ONode.Node.parent(a), OFit.fit.go(f, OFit.choose(OFit.Last{}, t, bud, 0n, OInfo.All{1n}, OFit.merge(OInfo.All{1n}, y, a)), OFit.Last{}, t, bud, 0n, OInfo.All{1n}, OFit.merge(OInfo.All{1n}, y, a))) : {_ == w : List<&2, ONode.Node>}
  %Equal.sym(List<&2, ONode.Node>, OFit.merge(OInfo.All{1n}, y, a), w, hm) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(f, OFit.choose(OFit.Last{}, t, bud, 0n, OInfo.All{1n}, _), OFit.Last{}, t, bud, 0n, OInfo.All{1n}, _)) == w : List<&2, ONode.Node>}
  %Equal.sym(Maybe<&2, ONode.Node>, OFit.choose(OFit.Last{}, t, bud, 0n, OInfo.All{1n}, w), None{}, hn) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(f, _, OFit.Last{}, t, bud, 0n, OInfo.All{1n}, w)) == w : List<&2, ONode.Node>}
  pa.fit_none(f, t, bud, w)
