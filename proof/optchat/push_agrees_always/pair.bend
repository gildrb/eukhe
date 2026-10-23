# eukhe: lemmas of the proof of LAW push_agrees_always: pair

import Base
import ../../../bend/optchat.bend as O

def pa.snd_cons(-n: O.Node, r: List<&2, O.Node> & List<&2, O.Node>) -> {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, r) == Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.cons(n, r)) : List<&2, O.Node>}:
  (ms, out) = r
  {==}

# One step
# --------

def pa.fit_none(f: Nat, -t: List<&2, Bool>, -bud: Nat, -w: List<&2, O.Node>) -> {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(f, None{}, O.Last{}, t, bud, 0n, O.All{1n}, w)) == w : List<&2, O.Node>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# a fit that merges a, then fits: one merge
def pa.base_fit(+f: Nat, +y: List<&2, O.Node>, +a: O.Node, +w: List<&2, O.Node>, +t: List<&2, Bool>, +bud: Nat,
  hc: {O.choose(O.Last{}, t, bud, 0n, O.All{1n}, y) == Some{a} : Maybe<&2, O.Node>},
  hm: {O.merge(O.All{1n}, y, a) == w : List<&2, O.Node>},
  hn: {O.choose(O.Last{}, t, bud, 0n, O.All{1n}, w) == None{} : Maybe<&2, O.Node>})
  -> {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, O.choose(O.Last{}, t, bud, 0n, O.All{1n}, y), O.Last{}, t, bud, 0n, O.All{1n}, y)) == w : List<&2, O.Node>}:
  %Equal.sym(Maybe<&2, O.Node>, O.choose(O.Last{}, t, bud, 0n, O.All{1n}, y), Some{a}, hc) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, _, O.Last{}, t, bud, 0n, O.All{1n}, y)) == w : List<&2, O.Node>}
  %pa.snd_cons(O.Node.parent(a), O.fit.go(f, O.choose(O.Last{}, t, bud, 0n, O.All{1n}, O.merge(O.All{1n}, y, a)), O.Last{}, t, bud, 0n, O.All{1n}, O.merge(O.All{1n}, y, a))) : {_ == w : List<&2, O.Node>}
  %Equal.sym(List<&2, O.Node>, O.merge(O.All{1n}, y, a), w, hm) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(f, O.choose(O.Last{}, t, bud, 0n, O.All{1n}, _), O.Last{}, t, bud, 0n, O.All{1n}, _)) == w : List<&2, O.Node>}
  %Equal.sym(Maybe<&2, O.Node>, O.choose(O.Last{}, t, bud, 0n, O.All{1n}, w), None{}, hn) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(f, _, O.Last{}, t, bud, 0n, O.All{1n}, w)) == w : List<&2, O.Node>}
  pa.fit_none(f, t, bud, w)
