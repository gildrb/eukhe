# eukhe: lemmas the proofs of two or more areas share: optchat

import Base
import ../../bend/optchat.bend as O
import ./bool/misc.bend as LBoolMisc
import ./nat/is_eq.bend as LNatIsEq

def pf.bits_cmp_refl(bs: List<&2, Bool>) -> {EQ{} == O.Bits.cmp(bs, bs) : Cmp}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +r:
      %pf.bits_cmp_refl(r) : {EQ{} == O.Cmp.then(_, Bool.cmp(b, b)) : Cmp}
      LBoolMisc.pf.bool_cmp_refl(b)

def pf.node_eq_refl(n: O.Node) -> {True{} == O.Node.eq(n, n) : Bool}:
  match n:
    case O.Node{+l, +i}:
      %LNatIsEq.pf.nat_eq_refl(l) : {True{} == Bool.and(_, O.Bits.same(i, i)) : Bool}
      %pf.bits_cmp_refl(i) : {True{} == Cmp.is_eq(_) : Bool}
      {==}
