# eukhe: the proof of LAW optchat_sibling
# Bits.flip keeps the level and turns the lowest bit: an even index k
# (low bit 0, or no bit) becomes k + 1, an odd one k - 1 (sb.idx); the
# parity S.other reads (k mod 2 == 1) is the lowest bit's (LAB.ob.mod2).

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/bits.bend as LAB
import ./base/queries.bend as LQ

# twice a number is even, one more odd
def sb.pr_even(v: Nat) -> {LAB.ob.pr(Nat.double(v)) == False{} : Bool}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      sb.pr_even(p)

def sb.pr_odd(v: Nat) -> {LAB.ob.pr(1n+Nat.double(v)) == True{} : Bool}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      sb.pr_odd(p)

# the other half of an index, by its bits
def sb.idx(i: List<&2, Bool>) -> {OBits.Bits.val(ONode.Bits.flip(i)) == S.other(OBits.Bits.val(i)) : Nat}:
  match i:
    case Nil{}:
      {==}
    case False{} <> +t:
      +v = Nat.double(OBits.Bits.val(t))
      %Equal.sym(Bool, Nat.is_eq(Nat.mod(v, 2n), 1n), LAB.ob.pr(v), LAB.ob.mod2(v)) : {1n+v == S.other.of(_, v) : Nat}
      %Equal.sym(Bool, LAB.ob.pr(v), False{}, sb.pr_even(OBits.Bits.val(t))) : {1n+v == S.other.of(_, v) : Nat}
      {==}
    case True{} <> t:
      match t:
        case Nil{}:
          {==}
        case +h <> +r:
          +v = Nat.double(OBits.Bits.val(h <> r))
          %Equal.sym(Bool, Nat.is_eq(Nat.mod(1n+v, 2n), 1n), LAB.ob.pr(1n+v), LAB.ob.mod2(1n+v)) : {v == S.other.of(_, 1n+v) : Nat}
          %Equal.sym(Bool, LAB.ob.pr(1n+v), True{}, sb.pr_odd(OBits.Bits.val(h <> r))) : {v == S.other.of(_, 1n+v) : Nat}
          Equal.sym(Nat, Nat.sub(v, 0n), v, LQ.oq.sub0(v))

def OptchatQueries.optchat_sibling(n):
  match n:
    case ONode.Node{l, i}:
      ({==}, sb.idx(i))
