# eukhe: lemmas of the proof of LAW push_agrees_always: nat

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/node.bend as ONode
import ../../base/logic/nat.bend as LLogicNat
import ../../base/nat.bend as LNat
import ./logic.bend as LLLogic

def pa.add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      LLogicNat.pa.succ(Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), pa.add_assoc(p, b, c))

def pa.double_add(a: Nat, +b: Nat) -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      LLogicNat.pa.succ(1n+Nat.double(Nat.add(p, b)), 1n+Nat.add(Nat.double(p), Nat.double(b)), LLogicNat.pa.succ(Nat.double(Nat.add(p, b)), Nat.add(Nat.double(p), Nat.double(b)), pa.double_add(p, b)))

# b + 1 + k is above b
def pa.gt_add(b: Nat, -k: Nat) -> {Nat.is_gt(Nat.add(b, 1n+k), b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      pa.gt_add(p, k)

def pa.gt_succ(n: Nat) -> {Nat.is_gt(1n+n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pa.gt_succ(p)

def pa.gt_self(n: Nat) -> {Nat.is_gt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pa.gt_self(p)

def pa.cmp_self(n: Nat) -> {Nat.cmp(n, n) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pa.cmp_self(p)

def pa.sh_add(+l: Nat, +a: Nat, +b: Nat) -> {LLLogic.pa.sh(l, Nat.add(a, b)) == Nat.add(LLLogic.pa.sh(l, a), LLLogic.pa.sh(l, b)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.double(LLLogic.pa.sh(p, Nat.add(a, b))), Nat.double(Nat.add(LLLogic.pa.sh(p, a), LLLogic.pa.sh(p, b))), Nat.add(Nat.double(LLLogic.pa.sh(p, a)), Nat.double(LLLogic.pa.sh(p, b))), Equal.cong(Nat, Nat, x => Nat.double(x), LLLogic.pa.sh(p, Nat.add(a, b)), Nat.add(LLLogic.pa.sh(p, a), LLLogic.pa.sh(p, b)), pa.sh_add(p, a, b)), pa.double_add(LLLogic.pa.sh(p, a), LLLogic.pa.sh(p, b)))

def pa.sh_double(+l: Nat, +x: Nat) -> {LLLogic.pa.sh(l, Nat.double(x)) == Nat.double(LLLogic.pa.sh(l, x)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, y => Nat.double(y), LLLogic.pa.sh(p, Nat.double(x)), Nat.double(LLLogic.pa.sh(p, x)), pa.sh_double(p, x))

def pa.add_bits(x: Bool, y: Bool, +P: Nat, +Q: Nat) -> {Nat.add(OBits.bit(x, P), OBits.bit(y, Q)) == OBits.bit(x, OBits.bit(y, Nat.add(P, Q))) : Nat}:
  match x y:
    case False{} False{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      LNat.pa.add_succ(P, Q)
    case True{} True{}:
      LLogicNat.pa.succ(Nat.add(P, 1n+Q), 1n+Nat.add(P, Q), LNat.pa.add_succ(P, Q))

def pa.good_lift.eq(d: Bool, +k: Nat, +R: Nat, -S: Nat, e: {Nat.double(S) == Nat.add(Nat.double(k), 4n+Nat.double(R)) : Nat})
  -> {Nat.double(S) == Nat.add(LLLogic.pa.bit_k(d, k), 2n+LLLogic.pa.Bd(d, R)) : Nat}:
  match d:
    case False{}:
      Equal.trans(Nat, Nat.double(S), Nat.add(Nat.double(k), 4n+Nat.double(R)), 1n+Nat.add(Nat.double(k), 3n+Nat.double(R)), e, LNat.pa.add_succ(Nat.double(k), 3n+Nat.double(R)))
    case True{}:
      e

def pa.add2(-a: Nat, -a2: Nat, -b: Nat, -b2: Nat, e1: {a == a2 : Nat}, e2: {b == b2 : Nat}) -> {Nat.add(a, b) == Nat.add(a2, b2) : Nat}:
  %e1 : {Nat.add(a, b) == Nat.add(_, b2) : Nat}
  %e2 : {Nat.add(a, b) == Nat.add(a, _) : Nat}
  {==}

def pa.swap_mid(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, c), b),
    pa.add_assoc(a, b, c),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b),
      Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, c), Nat.add(c, b), LNat.pa.add_comm(b, c)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), pa.add_assoc(a, c, b))))

# 2·2^l·(R + 3/2) + 2·2^l·(i + 2) = (3 + 2R + 2·2^l·(R + 1)) + 1 + 2k
def pa.ineq(+l: Nat, +R: Nat, +vi: Nat, +k: Nat, e: {LLLogic.pa.sh(l, 3n+vi) == Nat.add(k, 2n+R) : Nat})
  -> {Nat.add(Nat.double(LLLogic.pa.sh(l, 3n+Nat.double(R))), Nat.double(LLLogic.pa.sh(l, 2n+vi))) == Nat.add(Nat.add(3n+Nat.double(R), Nat.double(LLLogic.pa.sh(l, 2n+Nat.double(R)))), 1n+Nat.double(k)) : Nat}:
  +A = LLLogic.pa.sh(l, 1n)
  +P = LLLogic.pa.sh(l, 2n+Nat.double(R))
  +S = LLLogic.pa.sh(l, 2n+vi)
  +dA = Nat.double(A)
  +dP = Nat.double(P)
  +dS = Nat.double(S)
  +dk = Nat.double(k)
  +Y = Nat.add(3n+Nat.double(R), dP)
  -L0 = Nat.add(Nat.double(LLLogic.pa.sh(l, 3n+Nat.double(R))), dS)
  -L1 = Nat.add(Nat.double(Nat.add(A, P)), dS)
  -L2 = Nat.add(Nat.add(dA, dP), dS)
  -L3 = Nat.add(Nat.add(dA, dS), dP)
  -L4 = Nat.add(Nat.double(Nat.add(A, S)), dP)
  -L5 = Nat.add(Nat.double(Nat.add(k, 2n+R)), dP)
  -L6 = Nat.add(Nat.add(dk, 4n+Nat.double(R)), dP)
  -L7 = Nat.add(Nat.add(4n+Nat.double(R), dk), dP)
  -L8 = Nat.add(Nat.add(4n+Nat.double(R), dP), dk)
  -L9 = Nat.add(Y, 1n+dk)
  hs = Equal.trans(Nat, Nat.add(A, S), LLLogic.pa.sh(l, 3n+vi), Nat.add(k, 2n+R), Equal.sym(Nat, LLLogic.pa.sh(l, 3n+vi), Nat.add(A, S), pa.sh_add(l, 1n, 2n+vi)), e)
  c1 = Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), dS), LLLogic.pa.sh(l, 3n+Nat.double(R)), Nat.add(A, P), pa.sh_add(l, 1n, 2n+Nat.double(R)))
  c2 = Equal.trans(Nat, L0, L1, L2, c1, Equal.cong(Nat, Nat, z => Nat.add(z, dS), Nat.double(Nat.add(A, P)), Nat.add(dA, dP), pa.double_add(A, P)))
  c3 = Equal.trans(Nat, L0, L2, L3, c2, pa.swap_mid(dA, dP, dS))
  c4 = Equal.trans(Nat, L0, L3, L4, c3, Equal.cong(Nat, Nat, z => Nat.add(z, dP), Nat.add(dA, dS), Nat.double(Nat.add(A, S)), Equal.sym(Nat, Nat.double(Nat.add(A, S)), Nat.add(dA, dS), pa.double_add(A, S))))
  c5 = Equal.trans(Nat, L0, L4, L5, c4, Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), dP), Nat.add(A, S), Nat.add(k, 2n+R), hs))
  c6 = Equal.trans(Nat, L0, L5, L6, c5, Equal.cong(Nat, Nat, z => Nat.add(z, dP), Nat.double(Nat.add(k, 2n+R)), Nat.add(dk, 4n+Nat.double(R)), pa.double_add(k, 2n+R)))
  c7 = Equal.trans(Nat, L0, L6, L7, c6, Equal.cong(Nat, Nat, z => Nat.add(z, dP), Nat.add(dk, 4n+Nat.double(R)), Nat.add(4n+Nat.double(R), dk), LNat.pa.add_comm(dk, 4n+Nat.double(R))))
  c8 = Equal.trans(Nat, L0, L7, L8, c7, pa.swap_mid(4n+Nat.double(R), dk, dP))
  Equal.trans(Nat, L0, L8, L9, c8, Equal.sym(Nat, L9, 1n+Nat.add(Y, dk), LNat.pa.add_succ(Y, dk)))

def pa.old_one.gt(-X: List<&2, Bool>, -Y: List<&2, Bool>, -XX: Nat, +YY: Nat, +k: Nat, ex: {OBits.Bits.val(X) == XX : Nat}, ey: {OBits.Bits.val(Y) == YY : Nat}, ei: {XX == Nat.add(YY, 1n+Nat.double(k)) : Nat})
  -> {Nat.is_gt(OBits.Bits.val(X), OBits.Bits.val(Y)) == True{} : Bool}:
  %Equal.sym(Nat, OBits.Bits.val(X), XX, ex) : {Nat.is_gt(_, OBits.Bits.val(Y)) == True{} : Bool}
  %Equal.sym(Nat, OBits.Bits.val(Y), YY, ey) : {Nat.is_gt(XX, _) == True{} : Bool}
  %Equal.sym(Nat, XX, Nat.add(YY, 1n+Nat.double(k)), ei) : {Nat.is_gt(_, YY) == True{} : Bool}
  pa.gt_add(YY, Nat.double(k))

def pa.nb_odd(+r: Nat) -> {LLLogic.pa.nb(1n+Nat.double(r)) == True{} <> LLLogic.pa.nb(r) : List<&2, Bool>}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, z => OBits.Bits.inc(OBits.Bits.inc(z)), LLLogic.pa.nb(1n+Nat.double(p)), True{} <> LLLogic.pa.nb(p), pa.nb_odd(p))

def pa.nb_even(+p: Nat) -> {LLLogic.pa.nb(2n+Nat.double(p)) == False{} <> LLLogic.pa.nb(1n+p) : List<&2, Bool>}:
  Equal.cong(List<&2, Bool>, List<&2, Bool>, z => OBits.Bits.inc(z), LLLogic.pa.nb(1n+Nat.double(p)), True{} <> LLLogic.pa.nb(p), pa.nb_odd(p))

def pa.good_lift(+d: Bool, c: ONode.Node, +R: Nat, g: LLLogic.pa.Good(c, R)) -> LLLogic.pa.Good(LLLogic.pa.lift(c), LLLogic.pa.Bd(d, R)):
  match c:
    case ONode.Node{+l, +i}:
      (k0, e) = g
      +k = k0
      (LLLogic.pa.bit_k(d, k), pa.good_lift.eq(d, k, R, LLLogic.pa.sh(l, 3n+OBits.Bits.val(i)), Equal.trans(Nat, Nat.double(LLLogic.pa.sh(l, 3n+OBits.Bits.val(i))), Nat.double(Nat.add(k, 2n+R)), Nat.add(Nat.double(k), 4n+Nat.double(R)), Equal.cong(Nat, Nat, z => Nat.double(z), LLLogic.pa.sh(l, 3n+OBits.Bits.val(i)), Nat.add(k, 2n+R), e), pa.double_add(k, 2n+R))))

def pa.goods_lift(+d: Bool, xs: List<&2, ONode.Node>, +R: Nat, g: LLLogic.pa.GoodAll(R, xs)) -> LLLogic.pa.GoodAll(LLLogic.pa.Bd(d, R), LLLogic.pa.lifts(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case c <> t:
      (gc, gt) = g
      (pa.good_lift(d, c, R, gc), pa.goods_lift(d, t, R, gt))
