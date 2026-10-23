# eukhe: lemmas of the proof of LAW push_agrees_always: nat

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/fit.bend as OFit
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/node.bend as ONode
import ../../base/nat/add.bend as LNatAdd
import ../../base/nat/misc.bend as LNatMisc

def pa.add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      LNatMisc.pa.succ(Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), pa.add_assoc(p, b, c))

def pa.double_add(a: Nat, +b: Nat) -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      LNatMisc.pa.succ(1n+Nat.double(Nat.add(p, b)), 1n+Nat.add(Nat.double(p), Nat.double(b)), LNatMisc.pa.succ(Nat.double(Nat.add(p, b)), Nat.add(Nat.double(p), Nat.double(b)), pa.double_add(p, b)))

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

# x·2^l, doubling outside
def pa.sh(l: Nat, x: Nat) -> Nat:
  match l:
    case 0n:
      x
    case 1n+p:
      Nat.double(pa.sh(p, x))

def pa.sh_zero(l: Nat) -> {pa.sh(l, 0n) == 0n : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, pa.sh(p, 0n), 0n, pa.sh_zero(p)) : {Nat.double(_) == 0n : Nat}
      {==}

def pa.sh_add(+l: Nat, +a: Nat, +b: Nat) -> {pa.sh(l, Nat.add(a, b)) == Nat.add(pa.sh(l, a), pa.sh(l, b)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.double(pa.sh(p, Nat.add(a, b))), Nat.double(Nat.add(pa.sh(p, a), pa.sh(p, b))), Nat.add(Nat.double(pa.sh(p, a)), Nat.double(pa.sh(p, b))), Equal.cong(Nat, Nat, x => Nat.double(x), pa.sh(p, Nat.add(a, b)), Nat.add(pa.sh(p, a), pa.sh(p, b)), pa.sh_add(p, a, b)), pa.double_add(pa.sh(p, a), pa.sh(p, b)))

def pa.sh_double(+l: Nat, +x: Nat) -> {pa.sh(l, Nat.double(x)) == Nat.double(pa.sh(l, x)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, y => Nat.double(y), pa.sh(p, Nat.double(x)), Nat.double(pa.sh(p, x)), pa.sh_double(p, x))

def pa.add_bits(x: Bool, y: Bool, +P: Nat, +Q: Nat) -> {Nat.add(OBits.bit(x, P), OBits.bit(y, Q)) == OBits.bit(x, OBits.bit(y, Nat.add(P, Q))) : Nat}:
  match x y:
    case False{} False{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      LNatAdd.pa.add_succ(P, Q)
    case True{} True{}:
      LNatMisc.pa.succ(Nat.add(P, 1n+Q), 1n+Nat.add(P, Q), LNatAdd.pa.add_succ(P, Q))

# The counter
# -----------
# ds: push's keep bits, lowest (newest entry) first; T = B(ds) messages.

def pa.B(ds: List<&2, Bool>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case d <> r:
      match d:
        case False{}:
          1n+Nat.double(pa.B(r))
        case True{}:
          2n+Nat.double(pa.B(r))

def pa.hd(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      h

# Sizes
# -----
# Under push every line counts 1 and every node is built (All{1}).

def pa.vs(v: List<&2, ONode.Node>) -> Nat:
  OFit.view_size(0n, OInfo.All{1n}, v)

# B(d <> r) from B(r), and the slack one level up
def pa.Bd(d: Bool, +R: Nat) -> Nat:
  match d:
    case False{}:
      1n+Nat.double(R)
    case True{}:
      2n+Nat.double(R)

def pa.bit_k(d: Bool, +k: Nat) -> Nat:
  match d:
    case False{}:
      1n+Nat.double(k)
    case True{}:
      Nat.double(k)

def pa.good_lift.eq(d: Bool, +k: Nat, +R: Nat, -S: Nat, e: {Nat.double(S) == Nat.add(Nat.double(k), 4n+Nat.double(R)) : Nat})
  -> {Nat.double(S) == Nat.add(pa.bit_k(d, k), 2n+pa.Bd(d, R)) : Nat}:
  match d:
    case False{}:
      Equal.trans(Nat, Nat.double(S), Nat.add(Nat.double(k), 4n+Nat.double(R)), 1n+Nat.add(Nat.double(k), 3n+Nat.double(R)), e, LNatAdd.pa.add_succ(Nat.double(k), 3n+Nat.double(R)))
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
      Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, c), Nat.add(c, b), LNatAdd.pa.add_comm(b, c)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), pa.add_assoc(a, c, b))))

# 2·2^l·(R + 3/2) + 2·2^l·(i + 2) = (3 + 2R + 2·2^l·(R + 1)) + 1 + 2k
def pa.ineq(+l: Nat, +R: Nat, +vi: Nat, +k: Nat, e: {pa.sh(l, 3n+vi) == Nat.add(k, 2n+R) : Nat})
  -> {Nat.add(Nat.double(pa.sh(l, 3n+Nat.double(R))), Nat.double(pa.sh(l, 2n+vi))) == Nat.add(Nat.add(3n+Nat.double(R), Nat.double(pa.sh(l, 2n+Nat.double(R)))), 1n+Nat.double(k)) : Nat}:
  +A = pa.sh(l, 1n)
  +P = pa.sh(l, 2n+Nat.double(R))
  +S = pa.sh(l, 2n+vi)
  +dA = Nat.double(A)
  +dP = Nat.double(P)
  +dS = Nat.double(S)
  +dk = Nat.double(k)
  +Y = Nat.add(3n+Nat.double(R), dP)
  -L0 = Nat.add(Nat.double(pa.sh(l, 3n+Nat.double(R))), dS)
  -L1 = Nat.add(Nat.double(Nat.add(A, P)), dS)
  -L2 = Nat.add(Nat.add(dA, dP), dS)
  -L3 = Nat.add(Nat.add(dA, dS), dP)
  -L4 = Nat.add(Nat.double(Nat.add(A, S)), dP)
  -L5 = Nat.add(Nat.double(Nat.add(k, 2n+R)), dP)
  -L6 = Nat.add(Nat.add(dk, 4n+Nat.double(R)), dP)
  -L7 = Nat.add(Nat.add(4n+Nat.double(R), dk), dP)
  -L8 = Nat.add(Nat.add(4n+Nat.double(R), dP), dk)
  -L9 = Nat.add(Y, 1n+dk)
  hs = Equal.trans(Nat, Nat.add(A, S), pa.sh(l, 3n+vi), Nat.add(k, 2n+R), Equal.sym(Nat, pa.sh(l, 3n+vi), Nat.add(A, S), pa.sh_add(l, 1n, 2n+vi)), e)
  c1 = Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), dS), pa.sh(l, 3n+Nat.double(R)), Nat.add(A, P), pa.sh_add(l, 1n, 2n+Nat.double(R)))
  c2 = Equal.trans(Nat, L0, L1, L2, c1, Equal.cong(Nat, Nat, z => Nat.add(z, dS), Nat.double(Nat.add(A, P)), Nat.add(dA, dP), pa.double_add(A, P)))
  c3 = Equal.trans(Nat, L0, L2, L3, c2, pa.swap_mid(dA, dP, dS))
  c4 = Equal.trans(Nat, L0, L3, L4, c3, Equal.cong(Nat, Nat, z => Nat.add(z, dP), Nat.add(dA, dS), Nat.double(Nat.add(A, S)), Equal.sym(Nat, Nat.double(Nat.add(A, S)), Nat.add(dA, dS), pa.double_add(A, S))))
  c5 = Equal.trans(Nat, L0, L4, L5, c4, Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), dP), Nat.add(A, S), Nat.add(k, 2n+R), hs))
  c6 = Equal.trans(Nat, L0, L5, L6, c5, Equal.cong(Nat, Nat, z => Nat.add(z, dP), Nat.double(Nat.add(k, 2n+R)), Nat.add(dk, 4n+Nat.double(R)), pa.double_add(k, 2n+R)))
  c7 = Equal.trans(Nat, L0, L6, L7, c6, Equal.cong(Nat, Nat, z => Nat.add(z, dP), Nat.add(dk, 4n+Nat.double(R)), Nat.add(4n+Nat.double(R), dk), LNatAdd.pa.add_comm(dk, 4n+Nat.double(R))))
  c8 = Equal.trans(Nat, L0, L7, L8, c7, pa.swap_mid(4n+Nat.double(R), dk, dP))
  Equal.trans(Nat, L0, L8, L9, c8, Equal.sym(Nat, L9, 1n+Nat.add(Y, dk), LNatAdd.pa.add_succ(Y, dk)))

def pa.old_one.gt(-X: List<&2, Bool>, -Y: List<&2, Bool>, -XX: Nat, +YY: Nat, +k: Nat, ex: {OBits.Bits.val(X) == XX : Nat}, ey: {OBits.Bits.val(Y) == YY : Nat}, ei: {XX == Nat.add(YY, 1n+Nat.double(k)) : Nat})
  -> {Nat.is_gt(OBits.Bits.val(X), OBits.Bits.val(Y)) == True{} : Bool}:
  %Equal.sym(Nat, OBits.Bits.val(X), XX, ex) : {Nat.is_gt(_, OBits.Bits.val(Y)) == True{} : Bool}
  %Equal.sym(Nat, OBits.Bits.val(Y), YY, ey) : {Nat.is_gt(XX, _) == True{} : Bool}
  %Equal.sym(Nat, XX, Nat.add(YY, 1n+Nat.double(k)), ei) : {Nat.is_gt(_, YY) == True{} : Bool}
  pa.gt_add(YY, Nat.double(k))
