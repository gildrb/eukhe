# eukhe: lemmas the proofs of area optchat share: a node index read from
# the wire in binary (OBits.Bits.of)
#
# Nat.div and Nat.mod by 2 are the half and the parity by structure
# (ob.hf, ob.pr: Nat.divmod.go counts down two at a time); a number is its
# parity plus twice its half (ob.recompose). Bits.of.go takes the parity,
# then the bits of the half, with fuel to spare (the half of 1 + p is at
# most p), so its bits' value is the number (ob.val_of) and its last bit
# is the 1 of the number's top (ob.canon_of).

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../spec/memory/optchat.bend as S
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/nat.bend as LNat

# the half of n, by structure
def ob.hf(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+ob.hf(q)

# n is odd, by structure
def ob.pr(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match p:
        case 0n:
          True{}
        case 1n+q:
          ob.pr(q)

def ob.b(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def ob.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ob.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def ob.add0(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, ob.add0(p))

# Nat.divmod by 2 is the half and the parity
def ob.dm(n: Nat, +d: Nat) -> {Nat.divmod.go(n, 1n, d, 0n) == (Nat.add(ob.hf(n), d), ob.b(ob.pr(n))) : Nat & Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n++q:
          Equal.trans(Nat & Nat, Nat.divmod.go(q, 1n, 1n+d, 0n), (Nat.add(ob.hf(q), 1n+d), ob.b(ob.pr(q))), (1n+Nat.add(ob.hf(q), d), ob.b(ob.pr(q))), ob.dm(q, 1n+d), Equal.cong(Nat, Nat & Nat, x => (x, ob.b(ob.pr(q))), Nat.add(ob.hf(q), 1n+d), 1n+Nat.add(ob.hf(q), d), ob.add_succ(ob.hf(q), d)))

# m / 2 is its half
def ob.div2(+m: Nat) -> {Nat.div(m, 2n) == ob.hf(m) : Nat}:
  %Equal.sym(Nat & Nat, Nat.divmod.go(m, 1n, 0n, 0n), (Nat.add(ob.hf(m), 0n), ob.b(ob.pr(m))), ob.dm(m, 0n)) : {Pair.fst(Nat, Nat, _) == ob.hf(m) : Nat}
  ob.add0(ob.hf(m))

def ob.is_one(b: Bool) -> {Nat.is_eq(ob.b(b), 1n) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# m mod 2 is 1 exactly when m is odd
def ob.mod2(+m: Nat) -> {Nat.is_eq(Nat.mod(m, 2n), 1n) == ob.pr(m) : Bool}:
  %Equal.sym(Nat & Nat, Nat.divmod.go(m, 1n, 0n, 0n), (Nat.add(ob.hf(m), 0n), ob.b(ob.pr(m))), ob.dm(m, 0n)) : {Nat.is_eq(Pair.snd(Nat, Nat, _), 1n) == ob.pr(m) : Bool}
  ob.is_one(ob.pr(m))

def ob.recompose.two(b: Bool, -x: Nat, -q: Nat, e: {OBits.bit(b, x) == q : Nat}) -> {OBits.bit(b, 2n+x) == 2n+q : Nat}:
  match b:
    case True{}:
      Equal.cong(Nat, Nat, z => 2n+z, 1n+x, q, e)
    case False{}:
      Equal.cong(Nat, Nat, z => 2n+z, x, q, e)

# a number is its parity plus twice its half
def ob.recompose(m: Nat) -> {OBits.bit(ob.pr(m), Nat.double(ob.hf(m))) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n++q:
          ob.recompose.two(ob.pr(q), Nat.double(ob.hf(q)), q, ob.recompose(q))

def ob.le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ob.le_succ(p)

# the half of 1 + p is at most p
def ob.hf_le(p: Nat) -> {Nat.is_le(ob.hf(1n+p), p) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      match q:
        case 0n:
          {==}
        case 1n++r:
          LNat.compactor.pc.le_trans(ob.hf(1n+r), r, 1n+r, ob.hf_le(r), ob.le_succ(r))

# with fuel g >= n, the bits' value is n
def ob.val_go(+g: Nat, +n: Nat, le: {Nat.is_le(n, g) == True{} : Bool}) -> {OBits.Bits.val(OBits.Bits.of.go(g, n)) == n : Nat}:
  match g:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+p:
          LLogicLogic.pf.absurd_ft({0n == 1n+p : Nat}, le)
    case 1n+f:
      match n:
        case 0n:
          {==}
        case 1n+p:
          %Equal.sym(Bool, Nat.is_eq(Nat.mod(1n+p, 2n), 1n), ob.pr(1n+p), ob.mod2(1n+p)) : {OBits.bit(_, Nat.double(OBits.Bits.val(OBits.Bits.of.go(f, Nat.div(1n+p, 2n))))) == 1n+p : Nat}
          %Equal.sym(Nat, Nat.div(1n+p, 2n), ob.hf(1n+p), ob.div2(1n+p)) : {OBits.bit(ob.pr(1n+p), Nat.double(OBits.Bits.val(OBits.Bits.of.go(f, _)))) == 1n+p : Nat}
          %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.of.go(f, ob.hf(1n+p))), ob.hf(1n+p), ob.val_go(f, ob.hf(1n+p), LNat.compactor.pc.le_trans(ob.hf(1n+p), p, f, ob.hf_le(p), le))) : {OBits.bit(ob.pr(1n+p), Nat.double(_)) == 1n+p : Nat}
          ob.recompose(1n+p)

def ob.val_of(+n: Nat) -> {OBits.Bits.val(OBits.Bits.of(n)) == n : Nat}:
  ob.val_go(n, n, LNat.compactor.pc.le_refl(n))

def ob.isz(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

# 1 + x is not 0: a False == True from it
def ob.succ_zero(-x: Nat, e: {1n+x == 0n : Nat}) -> {False{} == True{} : Bool}:
  %e : {Bool.not(ob.isz(_)) == True{} : Bool}
  {==}

# a number with half 0 and at least 1 is odd (it is 1)
def ob.one_odd(p: Nat, e: {ob.hf(1n+p) == 0n : Nat}) -> {ob.pr(1n+p) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      LLogicLogic.pf.absurd_ft({ob.pr(2n+q) == True{} : Bool}, ob.succ_zero(ob.hf(q), e))

def ob.NilT(xs: List<&2, Bool>, A: Type) -> Type:
  match xs:
    case Nil{}:
      A
    case h <> t:
      Unit

def ob.nonil(-A: Type, -x: Bool, -r: List<&2, Bool>, e: {x <> r == Nil{} : List<&2, Bool>}) -> A:
  %e : ob.NilT(_, A)
  Unit{}

# no bits within the fuel: the number is 0
def ob.nil_zero(f: Nat, d: Nat, le: {Nat.is_le(d, f) == True{} : Bool}, e: {OBits.Bits.of.go(f, d) == Nil{} : List<&2, Bool>}) -> {d == 0n : Nat}:
  match f:
    case 0n:
      match d:
        case 0n:
          {==}
        case 1n+q:
          LLogicLogic.pf.absurd_ft({1n+q == 0n : Nat}, le)
    case 1n+g:
      match d:
        case 0n:
          {==}
        case 1n++q:
          ob.nonil({1n+q == 0n : Nat}, Nat.is_eq(Nat.mod(1n+q, 2n), 1n), OBits.Bits.of.go(g, Nat.div(1n+q, 2n)), e)

# the last bit of b, then r: r's last bit, or b when r is empty
def ob.canon_step(r: List<&2, Bool>, +b: Bool, ih: {S.Bits.canon(r) == True{} : Bool}, nil: {r == Nil{} : List<&2, Bool>} -> {b == True{} : Bool}) -> {S.Bits.canon.go(r, b) == True{} : Bool}:
  match r:
    case Nil{}:
      nil({==})
    case x <> t:
      ih

# with fuel g >= n, the bits of n have no high zero bit
def ob.canon_go(+g: Nat, +n: Nat, +le: {Nat.is_le(n, g) == True{} : Bool}) -> {S.Bits.canon(OBits.Bits.of.go(g, n)) == True{} : Bool}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      match n:
        case 0n:
          {==}
        case 1n+p:
          +lh = LNat.compactor.pc.le_trans(ob.hf(1n+p), p, f, ob.hf_le(p), le)
          %Equal.sym(Bool, Nat.is_eq(Nat.mod(1n+p, 2n), 1n), ob.pr(1n+p), ob.mod2(1n+p)) : {S.Bits.canon(_ <> OBits.Bits.of.go(f, Nat.div(1n+p, 2n))) == True{} : Bool}
          %Equal.sym(Nat, Nat.div(1n+p, 2n), ob.hf(1n+p), ob.div2(1n+p)) : {S.Bits.canon(ob.pr(1n+p) <> OBits.Bits.of.go(f, _)) == True{} : Bool}
          ob.canon_step(OBits.Bits.of.go(f, ob.hf(1n+p)), ob.pr(1n+p), ob.canon_go(f, ob.hf(1n+p), lh), nil => ob.one_odd(p, ob.nil_zero(f, ob.hf(1n+p), lh, nil)))

def ob.canon_of(+n: Nat) -> {S.Bits.canon(OBits.Bits.of(n)) == True{} : Bool}:
  ob.canon_go(n, n, LNat.compactor.pc.le_refl(n))
