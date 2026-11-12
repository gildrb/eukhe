# eukhe: lemmas the proofs of area optchat share: the spec's due order
# (S.more_due, S.cross) is a strict order
#
# S.cross(U, la, lb, xa, xb) compares (U - xa)/2^la with (U - xb)/2^lb by
# U·2^lb + xb·2^la > U·2^la + xa·2^lb. Scaling by a power of 2 and adding
# a term on both sides keep a comparison (du.cmp_sh, du.cmp_add_r), so
# the comparison is irreflexive (du.md_self), asymmetric (du.md_asym) and
# transitive through a non-strict step (du.md_tr: a > c >= x gives
# a > x); a pair named by the same level and index value is as due as
# the other (du.md_same).

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/fit.bend as OFit
import ../../../spec/memory/optchat.bend as S
import ../../base/nat.bend as LNat
import ./step.bend as LA

# Shifts
# ------

def du.dbl_add(a: Nat, +b: Nat) -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, x => 2n+x, Nat.double(Nat.add(p, b)), Nat.add(Nat.double(p), Nat.double(b)), du.dbl_add(p, b))

def du.sh_add(l: Nat, +x: Nat, +y: Nat) -> {S.sh(l, Nat.add(x, y)) == Nat.add(S.sh(l, x), S.sh(l, y)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat, Nat.double(S.sh(p, Nat.add(x, y))), Nat.double(Nat.add(S.sh(p, x), S.sh(p, y))), Nat.add(Nat.double(S.sh(p, x)), Nat.double(S.sh(p, y))),
        Equal.cong(Nat, Nat, z => Nat.double(z), S.sh(p, Nat.add(x, y)), Nat.add(S.sh(p, x), S.sh(p, y)), du.sh_add(p, x, y)),
        du.dbl_add(S.sh(p, x), S.sh(p, y)))

def du.sh_dbl(b: Nat, +x: Nat) -> {S.sh(b, Nat.double(x)) == Nat.double(S.sh(b, x)) : Nat}:
  match b:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, z => Nat.double(z), S.sh(p, Nat.double(x)), Nat.double(S.sh(p, x)), du.sh_dbl(p, x))

# x·2^b·2^a = x·2^a·2^b
def du.comm(a: Nat, +b: Nat, +x: Nat) -> {S.sh(a, S.sh(b, x)) == S.sh(b, S.sh(a, x)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat, Nat.double(S.sh(p, S.sh(b, x))), Nat.double(S.sh(b, S.sh(p, x))), S.sh(b, Nat.double(S.sh(p, x))),
        Equal.cong(Nat, Nat, z => Nat.double(z), S.sh(p, S.sh(b, x)), S.sh(b, S.sh(p, x)), du.comm(p, b, x)),
        Equal.sym(Nat, S.sh(b, Nat.double(S.sh(p, x))), Nat.double(S.sh(b, S.sh(p, x))), du.sh_dbl(b, S.sh(p, x))))

# Comparisons
# -----------

def du.cmp_dbl(x: Nat, y: Nat) -> {Nat.cmp(Nat.double(x), Nat.double(y)) == Nat.cmp(x, y) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      du.cmp_dbl(p, q)

def du.cmp_sh(l: Nat, +x: Nat, +y: Nat) -> {Nat.cmp(S.sh(l, x), S.sh(l, y)) == Nat.cmp(x, y) : Cmp}:
  match l:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Cmp, Nat.cmp(Nat.double(S.sh(p, x)), Nat.double(S.sh(p, y))), Nat.cmp(S.sh(p, x), S.sh(p, y)), Nat.cmp(x, y), du.cmp_dbl(S.sh(p, x), S.sh(p, y)), du.cmp_sh(p, x, y))

def du.cmp_add(z: Nat, -x: Nat, -y: Nat) -> {Nat.cmp(Nat.add(z, x), Nat.add(z, y)) == Nat.cmp(x, y) : Cmp}:
  match z:
    case 0n:
      {==}
    case 1n+p:
      du.cmp_add(p, x, y)

def du.cmp_add_r(+x: Nat, +y: Nat, +z: Nat) -> {Nat.cmp(Nat.add(x, z), Nat.add(y, z)) == Nat.cmp(x, y) : Cmp}:
  %LNat.add_comm(z, x) : {Nat.cmp(_, Nat.add(y, z)) == Nat.cmp(x, y) : Cmp}
  %LNat.add_comm(z, y) : {Nat.cmp(Nat.add(z, x), _) == Nat.cmp(x, y) : Cmp}
  du.cmp_add(z, x, y)

def du.gt_self(n: Nat) -> {Nat.is_gt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      du.gt_self(p)

def du.asym(a: Nat, b: Nat, e: {Nat.is_gt(a, b) == True{} : Bool}) -> {Nat.is_gt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.cover.absurd({Nat.is_gt(1n+q, 0n) == False{} : Bool}, e)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      du.asym(p, q, e)

def du.cgl(c: Cmp, e: {Cmp.is_gt(c) == False{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      LA.cover.absurd({False{} == True{} : Bool}, Equal.sym(Bool, True{}, False{}, e))

# x >= y > z gives x > z
def du.le_gt(x: Nat, y: Nat, z: Nat, a: {Nat.is_le(y, x) == True{} : Bool}, b: {Nat.is_gt(y, z) == True{} : Bool}) -> {Nat.is_gt(x, z) == True{} : Bool}:
  match x y z:
    case _ 0n 0n:
      LA.cover.absurd({Nat.is_gt(x, 0n) == True{} : Bool}, b)
    case _ 0n 1n+r:
      LA.cover.absurd({Nat.is_gt(x, 1n+r) == True{} : Bool}, b)
    case 0n 1n+q _:
      LA.cover.absurd({Nat.is_gt(0n, z) == True{} : Bool}, a)
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      du.le_gt(p, q, r, a, b)

# a > b and c <= d give a + d > b + c
def du.gt_add_le(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h: {Nat.is_gt(a, b) == True{} : Bool}, k: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_gt(Nat.add(a, d), Nat.add(b, c)) == True{} : Bool}:
  +le = Equal.trans(Bool, Nat.is_le(Nat.add(a, c), Nat.add(a, d)), Nat.is_le(c, d), True{}, Equal.cong(Cmp, Bool, q => Cmp.is_le(q), Nat.cmp(Nat.add(a, c), Nat.add(a, d)), Nat.cmp(c, d), du.cmp_add(a, c, d)), k)
  +gt = Equal.trans(Bool, Nat.is_gt(Nat.add(a, c), Nat.add(b, c)), Nat.is_gt(a, b), True{}, Equal.cong(Cmp, Bool, q => Cmp.is_gt(q), Nat.cmp(Nat.add(a, c), Nat.add(b, c)), Nat.cmp(a, b), du.cmp_add_r(a, b, c)), h)
  du.le_gt(Nat.add(a, d), Nat.add(a, c), Nat.add(b, c), le, gt)

# (a + b) + (c + d) = (a + d) + (b + c)
def du.sh1(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, d), Nat.add(b, c)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), LNat.add_assoc(a, b, Nat.add(c, d))) : {_ == Nat.add(Nat.add(a, d), Nat.add(b, c)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, d), Nat.add(b, c)), Nat.add(a, Nat.add(d, Nat.add(b, c))), LNat.add_assoc(a, d, Nat.add(b, c))) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %LNat.add_assoc(b, c, d) : {Nat.add(a, _) == Nat.add(a, Nat.add(d, Nat.add(b, c))) : Nat}
  %LNat.add_comm(d, Nat.add(b, c)) : {Nat.add(a, _) == Nat.add(a, Nat.add(d, Nat.add(b, c))) : Nat}
  {==}

# (a + b) + (c + d) = (c + b) + (d + a)
def du.sh2(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(c, b), Nat.add(d, a)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(Nat.add(c, d), Nat.add(a, b)), Nat.add(Nat.add(c, b), Nat.add(d, a)), LNat.add_comm(Nat.add(a, b), Nat.add(c, d)), du.sh1(c, d, a, b))

# p + q > r + wa and m + q <= r + wx give p + wx > m + wa
def du.core(+p: Nat, +q: Nat, +r: Nat, +wa: Nat, +m: Nat, +wx: Nat, h1: {Nat.is_gt(Nat.add(p, q), Nat.add(r, wa)) == True{} : Bool}, h2: {Nat.is_le(Nat.add(m, q), Nat.add(r, wx)) == True{} : Bool}) -> {Nat.is_gt(Nat.add(p, wx), Nat.add(m, wa)) == True{} : Bool}:
  +z = Nat.add(q, r)
  %du.cmp_add_r(Nat.add(p, wx), Nat.add(m, wa), z) : {Cmp.is_gt(_) == True{} : Bool}
  %du.sh1(p, q, r, wx) : {Cmp.is_gt(Nat.cmp(_, Nat.add(Nat.add(m, wa), z))) == True{} : Bool}
  %du.sh2(r, wa, m, q) : {Cmp.is_gt(Nat.cmp(Nat.add(Nat.add(p, q), Nat.add(r, wx)), _)) == True{} : Bool}
  du.gt_add_le(Nat.add(p, q), Nat.add(r, wa), Nat.add(m, q), Nat.add(r, wx), h1, h2)

# The due order
# -------------

def du.h1(+u: Nat, +la: Nat, +lc: Nat, +lx: Nat, +xa: Nat, +xc: Nat, h: {S.cross(u, la, lc, xa, xc) == True{} : Bool})
  -> {Nat.is_gt(Nat.add(S.sh(lx, S.sh(lc, u)), S.sh(lx, S.sh(la, xc))), Nat.add(S.sh(lx, S.sh(la, u)), S.sh(lx, S.sh(lc, xa)))) == True{} : Bool}:
  +a = Nat.add(S.sh(lc, u), S.sh(la, xc))
  +b = Nat.add(S.sh(la, u), S.sh(lc, xa))
  %du.sh_add(lx, S.sh(lc, u), S.sh(la, xc)) : {Nat.is_gt(_, Nat.add(S.sh(lx, S.sh(la, u)), S.sh(lx, S.sh(lc, xa)))) == True{} : Bool}
  %du.sh_add(lx, S.sh(la, u), S.sh(lc, xa)) : {Nat.is_gt(S.sh(lx, a), _) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(S.sh(lx, a), S.sh(lx, b)), Nat.cmp(a, b), du.cmp_sh(lx, a, b)) : {Cmp.is_gt(_) == True{} : Bool}
  h

def du.h2(+u: Nat, +la: Nat, +lc: Nat, +lx: Nat, +xx: Nat, +xc: Nat, h: {S.cross(u, lx, lc, xx, xc) == False{} : Bool})
  -> {Nat.is_le(Nat.add(S.sh(la, S.sh(lc, u)), S.sh(lx, S.sh(la, xc))), Nat.add(S.sh(lx, S.sh(la, u)), S.sh(la, S.sh(lc, xx)))) == True{} : Bool}:
  +a = Nat.add(S.sh(lc, u), S.sh(lx, xc))
  +b = Nat.add(S.sh(lx, u), S.sh(lc, xx))
  %du.comm(la, lx, xc) : {Nat.is_le(Nat.add(S.sh(la, S.sh(lc, u)), _), Nat.add(S.sh(lx, S.sh(la, u)), S.sh(la, S.sh(lc, xx)))) == True{} : Bool}
  %du.comm(la, lx, u) : {Nat.is_le(Nat.add(S.sh(la, S.sh(lc, u)), S.sh(la, S.sh(lx, xc))), Nat.add(_, S.sh(la, S.sh(lc, xx)))) == True{} : Bool}
  %du.sh_add(la, S.sh(lc, u), S.sh(lx, xc)) : {Nat.is_le(_, Nat.add(S.sh(la, S.sh(lx, u)), S.sh(la, S.sh(lc, xx)))) == True{} : Bool}
  %du.sh_add(la, S.sh(lx, u), S.sh(lc, xx)) : {Nat.is_le(S.sh(la, a), _) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(S.sh(la, a), S.sh(la, b)), Nat.cmp(a, b), du.cmp_sh(la, a, b)) : {Cmp.is_le(_) == True{} : Bool}
  du.cgl(Nat.cmp(a, b), h)

# a > c and not x > c give a > x
def du.cross_tr(+u: Nat, +la: Nat, +lc: Nat, +lx: Nat, +xa: Nat, +xc: Nat, +xx: Nat, h1: {S.cross(u, la, lc, xa, xc) == True{} : Bool}, h2: {S.cross(u, lx, lc, xx, xc) == False{} : Bool}) -> {S.cross(u, la, lx, xa, xx) == True{} : Bool}:
  +g1 = Nat.add(S.sh(lx, u), S.sh(la, xx))
  +g2 = Nat.add(S.sh(la, u), S.sh(lx, xa))
  %du.cmp_sh(lc, g1, g2) : {Cmp.is_gt(_) == True{} : Bool}
  %Equal.sym(Nat, S.sh(lc, g1), Nat.add(S.sh(lc, S.sh(lx, u)), S.sh(lc, S.sh(la, xx))), du.sh_add(lc, S.sh(lx, u), S.sh(la, xx))) : {Cmp.is_gt(Nat.cmp(_, S.sh(lc, g2))) == True{} : Bool}
  %Equal.sym(Nat, S.sh(lc, g2), Nat.add(S.sh(lc, S.sh(la, u)), S.sh(lc, S.sh(lx, xa))), du.sh_add(lc, S.sh(la, u), S.sh(lx, xa))) : {Cmp.is_gt(Nat.cmp(Nat.add(S.sh(lc, S.sh(lx, u)), S.sh(lc, S.sh(la, xx))), _)) == True{} : Bool}
  %du.comm(lx, lc, u) : {Cmp.is_gt(Nat.cmp(Nat.add(_, S.sh(lc, S.sh(la, xx))), Nat.add(S.sh(lc, S.sh(la, u)), S.sh(lc, S.sh(lx, xa))))) == True{} : Bool}
  %du.comm(la, lc, xx) : {Cmp.is_gt(Nat.cmp(Nat.add(S.sh(lx, S.sh(lc, u)), _), Nat.add(S.sh(lc, S.sh(la, u)), S.sh(lc, S.sh(lx, xa))))) == True{} : Bool}
  %du.comm(la, lc, u) : {Cmp.is_gt(Nat.cmp(Nat.add(S.sh(lx, S.sh(lc, u)), S.sh(la, S.sh(lc, xx))), Nat.add(_, S.sh(lc, S.sh(lx, xa))))) == True{} : Bool}
  %du.comm(lx, lc, xa) : {Cmp.is_gt(Nat.cmp(Nat.add(S.sh(lx, S.sh(lc, u)), S.sh(la, S.sh(lc, xx))), Nat.add(S.sh(la, S.sh(lc, u)), _))) == True{} : Bool}
  du.core(S.sh(lx, S.sh(lc, u)), S.sh(lx, S.sh(la, xc)), S.sh(lx, S.sh(la, u)), S.sh(lx, S.sh(lc, xa)), S.sh(la, S.sh(lc, u)), S.sh(la, S.sh(lc, xx)), du.h1(u, la, lc, lx, xa, xc, h1), du.h2(u, la, lc, lx, xx, xc, h2))

# the pair from a is more due than the one from c, the one from x is not:
# so the pair from a is more due than the one from x
def du.md_tr(m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, +c: ONode.Node, +x: ONode.Node, h1: {S.more_due(m, t, a, c) == True{} : Bool}, h2: {S.more_due(m, t, x, c) == False{} : Bool}) -> {S.more_due(m, t, a, x) == True{} : Bool}:
  match m:
    case OFit.Last{}:
      du.cross_tr(1n+OBits.Bits.val(t), S.lvl(a), S.lvl(c), S.lvl(x), S.sh(S.lvl(a), 2n+S.idx(a)), S.sh(S.lvl(c), 2n+S.idx(c)), S.sh(S.lvl(x), 2n+S.idx(x)), h1, h2)
    case OFit.First{}:
      du.cross_tr(OBits.Bits.val(t), S.lvl(a), S.lvl(c), S.lvl(x), S.sh(S.lvl(a), S.idx(a)), S.sh(S.lvl(c), S.idx(c)), S.sh(S.lvl(x), S.idx(x)), h1, h2)

def du.md_asym(m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, +b: ONode.Node, h: {S.more_due(m, t, a, b) == True{} : Bool}) -> {S.more_due(m, t, b, a) == False{} : Bool}:
  match m:
    case OFit.Last{}:
      +u = Nat.add(1n, OBits.Bits.val(t))
      +xa = S.sh(S.lvl(a), 2n+S.idx(a))
      +xb = S.sh(S.lvl(b), 2n+S.idx(b))
      du.asym(Nat.add(S.sh(S.lvl(b), u), S.sh(S.lvl(a), xb)), Nat.add(S.sh(S.lvl(a), u), S.sh(S.lvl(b), xa)), h)
    case OFit.First{}:
      +u = OBits.Bits.val(t)
      +xa = S.sh(S.lvl(a), S.idx(a))
      +xb = S.sh(S.lvl(b), S.idx(b))
      du.asym(Nat.add(S.sh(S.lvl(b), u), S.sh(S.lvl(a), xb)), Nat.add(S.sh(S.lvl(a), u), S.sh(S.lvl(b), xa)), h)

# a > x > c gives a > c
def du.md_tr2(+m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, +x: ONode.Node, +c: ONode.Node, h1: {S.more_due(m, t, a, x) == True{} : Bool}, h2: {S.more_due(m, t, x, c) == True{} : Bool}) -> {S.more_due(m, t, a, c) == True{} : Bool}:
  du.md_tr(m, t, a, x, c, h1, du.md_asym(m, t, x, c, h2))

def du.md_self(m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node) -> {S.more_due(m, t, a, a) == False{} : Bool}:
  match m:
    case OFit.Last{}:
      +u = Nat.add(1n, OBits.Bits.val(t))
      du.gt_self(Nat.add(S.sh(S.lvl(a), u), S.sh(S.lvl(a), S.sh(S.lvl(a), 2n+S.idx(a)))))
    case OFit.First{}:
      +u = OBits.Bits.val(t)
      du.gt_self(Nat.add(S.sh(S.lvl(a), u), S.sh(S.lvl(a), S.sh(S.lvl(a), S.idx(a)))))

def du.md_same.v(m: OFit.Age, +t: List<&2, Bool>, +la: Nat, +ia: List<&2, Bool>, +ix: List<&2, Bool>, hv: {OBits.Bits.val(ix) == OBits.Bits.val(ia) : Nat}) -> {S.more_due(m, t, ONode.Node{la, ia}, ONode.Node{la, ix}) == False{} : Bool}:
  match m:
    case OFit.Last{}:
      %Equal.sym(Nat, OBits.Bits.val(ix), OBits.Bits.val(ia), hv) : {S.cross(1n+OBits.Bits.val(t), la, la, S.sh(la, 2n+OBits.Bits.val(ia)), S.sh(la, 2n+_)) == False{} : Bool}
      du.md_self(OFit.Last{}, t, ONode.Node{la, ia})
    case OFit.First{}:
      %Equal.sym(Nat, OBits.Bits.val(ix), OBits.Bits.val(ia), hv) : {S.cross(OBits.Bits.val(t), la, la, S.sh(la, OBits.Bits.val(ia)), S.sh(la, _)) == False{} : Bool}
      du.md_self(OFit.First{}, t, ONode.Node{la, ia})

# a pair named by the same level and index value is not more due than a's
def du.md_same(+m: OFit.Age, +t: List<&2, Bool>, a: ONode.Node, x: ONode.Node, +e: {S.same(x, a) == True{} : Bool}) -> {S.more_due(m, t, a, x) == False{} : Bool}:
  match a x:
    case ONode.Node{+la, +ia} ONode.Node{+lx, +ix}:
      +hl = LA.cover.eq_of_is_eq(lx, la, LA.cover.and_l(Nat.is_eq(lx, la), Nat.is_eq(OBits.Bits.val(ix), OBits.Bits.val(ia)), e))
      +hv = LA.cover.eq_of_is_eq(OBits.Bits.val(ix), OBits.Bits.val(ia), LA.cover.and_r(Nat.is_eq(lx, la), Nat.is_eq(OBits.Bits.val(ix), OBits.Bits.val(ia)), e))
      %Equal.sym(Nat, lx, la, hl) : {S.more_due(m, t, ONode.Node{la, ia}, ONode.Node{_, ix}) == False{} : Bool}
      du.md_same.v(m, t, la, ia, ix, hv)

