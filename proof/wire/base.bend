# eukhe: lemmas the proofs of area wire share

import Base
import ../../bend/wire.bend as Wr
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ../base/list.bend as LList
import ../base/nat/add.bend as LNatAdd
import ../base/nat/is_le.bend as LNatIsLe
import ../base/nat/misc.bend as LNatMisc
import ../base/pair.bend as LPair

# ---- Nat: zero, mul, order ----

def wn_isz(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

# 1 + n is not 0
def wn_succ_nz(-G: Type, -n: Nat, e: {1n+n == 0n : Nat}) -> G:
  LBoolMisc.wn_absurd(G, Equal.cong(Nat, Bool, wn_isz, 1n+n, 0n, e))

def wn_add_eq_zero_l(a: Nat, -b: Nat, e: {Nat.add(a, b) == 0n : Nat}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      wn_succ_nz({1n+p == 0n : Nat}, Nat.add(p, b), e)

def wn_add_eq_zero_r(a: Nat, -b: Nat, e: {Nat.add(a, b) == 0n : Nat}) -> {b == 0n : Nat}:
  match a:
    case 0n:
      e
    case 1n+p:
      wn_succ_nz({b == 0n : Nat}, Nat.add(p, b), e)

def wn_ud0(+d: Nat, h: {LBoolMisc.wn_lt10(d) == True{} : Bool}) -> {Nat.div(Nat.add(d, Nat.mul(10n, 0n)), 10n) == 0n : Nat}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+p:
      LBoolMisc.wn_absurd({Nat.div(Nat.add(10n+p, Nat.mul(10n, 0n)), 10n) == 0n : Nat}, h)

def wn_um0(+d: Nat, h: {LBoolMisc.wn_lt10(d) == True{} : Bool}) -> {Nat.mod(Nat.add(d, Nat.mul(10n, 0n)), 10n) == d : Nat}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+p:
      LBoolMisc.wn_absurd({Nat.mod(Nat.add(10n+p, Nat.mul(10n, 0n)), 10n) == 10n+p : Nat}, h)

# a digit d below 10 then v: (d + 10 * v) / 10 == v
def wn_ud(+v: Nat, +d: Nat, h: {LBoolMisc.wn_lt10(d) == True{} : Bool}) -> {Nat.div(Nat.add(d, Nat.mul(10n, v)), 10n) == v : Nat}:
  match v:
    case 0n:
      wn_ud0(d, h)
    case 1n+w:
      %Equal.sym(Nat, Nat.mul(10n, 1n+w), Nat.add(10n, Nat.mul(10n, w)), LNatAdd.wn_mul_succ_r(10n, w)) : {Nat.div(Nat.add(d, _), 10n) == 1n+w : Nat}
      %Equal.sym(Nat, Nat.add(d, Nat.add(10n, Nat.mul(10n, w))), Nat.add(10n, Nat.add(d, Nat.mul(10n, w))), LNatAdd.wn_add_swap(d, 10n, Nat.mul(10n, w))) : {Nat.div(_, 10n) == 1n+w : Nat}
      %Equal.sym(Nat, Nat.div(10n+Nat.add(d, Nat.mul(10n, w)), 10n), 1n+Nat.div(Nat.add(d, Nat.mul(10n, w)), 10n), LPair.wn_div_step(Nat.add(d, Nat.mul(10n, w)))) : {_ == 1n+w : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, Nat.div(Nat.add(d, Nat.mul(10n, w)), 10n), w, wn_ud(w, d, h))

# a digit d below 10 then v: (d + 10 * v) % 10 == d
def wn_um(+v: Nat, +d: Nat, h: {LBoolMisc.wn_lt10(d) == True{} : Bool}) -> {Nat.mod(Nat.add(d, Nat.mul(10n, v)), 10n) == d : Nat}:
  match v:
    case 0n:
      wn_um0(d, h)
    case 1n+w:
      %Equal.sym(Nat, Nat.mul(10n, 1n+w), Nat.add(10n, Nat.mul(10n, w)), LNatAdd.wn_mul_succ_r(10n, w)) : {Nat.mod(Nat.add(d, _), 10n) == d : Nat}
      %Equal.sym(Nat, Nat.add(d, Nat.add(10n, Nat.mul(10n, w))), Nat.add(10n, Nat.add(d, Nat.mul(10n, w))), LNatAdd.wn_add_swap(d, 10n, Nat.mul(10n, w))) : {Nat.mod(_, 10n) == d : Nat}
      %Equal.sym(Nat, Nat.mod(10n+Nat.add(d, Nat.mul(10n, w)), 10n), Nat.mod(Nat.add(d, Nat.mul(10n, w)), 10n), LPair.wn_mod_step(Nat.add(d, Nat.mul(10n, w)))) : {_ == d : Nat}
      wn_um(w, d, h)

def wn_nz_lt(+d: Nat, c: {LBoolMisc.wn_nz10(d) == True{} : Bool}) -> {LBoolMisc.wn_lt10(d) == True{} : Bool}:
  match d:
    case 0n:
      LBoolMisc.wn_absurd({LBoolMisc.wn_lt10(0n) == True{} : Bool}, c)
    case 1n+p:
      c

def wn_okc_lt(t: List<&2, Nat>, +d: Nat, c: {LBoolMisc.wn_okc(t, d) == True{} : Bool}) -> {LBoolMisc.wn_lt10(d) == True{} : Bool}:
  match t:
    case Nil{}:
      wn_nz_lt(d, c)
    case Con{e, u}:
      LBoolAnd.wn_and_l(LBoolMisc.wn_lt10(d), LBoolMisc.wn_okc(u, e), c)

# a canonical list is not worth 0
def wn_vp(u: List<&2, Nat>, +e: Nat, -G: Type, cu: {LBoolMisc.wn_okc(u, e) == True{} : Bool}, eq: {LNatMisc.wo_value(e <> u) == 0n : Nat}) -> G:
  match u:
    case Nil{}:
      LBoolMisc.wn_absurd(G, Equal.trans(Bool, False{}, LBoolMisc.wn_nz10(e), True{},
        Equal.sym(Bool, LBoolMisc.wn_nz10(e), False{}, Equal.cong(Nat, Bool, LBoolMisc.wn_nz10, e, 0n, wn_add_eq_zero_l(e, Nat.mul(10n, 0n), eq))), cu))
    case Con{+e2, +u2}:
      wn_vp(u2, e2, G, LBoolAnd.wn_and_r(LBoolMisc.wn_lt10(e), LBoolMisc.wn_okc(u2, e2), cu),
        wn_add_eq_zero_l(LNatMisc.wo_value(e2 <> u2), Nat.mul(9n, LNatMisc.wo_value(e2 <> u2)),
          wn_add_eq_zero_r(e, Nat.mul(10n, LNatMisc.wo_value(e2 <> u2)), eq)))

def wn_lth(+q: Nat, +g: Nat, +e: Nat, +u: List<&2, Nat>, +eq: {LNatMisc.wo_value(e <> u) == q : Nat}, +cu: {LBoolMisc.wn_okc(u, e) == True{} : Bool},
  h: {Nat.is_le(q, g) == True{} : Bool},
  rec: @d2: Nat -> @g2: Nat -> {LBoolMisc.wn_okc(u, d2) == True{} : Bool} -> {Nat.is_le(LNatMisc.wo_value(u), g2) == True{} : Bool}
    -> {LList.wn_L(g2, LNatMisc.wo_value(u)) == u : List<&2, Nat>})
  -> {LList.wn_L(g, q) == e <> u : List<&2, Nat>}:
  match q g:
    case 0n 0n:
      wn_vp(u, e, {LList.wn_L(0n, 0n) == e <> u : List<&2, Nat>}, cu, eq)
    case 0n 1n+f:
      wn_vp(u, e, {LList.wn_L(1n+f, 0n) == e <> u : List<&2, Nat>}, cu, eq)
    case 1n+p 0n:
      LBoolMisc.wn_absurd({LList.wn_L(0n, 1n+p) == e <> u : List<&2, Nat>}, h)
    case 1n+p 1n+f:
      +he = wn_okc_lt(u, e, cu)
      +ed = Equal.trans(Nat, Nat.div(1n+p, 10n), Nat.div(LNatMisc.wo_value(e <> u), 10n), LNatMisc.wo_value(u),
        Equal.cong(Nat, Nat, x => Nat.div(x, 10n), 1n+p, LNatMisc.wo_value(e <> u), Equal.sym(Nat, LNatMisc.wo_value(e <> u), 1n+p, eq)),
        wn_ud(LNatMisc.wo_value(u), e, he))
      +em = Equal.trans(Nat, Nat.mod(1n+p, 10n), Nat.mod(LNatMisc.wo_value(e <> u), 10n), e,
        Equal.cong(Nat, Nat, x => Nat.mod(x, 10n), 1n+p, LNatMisc.wo_value(e <> u), Equal.sym(Nat, LNatMisc.wo_value(e <> u), 1n+p, eq)),
        wn_um(LNatMisc.wo_value(u), e, he))
      +fuel = Equal.trans(Bool, Nat.is_le(LNatMisc.wo_value(u), f), Nat.is_le(Nat.div(1n+p, 10n), f), True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, f), LNatMisc.wo_value(u), Nat.div(1n+p, 10n), Equal.sym(Nat, Nat.div(1n+p, 10n), LNatMisc.wo_value(u), ed)),
        LNatIsLe.wn_le_trans(Nat.div(1n+p, 10n), p, f, LPair.wn_div_lt(p), h))
      %Equal.sym(Nat, Nat.mod(1n+p, 10n), e, em) : {_ <> LList.wn_L(f, Nat.div(1n+p, 10n)) == e <> u : List<&2, Nat>}
      %Equal.sym(Nat, Nat.div(1n+p, 10n), LNatMisc.wo_value(u), ed) : {e <> LList.wn_L(f, _) == e <> u : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, LList.wn_L(f, LNatMisc.wo_value(u)), u, rec(e, f, cu, fuel)) : {e <> _ == e <> u : List<&2, Nat>}
      {==}

def wn_lt(t: List<&2, Nat>) -> @d: Nat -> @g: Nat -> {LBoolMisc.wn_okc(t, d) == True{} : Bool} -> {Nat.is_le(LNatMisc.wo_value(t), g) == True{} : Bool}
  -> {LList.wn_L(g, LNatMisc.wo_value(t)) == t : List<&2, Nat>}:
  match t:
    case Nil{}:
      d => g => c => h => LList.wn_Lzero(g)
    case Con{+e, +u}:
      d => g => c => h =>
        wn_lth(LNatMisc.wo_value(e <> u), g, e, u, {==}, LBoolAnd.wn_and_r(LBoolMisc.wn_lt10(d), LBoolMisc.wn_okc(u, e), c), h, wn_lt(u))

# the digits of the value of a canonical list are that list
def wn_lv(+t: List<&2, Nat>, +d: Nat, +c: {LBoolMisc.wn_okc(t, d) == True{} : Bool}) -> {LList.wn_full(LNatMisc.wo_value(d <> t)) == d <> t : List<&2, Nat>}:
  +he = wn_okc_lt(t, d, c)
  +ed = wn_ud(LNatMisc.wo_value(t), d, he)
  +fuel = Equal.trans(Bool, Nat.is_le(LNatMisc.wo_value(t), LNatMisc.wo_value(d <> t)), Nat.is_le(Nat.div(LNatMisc.wo_value(d <> t), 10n), LNatMisc.wo_value(d <> t)), True{},
    Equal.cong(Nat, Bool, x => Nat.is_le(x, LNatMisc.wo_value(d <> t)), LNatMisc.wo_value(t), Nat.div(LNatMisc.wo_value(d <> t), 10n),
      Equal.sym(Nat, Nat.div(LNatMisc.wo_value(d <> t), 10n), LNatMisc.wo_value(t), ed)),
    LPair.wn_div_le(LNatMisc.wo_value(d <> t)))
  %Equal.sym(Nat, Nat.mod(LNatMisc.wo_value(d <> t), 10n), d, wn_um(LNatMisc.wo_value(t), d, he)) : {_ <> LList.wn_L(LNatMisc.wo_value(d <> t), Nat.div(LNatMisc.wo_value(d <> t), 10n)) == d <> t : List<&2, Nat>}
  %Equal.sym(Nat, Nat.div(LNatMisc.wo_value(d <> t), 10n), LNatMisc.wo_value(t), ed) : {d <> LList.wn_L(LNatMisc.wo_value(d <> t), _) == d <> t : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, LList.wn_L(LNatMisc.wo_value(d <> t), LNatMisc.wo_value(t)), t, wn_lt(t)(d, LNatMisc.wo_value(d <> t), c, fuel)) : {d <> _ == d <> t : List<&2, Nat>}
  {==}

# ---- the decoder ----

def wn_isgot(r: Wr.Dec<Nat>) -> Bool:
  match r:
    case Wr.Got{v, s}:
      True{}
    case Wr.Bad{}:
      False{}

def wn_bad_got(-G: Type, -n: Nat, -s: String, e: {Wr.Bad{} == Wr.Got{n, s} : Wr.Dec<Nat>}) -> G:
  LBoolMisc.wn_absurd(G, Equal.cong(Wr.Dec<Nat>, Bool, wn_isgot, Wr.Bad{}, Wr.Got{n, s}, e))

# ---- wire: u32 ----

# ---- wire: U32 (prefix wu_) ----

# Bool / Nat kit (copied from the bend skill, examples/sort/proof/kit.bend)

# a motive that is the goal G at True and trivial at False
def wu_Clash(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

# False == True proves anything
def wu_absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : wu_Clash(_, G)
  Unit{}
