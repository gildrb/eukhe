# eukhe: the proof of LAW tui_color_ffi_band
# The request reads back whole (LA.tcf.dec). The entry's test of a share
# num / D (D = 1 + dp) asks whether t reaches need = num * q + Q, with
# w = q * D + r and num * r + dp = Q * D + R (R <= dp); the model asks
# whether w * num <= t * D. With P = num * q * D and K = num * r,
# w * num = P + K (fb.wn), and K <= Q * D <= K + dp (fb.kq, fb.qk):
# - need <= t: w * num = P + K <= P + Q * D = need * D <= t * D;
# - t < need: t * D + D <= need * D = P + Q * D <= P + K + dp, so
#   t * D < P + K = w * num.
# So the two tests agree on every share (fb.reach), and the entry's band
# is the model's (fb.band_go).

import Base
import ../../bend/ffi_tui_color.bend as FTC
import ../../bend/tui_color.bend as TC
import ../../bend/wire.bend as Wr
import ../../laws/tui_color.bend as TuiColor
import ../base/nat.bend as LNat
import ./base.bend as LA

# Arithmetic
# ----------

def fb.mul_comm(+a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, LA.pu.mul_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), LNat.wn_mul_succ_r(b, p)) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %fb.mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

# rewrite the left side of a <= that holds
def fb.le_rw_l(-x: Nat, -y: Nat, -z: Nat, e: {x == y : Nat}, h: {Nat.is_le(x, z) == True{} : Bool}) -> {Nat.is_le(y, z) == True{} : Bool}:
  %e : {Nat.is_le(_, z) == True{} : Bool}
  h

# rewrite the right side of a <= that holds
def fb.le_rw_r(-x: Nat, -y: Nat, -z: Nat, e: {y == z : Nat}, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x, z) == True{} : Bool}:
  %e : {Nat.is_le(x, _) == True{} : Bool}
  h

# a + d <= b + d gives a <= b
def fb.le_cancel_r(+a: Nat, +b: Nat, +d: Nat, +h: {Nat.is_le(Nat.add(a, d), Nat.add(b, d)) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  +h1 = fb.le_rw_l(Nat.add(a, d), Nat.add(d, a), Nat.add(b, d), LNat.pa.add_comm(a, d), h)
  +h2 = fb.le_rw_r(Nat.add(d, a), Nat.add(b, d), Nat.add(d, b), LNat.pa.add_comm(b, d), h1)
  LA.pu.le_add_cancel_l(d, a, b, h2)

# The share test
# --------------

# w * num = num * q * D + num * r
def fb.wn(+num: Nat, +dp: Nat, +w: Nat) -> {Nat.mul(w, num) == Nat.add(Nat.mul(Nat.mul(num, Nat.div(w, 1n+dp)), 1n+dp), Nat.mul(num, Nat.mod(w, 1n+dp))) : Nat}:
  +d = {1n+dp : Nat}
  +q = Nat.div(w, d)
  +r = Nat.mod(w, d)
  +rhs = Nat.add(Nat.mul(Nat.mul(num, q), d), Nat.mul(num, r))
  %LA.pu.div_eq(w, dp) : {Nat.mul(_, num) == rhs : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(q, d), r), num), Nat.add(Nat.mul(Nat.mul(q, d), num), Nat.mul(r, num)), LA.pu.mul_add_r(Nat.mul(q, d), r, num)) : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.mul(r, num), Nat.mul(num, r), fb.mul_comm(r, num)) : {Nat.add(Nat.mul(Nat.mul(q, d), num), _) == rhs : Nat}
  +e = Equal.trans(Nat, Nat.mul(Nat.mul(num, q), d), Nat.mul(num, Nat.mul(q, d)), Nat.mul(Nat.mul(q, d), num), LA.pu.mul_assoc(num, q, d), Equal.sym(Nat, Nat.mul(Nat.mul(q, d), num), Nat.mul(num, Nat.mul(q, d)), fb.mul_comm(Nat.mul(q, d), num)))
  %e : {Nat.add(_, Nat.mul(num, r)) == rhs : Nat}
  {==}

# K <= Q * D: K + dp = Q * D + R with R <= dp
def fb.kq(+k: Nat, +dp: Nat) -> {Nat.is_le(k, Nat.mul(Nat.div(Nat.add(k, dp), 1n+dp), 1n+dp)) == True{} : Bool}:
  +x = Nat.add(k, dp)
  +qd = Nat.mul(Nat.div(x, 1n+dp), 1n+dp)
  +rr = Nat.mod(x, 1n+dp)
  +h1 = LA.pu.le_add_l(qd, rr, dp, LA.pu.mod_le(x, dp))
  +h2 = fb.le_rw_l(Nat.add(qd, rr), x, Nat.add(qd, dp), LA.pu.div_eq(x, dp), h1)
  fb.le_cancel_r(k, qd, dp, h2)

# Q * D <= K + dp
def fb.qk(+k: Nat, +dp: Nat) -> {Nat.is_le(Nat.mul(Nat.div(Nat.add(k, dp), 1n+dp), 1n+dp), Nat.add(k, dp)) == True{} : Bool}:
  +x = Nat.add(k, dp)
  +qd = Nat.mul(Nat.div(x, 1n+dp), 1n+dp)
  fb.le_rw_r(qd, Nat.add(qd, Nat.mod(x, 1n+dp)), x, LA.pu.div_eq(x, dp), LNat.pu.le_add_r(qd, Nat.mod(x, 1n+dp)))

# need * D = P + Q * D
def fb.nd(+a: Nat, +qq: Nat, +dp: Nat) -> {Nat.mul(Nat.add(a, qq), 1n+dp) == Nat.add(Nat.mul(a, 1n+dp), Nat.mul(qq, 1n+dp)) : Nat}:
  LA.pu.mul_add_r(a, qq, 1n+dp)

# need <= t: the model's test holds
def fb.le_case(+num: Nat, +dp: Nat, +t: Nat, +w: Nat, +h: {Nat.is_le(FTC.need(num, dp, w), t) == True{} : Bool}) -> {Nat.is_le(Nat.mul(w, num), Nat.mul(t, 1n+dp)) == True{} : Bool}:
  +d = {1n+dp : Nat}
  +k = Nat.mul(num, Nat.mod(w, d))
  +a = Nat.mul(num, Nat.div(w, d))
  +qq = Nat.div(Nat.add(k, dp), d)
  +p = Nat.mul(a, d)
  +qd = Nat.mul(qq, d)
  +h1 = fb.le_rw_l(Nat.mul(Nat.add(a, qq), d), Nat.add(p, qd), Nat.mul(t, d), fb.nd(a, qq, dp), LA.pu.mul_le_mono_l(Nat.add(a, qq), t, d, h))
  +h2 = LNat.pu.le_trans(Nat.add(p, k), Nat.add(p, qd), Nat.mul(t, d), LA.pu.le_add_l(p, k, qd, fb.kq(k, dp)), h1)
  %Equal.sym(Nat, Nat.mul(w, num), Nat.add(p, k), fb.wn(num, dp, w)) : {Nat.is_le(_, Nat.mul(t, d)) == True{} : Bool}
  h2

# t < need: the model's test fails
def fb.gt_case(+num: Nat, +dp: Nat, +t: Nat, +w: Nat, +h: {Nat.is_le(FTC.need(num, dp, w), t) == False{} : Bool}) -> {Nat.is_le(Nat.mul(w, num), Nat.mul(t, 1n+dp)) == False{} : Bool}:
  +d = {1n+dp : Nat}
  +k = Nat.mul(num, Nat.mod(w, d))
  +a = Nat.mul(num, Nat.div(w, d))
  +qq = Nat.div(Nat.add(k, dp), d)
  +p = Nat.mul(a, d)
  +qd = Nat.mul(qq, d)
  +m = Nat.mul(t, d)
  +pk = Nat.add(p, k)
  +s1 = LA.pu.le_succ_of_lt(t, Nat.add(a, qq), LA.pu.not_le_lt(Nat.add(a, qq), t, h))
  +s2 = fb.le_rw_r(Nat.add(d, m), Nat.mul(Nat.add(a, qq), d), Nat.add(p, qd), fb.nd(a, qq, dp), LA.pu.mul_le_mono_l(1n+t, Nat.add(a, qq), d, s1))
  +s3 = LNat.pu.le_trans(Nat.add(d, m), Nat.add(p, qd), Nat.add(p, Nat.add(k, dp)), s2, LA.pu.le_add_l(p, qd, Nat.add(k, dp), fb.qk(k, dp)))
  +s4 = fb.le_rw_r(Nat.add(d, m), Nat.add(p, Nat.add(k, dp)), Nat.add(pk, dp), Equal.sym(Nat, Nat.add(pk, dp), Nat.add(p, Nat.add(k, dp)), LA.pu.add_assoc(p, k, dp)), s3)
  +s5 = fb.le_rw_l(Nat.add(d, m), Nat.add(1n+m, dp), Nat.add(pk, dp), Equal.trans(Nat, Nat.add(d, m), Nat.add(m, d), Nat.add(1n+m, dp), LNat.pa.add_comm(d, m), LNat.pa.add_succ(m, dp)), s4)
  +s6 = fb.le_cancel_r(1n+m, pk, dp, s5)
  %Equal.sym(Nat, Nat.mul(w, num), pk, fb.wn(num, dp, w)) : {Nat.is_le(_, m) == False{} : Bool}
  LA.pu.lt_not_le(m, pk, LA.pu.lt_of_le_succ(m, pk, s6))

def fb.pick(+b: Bool, +num: Nat, +dp: Nat, +t: Nat, +w: Nat, +eb: {Nat.is_le(FTC.need(num, dp, w), t) == b : Bool}) -> {b == Nat.is_le(Nat.mul(w, num), Nat.mul(t, 1n+dp)) : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, Nat.is_le(Nat.mul(w, num), Nat.mul(t, 1n+dp)), True{}, fb.le_case(num, dp, t, w, eb))
    case False{}:
      Equal.sym(Bool, Nat.is_le(Nat.mul(w, num), Nat.mul(t, 1n+dp)), False{}, fb.gt_case(num, dp, t, w, eb))

# the entry's test of a share is the model's
def fb.reach(+f: TC.Frac, +t: Nat, +w: Nat) -> {FTC.reach(f, t, w) == TC.reached(f, t, w) : Bool}:
  match f:
    case TC.Frac{+num, den}:
      match den:
        case 0n:
          {==}
        case 1n+dp:
          %fb.pick(Nat.is_le(FTC.need(num, dp, w), t), num, dp, t, w, {==}) : {Bool.and(Nat.is_lt(0n, w), Nat.is_le(FTC.need(num, dp, w), t)) == Bool.and(Nat.is_lt(0n, w), _) : Bool}
          {==}

# the entry's band is the model's, on any list of shares
def fb.band_go(+fs: List<&2, TC.Frac>, +t: Nat, +w: Nat) -> {FTC.band.go(fs, t, w) == TC.band.go(fs, t, w) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, rest}:
      %fb.band_go(rest, t, w) : {Nat.add(TC.one(FTC.reach(f, t, w)), FTC.band.go(rest, t, w)) == Nat.add(TC.one(TC.reached(f, t, w)), _) : Nat}
      %fb.reach(f, t, w) : {Nat.add(TC.one(FTC.reach(f, t, w)), FTC.band.go(rest, t, w)) == Nat.add(TC.one(_), FTC.band.go(rest, t, w)) : Nat}
      {==}

def TuiColor.tui_color_ffi_band(t, w, fit):
  +q = {FTC.QBand{t, w} : FTC.Req}
  +rhs = Wr.put_nat(TC.band(t, w), "")
  %Equal.sym(Wr.Dec<FTC.Req>, FTC.get_req(TuiColor.spell_req(q, "")), Wr.Got{q, ""}, LA.tcf.dec(q, "", fit)) : {FTC.run(_) == rhs : String}
  %fb.band_go(TC.bands(), t, w) : {Wr.put_nat(FTC.band(t, w), "") == Wr.put_nat(_, "") : String}
  {==}
