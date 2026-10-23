# eukhe: lemmas the proofs of two or more areas share: semver

import Base
import ../../bend/semver.bend as Sv
import ./logic/bool.bend as LLogicBool
import ./logic/list.bend as LLogicList
import ./logic/logic.bend as LLogicLogic
import ./logic/nat.bend as LLogicNat
import ./logic/semver.bend as LLogicSemver
import ./nat.bend as LNat

def ps.digs_refl(+ds: List<&2, Sv.Dig>) -> {True{} == Sv.Num.digs_eq(ds, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> r:
      %LNat.semver.ps.eq_refl(Sv.Dig.val(d)) : {True{} == Bool.and(_, Sv.Num.digs_eq(r, r)) : Bool}
      ps.digs_refl(r)

# The rank's field reader against semver.bend's Num.read
# -------------------------------------------------------

def rk.ten_mul(v: Nat) -> {Sv.Num.ten(v) == Nat.mul(v, 10n) : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      %rk.ten_mul(p) : {Nat.add(10n, Sv.Num.ten(p)) == Nat.add(10n, _) : Nat}
      {==}

# ten increments carry once and leave the last digit as it was
def rk.inc10(d: Sv.Dig, -r: List<&2, Sv.Dig>) -> {LLogicList.rk.I10(d <> r) == d <> Sv.Num.inc(r) : List<&2, Sv.Dig>}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

def rk.dec10(m: Nat) -> {Sv.Num.dec(Nat.add(10n, m)) == LLogicList.rk.I10(Sv.Num.dec(m)) : List<&2, Sv.Dig>}:
  {==}

def rk.dec_step0(d: Sv.Dig) -> {Sv.Num.dec(Nat.add(Sv.Dig.val(d), Sv.Num.ten(1n))) == d <> Sv.Num.dec(1n) : List<&2, Sv.Dig>}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

# d + 10 * (1 + u) is written as d after the digits of 1 + u
def rk.dec_step(+d: Sv.Dig, u: Nat) -> {Sv.Num.dec(Nat.add(Sv.Dig.val(d), Sv.Num.ten(1n+u))) == d <> Sv.Num.dec(1n+u) : List<&2, Sv.Dig>}:
  match u:
    case 0n:
      rk.dec_step0(d)
    case 1n++w:
      +X = Sv.Num.ten(1n+w)
      +v = Sv.Dig.val(d)
      Equal.trans(List<&2, Sv.Dig>, Sv.Num.dec(Nat.add(v, Nat.add(10n, X))), Sv.Num.dec(Nat.add(10n, Nat.add(v, X))), d <> Sv.Num.inc(Sv.Num.dec(1n+w)), Equal.cong(Nat, List<&2, Sv.Dig>, Sv.Num.dec, Nat.add(v, Nat.add(10n, X)), Nat.add(10n, Nat.add(v, X)), LNat.rk.add_swap(10n, v, X)), Equal.trans(List<&2, Sv.Dig>, Sv.Num.dec(Nat.add(10n, Nat.add(v, X))), LLogicList.rk.I10(Sv.Num.dec(Nat.add(v, X))), d <> Sv.Num.inc(Sv.Num.dec(1n+w)), rk.dec10(Nat.add(v, X)), Equal.trans(List<&2, Sv.Dig>, LLogicList.rk.I10(Sv.Num.dec(Nat.add(v, X))), LLogicList.rk.I10(d <> Sv.Num.dec(1n+w)), d <> Sv.Num.inc(Sv.Num.dec(1n+w)), Equal.cong(List<&2, Sv.Dig>, List<&2, Sv.Dig>, LLogicList.rk.I10, Sv.Num.dec(Nat.add(v, X)), d <> Sv.Num.dec(1n+w), rk.dec_step(d, w)), rk.inc10(d, Sv.Num.dec(1n+w)))))

def rk.h1_at(+d: Sv.Dig, +rest: List<&2, Sv.Dig>, V: Nat, +eV: {Sv.Num.val(rest) == V : Nat}, nz: {Sv.Num.val(rest) == 0n : Nat} -> Empty, ih: {Sv.Num.dec(Sv.Num.val(rest)) == rest : List<&2, Sv.Dig>}) -> {Sv.Num.dec(Nat.add(Sv.Dig.val(d), Sv.Num.ten(V))) == d <> rest : List<&2, Sv.Dig>}:
  match V:
    case 0n:
      Empty.absurd({Sv.Num.dec(Nat.add(Sv.Dig.val(d), Sv.Num.ten(0n))) == d <> rest : List<&2, Sv.Dig>}, nz(eV))
    case 1n++u:
      Equal.trans(List<&2, Sv.Dig>, Sv.Num.dec(Nat.add(Sv.Dig.val(d), Sv.Num.ten(1n+u))), d <> Sv.Num.dec(1n+u), d <> rest, rk.dec_step(d, u), LLogicList.rk.dcons(d, Sv.Num.dec(1n+u), rest, Equal.trans(List<&2, Sv.Dig>, Sv.Num.dec(1n+u), Sv.Num.dec(Sv.Num.val(rest)), rest, Equal.cong(Nat, List<&2, Sv.Dig>, Sv.Num.dec, 1n+u, Sv.Num.val(rest), Equal.sym(Nat, Sv.Num.val(rest), 1n+u, eV)), ih)))

def rk.h1_one(d: Sv.Dig) -> {Sv.Num.dec(Sv.Num.val([d])) == [d] : List<&2, Sv.Dig>}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

def rk.ofv_val(d: Sv.Dig) -> {LLogicSemver.rk.ofv(Sv.Dig.val(d)) == d : Sv.Dig}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

def rk.dig_sound(+a: Sv.Dig, +b: Sv.Dig, h: {Sv.Dig.eq(a, b) == True{} : Bool}) -> {a == b : Sv.Dig}:
  Equal.trans(Sv.Dig, a, LLogicSemver.rk.ofv(Sv.Dig.val(a)), b, Equal.sym(Sv.Dig, LLogicSemver.rk.ofv(Sv.Dig.val(a)), a, rk.ofv_val(a)), Equal.trans(Sv.Dig, LLogicSemver.rk.ofv(Sv.Dig.val(a)), LLogicSemver.rk.ofv(Sv.Dig.val(b)), b, Equal.cong(Nat, Sv.Dig, LLogicSemver.rk.ofv, Sv.Dig.val(a), Sv.Dig.val(b), LLogicNat.semver.ps.eq_true(Sv.Dig.val(a), Sv.Dig.val(b), h)), rk.ofv_val(b)))

def rk.digs_sound(xs: List<&2, Sv.Dig>, ys: List<&2, Sv.Dig>, +h: {Sv.Num.digs_eq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Sv.Dig>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      LLogicLogic.semver.ps.absurdF({Nil{} == y <> yr : List<&2, Sv.Dig>}, h)
    case x <> xr Nil{}:
      LLogicLogic.semver.ps.absurdF({x <> xr == Nil{} : List<&2, Sv.Dig>}, h)
    case +x <> +xr +y <> +yr:
      %rk.dig_sound(x, y, LLogicBool.semver.ps.and_l(Sv.Dig.eq(x, y), Sv.Num.digs_eq(xr, yr), h)) : {x <> xr == _ <> yr : List<&2, Sv.Dig>}
      %rk.digs_sound(xr, yr, LLogicBool.semver.ps.and_r(Sv.Dig.eq(x, y), Sv.Num.digs_eq(xr, yr), h)) : {x <> xr == x <> _ : List<&2, Sv.Dig>}
      {==}

def rk.nz_d0(X: List<&2, Sv.Dig>, h: {LLogicBool.rk.nz(X) == True{} : Bool}) -> {LLogicBool.rk.nz(Sv.D0{} <> X) == True{} : Bool}:
  match X:
    case Nil{}:
      LLogicLogic.semver.ps.absurdF({LLogicBool.rk.nz(Sv.D0{} <> Nil{}) == True{} : Bool}, h)
    case x <> xs:
      h
