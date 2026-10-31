# eukhe: the insertion sorts of bend/autoresearch/stats.bend (sort, on
# digit lists) and spec/autoresearch/stats.bend (zsort, nsort) for the
# proof of LAW confidence_exact: each sorts the values as nsort does

import Base
import ../../../../bend/autoresearch/dec.bend as ArD
import ../../../../bend/autoresearch/stats.bend as ArT
import ../../../../spec/autoresearch/decimal.bend as SD
import ../../../../spec/autoresearch/stats.bend as SS
import ./nat.bend as CN
import ./big.bend as CB
import ./zint.bend as CZ

# Digit lists
# -----------

def ac.vals(xs: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      ArT.big.val(x) <> ac.vals(t)

def ac.adok(xs: List<&2, List<&2, Nat>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(SD.digits_ok(x), ac.adok(t))

def ac.adok_hd(+x: List<&2, Nat>, -t: List<&2, List<&2, Nat>>, +h: {ac.adok(x <> t) == True{} : Bool}) -> {SD.digits_ok(x) == True{} : Bool}:
  CN.ac.and_l(SD.digits_ok(x), ac.adok(t), h)

def ac.adok_tl(+x: List<&2, Nat>, -t: List<&2, List<&2, Nat>>, +h: {ac.adok(x <> t) == True{} : Bool}) -> {ac.adok(t) == True{} : Bool}:
  CN.ac.and_r(SD.digits_ok(x), ac.adok(t), h)

# big.cmp's at-most is the values' at-most
def ac.big_le(+x: List<&2, Nat>, +y: List<&2, Nat>, +hx: {SD.digits_ok(x) == True{} : Bool}, +hy: {SD.digits_ok(y) == True{} : Bool}) -> {Cmp.is_le(ArT.big.cmp(x, y, EQ{})) == Nat.is_le(ArT.big.val(x), ArT.big.val(y)) : Bool}:
  +c = Nat.cmp(ArT.big.val(x), ArT.big.val(y))
  %Equal.sym(Cmp, ArT.big.cmp(x, y, EQ{}), ArD.then(c, EQ{}), CB.ac.cmp_val(x, y, EQ{}, hx, hy)) : {Cmp.is_le(_) == Nat.is_le(ArT.big.val(x), ArT.big.val(y)) : Bool}
  %Equal.sym(Cmp, ArD.then(c, EQ{}), c, CB.ac.then_eq(c)) : {Cmp.is_le(_) == Nat.is_le(ArT.big.val(x), ArT.big.val(y)) : Bool}
  {==}

def ac.ins_val.at(le: Bool, +x: List<&2, Nat>, +y: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, +r: List<&2, List<&2, Nat>>, ih: {ac.vals(r) == SS.nins(ArT.big.val(x), ac.vals(t)) : List<&2, Nat>}) -> {ac.vals(ArT.ins.at(le, x, y, t, r)) == SS.nins.at(le, ArT.big.val(x), ArT.big.val(y), ac.vals(t), SS.nins(ArT.big.val(x), ac.vals(t))) : List<&2, Nat>}:
  match le:
    case True{}:
      {==}
    case False{}:
      %ih : {ArT.big.val(y) <> ac.vals(r) == ArT.big.val(y) <> _ : List<&2, Nat>}
      {==}

# inserting by big.cmp inserts the values
def ac.ins_val(+x: List<&2, Nat>, xs: List<&2, List<&2, Nat>>, +hx: {SD.digits_ok(x) == True{} : Bool}, +hs: {ac.adok(xs) == True{} : Bool}) -> {ac.vals(ArT.ins(x, xs)) == SS.nins(ArT.big.val(x), ac.vals(xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +t:
      +vx = ArT.big.val(x)
      +vy = ArT.big.val(y)
      %Equal.sym(Bool, Cmp.is_le(ArT.big.cmp(x, y, EQ{})), Nat.is_le(vx, vy), ac.big_le(x, y, hx, ac.adok_hd(y, t, hs))) : {ac.vals(ArT.ins.at(_, x, y, t, ArT.ins(x, t))) == SS.nins.at(Nat.is_le(vx, vy), vx, vy, ac.vals(t), SS.nins(vx, ac.vals(t))) : List<&2, Nat>}
      ac.ins_val.at(Nat.is_le(vx, vy), x, y, t, ArT.ins(x, t), ac.ins_val(x, t, hx, ac.adok_tl(y, t, hs)))

def ac.ins_dok.at(le: Bool, +x: List<&2, Nat>, +y: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, +r: List<&2, List<&2, Nat>>, +hx: {SD.digits_ok(x) == True{} : Bool}, +hy: {SD.digits_ok(y) == True{} : Bool}, +ht: {ac.adok(t) == True{} : Bool}, +hr: {ac.adok(r) == True{} : Bool}) -> {ac.adok(ArT.ins.at(le, x, y, t, r)) == True{} : Bool}:
  match le:
    case True{}:
      CN.ac.and_i(SD.digits_ok(x), ac.adok(y <> t), hx, CN.ac.and_i(SD.digits_ok(y), ac.adok(t), hy, ht))
    case False{}:
      CN.ac.and_i(SD.digits_ok(y), ac.adok(r), hy, hr)

def ac.ins_dok(+x: List<&2, Nat>, xs: List<&2, List<&2, Nat>>, +hx: {SD.digits_ok(x) == True{} : Bool}, +hs: {ac.adok(xs) == True{} : Bool}) -> {ac.adok(ArT.ins(x, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      CN.ac.and_i(SD.digits_ok(x), True{}, hx, {==})
    case +y <> +t:
      ac.ins_dok.at(Cmp.is_le(ArT.big.cmp(x, y, EQ{})), x, y, t, ArT.ins(x, t), hx, ac.adok_hd(y, t, hs), ac.adok_tl(y, t, hs), ac.ins_dok(x, t, hx, ac.adok_tl(y, t, hs)))

def ac.sort_dok(xs: List<&2, List<&2, Nat>>, +hs: {ac.adok(xs) == True{} : Bool}) -> {ac.adok(ArT.sort(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      ac.ins_dok(x, ArT.sort(t), ac.adok_hd(x, t, hs), ac.sort_dok(t, ac.adok_tl(x, t, hs)))

# the code's sort sorts the values
def ac.sort_val(xs: List<&2, List<&2, Nat>>, +hs: {ac.adok(xs) == True{} : Bool}) -> {ac.vals(ArT.sort(xs)) == SS.nsort(ac.vals(xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +ht = ac.adok_tl(x, t, hs)
      %ac.sort_val(t, ht) : {ac.vals(ArT.ins(x, ArT.sort(t))) == SS.nins(ArT.big.val(x), _) : List<&2, Nat>}
      ac.ins_val(x, ArT.sort(t), ac.adok_hd(x, t, hs), ac.sort_dok(t, ht))

# Shifted integers
# ----------------

def ac.offs(+K: Nat, zs: List<&2, SS.Z>) -> List<&2, Nat>:
  match zs:
    case Nil{}:
      Nil{}
    case z <> t:
      CZ.ac.off(K, z) <> ac.offs(K, t)

def ac.arng(+K: Nat, zs: List<&2, SS.Z>) -> Bool:
  match zs:
    case Nil{}:
      True{}
    case z <> t:
      Bool.and(CZ.ac.rng(K, z), ac.arng(K, t))

def ac.zins_off.at(le: Bool, +K: Nat, +x: SS.Z, +y: SS.Z, +t: List<&2, SS.Z>, +r: List<&2, SS.Z>, ih: {ac.offs(K, r) == SS.nins(CZ.ac.off(K, x), ac.offs(K, t)) : List<&2, Nat>}) -> {ac.offs(K, SS.zins.at(le, x, y, t, r)) == SS.nins.at(le, CZ.ac.off(K, x), CZ.ac.off(K, y), ac.offs(K, t), SS.nins(CZ.ac.off(K, x), ac.offs(K, t))) : List<&2, Nat>}:
  match le:
    case True{}:
      {==}
    case False{}:
      %ih : {CZ.ac.off(K, y) <> ac.offs(K, r) == CZ.ac.off(K, y) <> _ : List<&2, Nat>}
      {==}

def ac.zins_off(+K: Nat, +x: SS.Z, zs: List<&2, SS.Z>, +rx: {CZ.ac.rng(K, x) == True{} : Bool}, +rs: {ac.arng(K, zs) == True{} : Bool}) -> {ac.offs(K, SS.zins(x, zs)) == SS.nins(CZ.ac.off(K, x), ac.offs(K, zs)) : List<&2, Nat>}:
  match zs:
    case Nil{}:
      {==}
    case +y <> +t:
      +ox = CZ.ac.off(K, x)
      +oy = CZ.ac.off(K, y)
      +ry = CN.ac.and_l(CZ.ac.rng(K, y), ac.arng(K, t), rs)
      +rt = CN.ac.and_r(CZ.ac.rng(K, y), ac.arng(K, t), rs)
      %Equal.sym(Bool, SS.z_le(x, y), Nat.is_le(ox, oy), CZ.ac.z_le_off(K, x, y, rx, ry)) : {ac.offs(K, SS.zins.at(_, x, y, t, SS.zins(x, t))) == SS.nins.at(Nat.is_le(ox, oy), ox, oy, ac.offs(K, t), SS.nins(ox, ac.offs(K, t))) : List<&2, Nat>}
      ac.zins_off.at(Nat.is_le(ox, oy), K, x, y, t, SS.zins(x, t), ac.zins_off(K, x, t, rx, rt))

def ac.zins_rng.at(le: Bool, +K: Nat, +x: SS.Z, +y: SS.Z, +t: List<&2, SS.Z>, +r: List<&2, SS.Z>, +rx: {CZ.ac.rng(K, x) == True{} : Bool}, +ry: {CZ.ac.rng(K, y) == True{} : Bool}, +rt: {ac.arng(K, t) == True{} : Bool}, +rr: {ac.arng(K, r) == True{} : Bool}) -> {ac.arng(K, SS.zins.at(le, x, y, t, r)) == True{} : Bool}:
  match le:
    case True{}:
      CN.ac.and_i(CZ.ac.rng(K, x), ac.arng(K, y <> t), rx, CN.ac.and_i(CZ.ac.rng(K, y), ac.arng(K, t), ry, rt))
    case False{}:
      CN.ac.and_i(CZ.ac.rng(K, y), ac.arng(K, r), ry, rr)

def ac.zins_rng(+K: Nat, +x: SS.Z, zs: List<&2, SS.Z>, +rx: {CZ.ac.rng(K, x) == True{} : Bool}, +rs: {ac.arng(K, zs) == True{} : Bool}) -> {ac.arng(K, SS.zins(x, zs)) == True{} : Bool}:
  match zs:
    case Nil{}:
      CN.ac.and_i(CZ.ac.rng(K, x), True{}, rx, {==})
    case +y <> +t:
      +ry = CN.ac.and_l(CZ.ac.rng(K, y), ac.arng(K, t), rs)
      +rt = CN.ac.and_r(CZ.ac.rng(K, y), ac.arng(K, t), rs)
      ac.zins_rng.at(SS.z_le(x, y), K, x, y, t, SS.zins(x, t), rx, ry, rt, ac.zins_rng(K, x, t, rx, rt))

def ac.zsort_rng(+K: Nat, zs: List<&2, SS.Z>, +rs: {ac.arng(K, zs) == True{} : Bool}) -> {ac.arng(K, SS.zsort(zs)) == True{} : Bool}:
  match zs:
    case Nil{}:
      {==}
    case +z <> +t:
      ac.zins_rng(K, z, SS.zsort(t), CN.ac.and_l(CZ.ac.rng(K, z), ac.arng(K, t), rs), ac.zsort_rng(K, t, CN.ac.and_r(CZ.ac.rng(K, z), ac.arng(K, t), rs)))

# zsort sorts the shifted integers
def ac.zsort_off(+K: Nat, zs: List<&2, SS.Z>, +rs: {ac.arng(K, zs) == True{} : Bool}) -> {ac.offs(K, SS.zsort(zs)) == SS.nsort(ac.offs(K, zs)) : List<&2, Nat>}:
  match zs:
    case Nil{}:
      {==}
    case +z <> +t:
      +rt = CN.ac.and_r(CZ.ac.rng(K, z), ac.arng(K, t), rs)
      %ac.zsort_off(K, t, rt) : {ac.offs(K, SS.zins(z, SS.zsort(t))) == SS.nins(CZ.ac.off(K, z), _) : List<&2, Nat>}
      ac.zins_off(K, z, SS.zsort(t), CN.ac.and_l(CZ.ac.rng(K, z), ac.arng(K, t), rs), ac.zsort_rng(K, t, rt))

# Lengths
# -------

def ac.zlen(zs: List<&2, SS.Z>) -> Nat:
  match zs:
    case Nil{}:
      0n
    case z <> t:
      1n+ac.zlen(t)

def ac.nlen(ns: List<&2, Nat>) -> Nat:
  match ns:
    case Nil{}:
      0n
    case n <> t:
      1n+ac.nlen(t)

def ac.zins_len.at(le: Bool, +x: SS.Z, +y: SS.Z, +t: List<&2, SS.Z>, +r: List<&2, SS.Z>, ih: {ac.zlen(r) == 1n+ac.zlen(t) : Nat}) -> {ac.zlen(SS.zins.at(le, x, y, t, r)) == 2n+ac.zlen(t) : Nat}:
  match le:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Nat, ac.zlen(r), 1n+ac.zlen(t), ih) : {1n+_ == 2n+ac.zlen(t) : Nat}
      {==}

def ac.zins_len(+x: SS.Z, zs: List<&2, SS.Z>) -> {ac.zlen(SS.zins(x, zs)) == 1n+ac.zlen(zs) : Nat}:
  match zs:
    case Nil{}:
      {==}
    case +y <> +t:
      ac.zins_len.at(SS.z_le(x, y), x, y, t, SS.zins(x, t), ac.zins_len(x, t))

def ac.zsort_len(zs: List<&2, SS.Z>) -> {ac.zlen(SS.zsort(zs)) == ac.zlen(zs) : Nat}:
  match zs:
    case Nil{}:
      {==}
    case +z <> +t:
      %ac.zsort_len(t) : {ac.zlen(SS.zins(z, SS.zsort(t))) == 1n+_ : Nat}
      ac.zins_len(z, SS.zsort(t))

def ac.offs_len(+K: Nat, zs: List<&2, SS.Z>) -> {ac.nlen(ac.offs(K, zs)) == ac.zlen(zs) : Nat}:
  match zs:
    case Nil{}:
      {==}
    case z <> +t:
      %ac.offs_len(K, t) : {1n+ac.nlen(ac.offs(K, t)) == 1n+_ : Nat}
      {==}

# Adding a constant
# -----------------

def ac.addc(+c: Nat, ns: List<&2, Nat>) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> t:
      Nat.add(c, n) <> ac.addc(c, t)

def ac.nins_addc.at(le: Bool, +c: Nat, +x: Nat, +y: Nat, +t: List<&2, Nat>, +r: List<&2, Nat>, ih: {SS.nins(Nat.add(c, x), ac.addc(c, t)) == ac.addc(c, r) : List<&2, Nat>}) -> {SS.nins.at(le, Nat.add(c, x), Nat.add(c, y), ac.addc(c, t), SS.nins(Nat.add(c, x), ac.addc(c, t))) == ac.addc(c, SS.nins.at(le, x, y, t, r)) : List<&2, Nat>}:
  match le:
    case True{}:
      {==}
    case False{}:
      %ih : {Nat.add(c, y) <> SS.nins(Nat.add(c, x), ac.addc(c, t)) == Nat.add(c, y) <> _ : List<&2, Nat>}
      {==}

def ac.nins_addc(+c: Nat, +x: Nat, ns: List<&2, Nat>) -> {SS.nins(Nat.add(c, x), ac.addc(c, ns)) == ac.addc(c, SS.nins(x, ns)) : List<&2, Nat>}:
  match ns:
    case Nil{}:
      {==}
    case +y <> +t:
      %Equal.sym(Bool, Nat.is_le(Nat.add(c, x), Nat.add(c, y)), Nat.is_le(x, y), CN.ac.le_cancel(c, x, y)) : {SS.nins.at(_, Nat.add(c, x), Nat.add(c, y), ac.addc(c, t), SS.nins(Nat.add(c, x), ac.addc(c, t))) == ac.addc(c, SS.nins.at(Nat.is_le(x, y), x, y, t, SS.nins(x, t))) : List<&2, Nat>}
      ac.nins_addc.at(Nat.is_le(x, y), c, x, y, t, SS.nins(x, t), ac.nins_addc(c, x, t))

def ac.nsort_addc(+c: Nat, ns: List<&2, Nat>) -> {SS.nsort(ac.addc(c, ns)) == ac.addc(c, SS.nsort(ns)) : List<&2, Nat>}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +t:
      %Equal.sym(List<&2, Nat>, SS.nsort(ac.addc(c, t)), ac.addc(c, SS.nsort(t)), ac.nsort_addc(c, t)) : {SS.nins(Nat.add(c, n), _) == ac.addc(c, SS.nins(n, SS.nsort(t))) : List<&2, Nat>}
      ac.nins_addc(c, n, SS.nsort(t))

def ac.addc_len(+c: Nat, ns: List<&2, Nat>) -> {ac.nlen(ac.addc(c, ns)) == ac.nlen(ns) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      %ac.addc_len(c, t) : {1n+ac.nlen(ac.addc(c, t)) == 1n+_ : Nat}
      {==}
