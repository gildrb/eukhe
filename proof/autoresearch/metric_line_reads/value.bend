# eukhe: lemmas of LAW metric_line_reads: the value canon reads from
# well-formed parts is canonical, worth the value as written, and fits
# exactly when the spec's significant digits do

import Base
import ../../../bend/autoresearch/dec.bend as D
import ../../../bend/autoresearch/line.bend as L
import ../../../spec/autoresearch/decimal.bend as SD
import ../../../spec/autoresearch/metric_line.bend as SL
import ../base/line.bend as AL

# Names for the terms canon builds
# --------------------------------

def alv.app(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  List.append(&2, Nat, a, b)

# the fraction without its trailing zeros
def alv.f(fs: List<&2, Nat>) -> List<&2, Nat>:
  L.strip(fs)

# how many zeros that drops
def alv.k(fs: List<&2, Nat>) -> Nat:
  AL.al.tz(fs)

# the digits joined
def alv.ci(int: List<&2, Nat>, fs: List<&2, Nat>) -> List<&2, Nat>:
  D.cat(int, L.strip(fs))

# the digits canon keeps
def alv.ds(int: List<&2, Nat>, fs: List<&2, Nat>) -> List<&2, Nat>:
  L.drop(D.cat(int, L.strip(fs)))

# the spec's significant digits
def alv.sig(int: List<&2, Nat>, fs: List<&2, Nat>) -> List<&2, Nat>:
  SL.trim_lead(List.append(&2, Nat, int, SL.trim_trail(fs)))

# Digits and length
# -----------------

# canon keeps exactly the spec's significant digits
def alv.sig_eq(+int: List<&2, Nat>, +fs: List<&2, Nat>) -> {D.len(alv.ds(int, fs)) == SL.dlen(alv.sig(int, fs)) : Nat}:
  Equal.trans(Nat, D.len(alv.ds(int, fs)), SL.dlen(alv.ds(int, fs)), SL.dlen(alv.sig(int, fs)), AL.al.len_dlen(alv.ds(int, fs)), Equal.cong(List<&2, Nat>, Nat, l => SL.dlen(l), alv.ds(int, fs), alv.sig(int, fs), Equal.trans(List<&2, Nat>, alv.ds(int, fs), SL.trim_lead(alv.ci(int, fs)), alv.sig(int, fs), AL.al.drop_trim(alv.ci(int, fs)), Equal.cong(List<&2, Nat>, List<&2, Nat>, l => SL.trim_lead(l), alv.ci(int, fs), alv.app(int, SL.trim_trail(fs)), Equal.trans(List<&2, Nat>, alv.ci(int, fs), alv.app(int, alv.f(fs)), alv.app(int, SL.trim_trail(fs)), AL.al.cat_app(int, alv.f(fs)), Equal.cong(List<&2, Nat>, List<&2, Nat>, l => alv.app(int, l), alv.f(fs), SL.trim_trail(fs), AL.al.strip_trim(fs)))))))

# Worth
# -----

# the digits as written are the kept digits, k places up
def alv.v1(+int: List<&2, Nat>, +fs: List<&2, Nat>) -> {SD.num(alv.app(int, fs)) == SD.shift(alv.k(fs), SD.num(alv.ds(int, fs))) : Nat}:
  Equal.trans(Nat, SD.num(alv.app(int, fs)), SD.num(alv.app(int, alv.app(alv.f(fs), D.zeros(alv.k(fs))))), SD.shift(alv.k(fs), SD.num(alv.ds(int, fs))), Equal.cong(List<&2, Nat>, Nat, l => SD.num(alv.app(int, l)), fs, alv.app(alv.f(fs), D.zeros(alv.k(fs))), Equal.sym(List<&2, Nat>, alv.app(alv.f(fs), D.zeros(alv.k(fs))), fs, AL.al.strip_tz(fs))), Equal.trans(Nat, SD.num(alv.app(int, alv.app(alv.f(fs), D.zeros(alv.k(fs))))), SD.num(alv.app(alv.app(int, alv.f(fs)), D.zeros(alv.k(fs)))), SD.shift(alv.k(fs), SD.num(alv.ds(int, fs))), Equal.cong(List<&2, Nat>, Nat, l => SD.num(l), alv.app(int, alv.app(alv.f(fs), D.zeros(alv.k(fs)))), alv.app(alv.app(int, alv.f(fs)), D.zeros(alv.k(fs))), Equal.sym(List<&2, Nat>, alv.app(alv.app(int, alv.f(fs)), D.zeros(alv.k(fs))), alv.app(int, alv.app(alv.f(fs), D.zeros(alv.k(fs)))), AL.al.app_assoc(int, alv.f(fs), D.zeros(alv.k(fs))))), Equal.trans(Nat, SD.num(alv.app(alv.app(int, alv.f(fs)), D.zeros(alv.k(fs)))), SD.shift(alv.k(fs), SD.num(alv.app(int, alv.f(fs)))), SD.shift(alv.k(fs), SD.num(alv.ds(int, fs))), AL.al.num_app_zeros(alv.app(int, alv.f(fs)), alv.k(fs), 0n), Equal.cong(Nat, Nat, x => SD.shift(alv.k(fs), x), SD.num(alv.app(int, alv.f(fs))), SD.num(alv.ds(int, fs)), Equal.sym(Nat, SD.num(alv.ds(int, fs)), SD.num(alv.app(int, alv.f(fs))), Equal.trans(Nat, SD.num(alv.ds(int, fs)), SD.num(alv.ci(int, fs)), SD.num(alv.app(int, alv.f(fs))), AL.al.num_drop(alv.ci(int, fs)), Equal.cong(List<&2, Nat>, Nat, l => SD.num(l), alv.ci(int, fs), alv.app(int, alv.f(fs)), AL.al.cat_app(int, alv.f(fs)))))))))

# the fraction is the kept fraction and k zeros
def alv.v2(+fs: List<&2, Nat>) -> {SL.dlen(fs) == Nat.add(alv.k(fs), D.len(alv.f(fs))) : Nat}:
  Equal.trans(Nat, SL.dlen(fs), SL.dlen(alv.app(alv.f(fs), D.zeros(alv.k(fs)))), Nat.add(alv.k(fs), D.len(alv.f(fs))), Equal.sym(Nat, SL.dlen(alv.app(alv.f(fs), D.zeros(alv.k(fs)))), SL.dlen(fs), Equal.cong(List<&2, Nat>, Nat, l => SL.dlen(l), alv.app(alv.f(fs), D.zeros(alv.k(fs))), fs, AL.al.strip_tz(fs))), AL.al.dlen_app_zeros(alv.f(fs), alv.k(fs)))

# both decimals brought to one scale are one number
def alv.e(+int: List<&2, Nat>, +fs: List<&2, Nat>) -> {SD.shift(SL.dlen(fs), SD.num(alv.ds(int, fs))) == SD.shift(D.len(alv.f(fs)), SD.num(alv.app(int, fs))) : Nat}:
  Equal.trans(Nat, SD.shift(SL.dlen(fs), SD.num(alv.ds(int, fs))), SD.shift(Nat.add(alv.k(fs), D.len(alv.f(fs))), SD.num(alv.ds(int, fs))), SD.shift(D.len(alv.f(fs)), SD.num(alv.app(int, fs))), Equal.cong(Nat, Nat, n => SD.shift(n, SD.num(alv.ds(int, fs))), SL.dlen(fs), Nat.add(alv.k(fs), D.len(alv.f(fs))), alv.v2(fs)), Equal.trans(Nat, SD.shift(Nat.add(alv.k(fs), D.len(alv.f(fs))), SD.num(alv.ds(int, fs))), SD.shift(D.len(alv.f(fs)), SD.shift(alv.k(fs), SD.num(alv.ds(int, fs)))), SD.shift(D.len(alv.f(fs)), SD.num(alv.app(int, fs))), AL.al.shift_add(alv.k(fs), D.len(alv.f(fs)), SD.num(alv.ds(int, fs))), Equal.cong(Nat, Nat, x => SD.shift(D.len(alv.f(fs)), x), SD.shift(alv.k(fs), SD.num(alv.ds(int, fs))), SD.num(alv.app(int, fs)), Equal.sym(Nat, SD.num(alv.app(int, fs)), SD.shift(alv.k(fs), SD.num(alv.ds(int, fs))), alv.v1(int, fs)))))

# the decimal canon builds is worth the value as written
def alv.same(neg: Bool, ds: List<&2, Nat>, lf: Nat, dl: Nat, -a2: List<&2, Nat>, k: Nat, v1: {SD.num(a2) == SD.shift(k, SD.num(ds)) : Nat}, e: {SD.shift(dl, SD.num(ds)) == SD.shift(lf, SD.num(a2)) : Nat}) -> {SD.same(D.Dec{Bool.and(neg, L.any_d(ds)), ds, lf}, D.Dec{neg, a2, dl}) == True{} : Bool}:
  match neg:
    case False{}:
      %e : {Cmp.is_eq(Nat.cmp(SD.shift(dl, SD.num(ds)), _)) == True{} : Bool}
      AL.al.cmp_self(SD.shift(dl, SD.num(ds)))
    case True{}:
      match ds:
        case Nil{}:
          %Equal.sym(Nat, SD.num(a2), 0n, Equal.trans(Nat, SD.num(a2), SD.shift(k, 0n), 0n, v1, AL.al.shift_zero(k))) : {Cmp.is_eq(SD.order.cross(Nat.is_eq(_, 0n), GT{})) == True{} : Bool}
          {==}
        case h <> t:
          %e : {Cmp.is_eq(Nat.cmp(_, SD.shift(dl, SD.num(h <> t)))) == True{} : Bool}
          AL.al.cmp_self(SD.shift(dl, SD.num(h <> t)))

# Canonical
# ---------

def alv.canon(ds: List<&2, Nat>, neg: Bool, +f: List<&2, Nat>, h1: {AL.al.headnz(ds) == True{} : Bool}, h2: {SD.digits_ok(ds) == True{} : Bool}, hf: {Bool.or(Nat.is_eq(D.len(f), 0n), SD.last_nz(ds)) == True{} : Bool}) -> {SD.canon.ds(Bool.and(neg, L.any_d(ds)), ds, D.len(f)) == True{} : Bool}:
  match ds:
    case Nil{}:
      match neg:
        case True{}:
          AL.al.or_false(Nat.is_eq(D.len(f), 0n), hf)
        case False{}:
          AL.al.or_false(Nat.is_eq(D.len(f), 0n), hf)
    case +h <> +t:
      AL.al.and_tt(Nat.is_ne(h, 0n), Bool.and(SD.digits_ok(h <> t), Bool.or(Nat.is_eq(D.len(f), 0n), SD.last_nz(h <> t))), h1, AL.al.and_tt(SD.digits_ok(h <> t), Bool.or(Nat.is_eq(D.len(f), 0n), SD.last_nz(h <> t)), h2, hf))

# the kept digits end in a non-zero digit, or the fraction is gone
def alv.last(+int: List<&2, Nat>, +fs: List<&2, Nat>) -> {Bool.or(Nat.is_eq(D.len(alv.f(fs)), 0n), SD.last_nz(alv.ds(int, fs))) == True{} : Bool}:
  AL.al.or_mono(Nat.is_eq(D.len(alv.f(fs)), 0n), SD.last_nz(alv.f(fs)), SD.last_nz(alv.ds(int, fs)), AL.al.strip_shape(fs), e => AL.al.drop_last(alv.ci(int, fs), AL.al.cat_last(int, alv.f(fs), e)))

def alv.canon_ok(+neg: Bool, +int: List<&2, Nat>, +fs: List<&2, Nat>, hi: {SD.digits_ok(int) == True{} : Bool}, hf: {SD.digits_ok(fs) == True{} : Bool}) -> {SD.canon.ds(Bool.and(neg, L.any_d(alv.ds(int, fs))), alv.ds(int, fs), D.len(alv.f(fs))) == True{} : Bool}:
  alv.canon(alv.ds(int, fs), neg, alv.f(fs), AL.al.drop_headnz(alv.ci(int, fs)), AL.al.drop_digits(alv.ci(int, fs), AL.al.cat_digits(int, alv.f(fs), hi, AL.al.strip_digits(fs, hf))), alv.last(int, fs))
