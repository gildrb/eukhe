# eukhe: lemmas of the proofs of area theme_entry
# Every stage of the entry's decoder (bend/ffi_theme.bend get_*) answers a
# value only for the spelling of that value as Rust writes it
# (spec/theme/wire.bend), within the wire, then whatever follows: each
# primitive by the wire's exactness and fit laws (wire_nat_exact,
# wire_nat_decoded_fits, wire_str_exact, wire_str_decoded_fits,
# wire_u32_exact, wire_bool_exact), each compound stage by its parts
# (tx.*: P(s, d) says a decoded d was spelled in s). No reply opens with
# 'E' (tx.reply_ok).

import Base
import ../../bend/wire.bend as Wr
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/resolve.bend as TResolve
import ../../bend/theme/bundled.bend as TBundled
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/name.bend as TName
import ../../bend/theme/choice.bend as TChoice
import ../../bend/ffi_theme.bend as FTh
import ../../spec/theme/wire.bend as Tw
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../wire/wire_u32_exact.bend as PWireU32Exact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_nat_not_err.bend as PWireNatNotErr

# Logic
# -----

def tx.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# True is not False
def tx.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : tx.BD(_, Unit, G)
  Unit{}

def tx.and(+a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def tx.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def tx.and_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      tx.absurd({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, e))

# Values
# ------

def tx.MNP(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Tw.mnat(m, r) : String} & {Tw.fits.mnat(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.mnat.some(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> tx.MNP(s, FTh.get_mnat.some(d)):
  match d:
    case Wr.Got{+n, +r}:
      +ee = ed
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(n, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(n, r), Wire.wire_nat_exact(s1, n, r, ee))), Wire.wire_nat_decoded_fits(s1, n, r, ee))
    case Wr.Bad{}:
      Unit{}

def tx.mnat(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.MNP(s, FTh.get_mnat(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, ed), {==})
        case 1n:
          tx.mnat.some(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_nat(s1), {==})
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def tx.JP(s: String, d: Wr.Dec<TFile.Json>) -> Type:
  match d:
    case Wr.Got{j, r}:
      {s == Tw.json(j, r) : String} & {Tw.fits.json(j) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.jstr.at(-s: String, +x: String, -s2: String, pre: {s == Wr.put_nat(0n, Wr.put_str(x, s2)) : String}, fx: {Tw.fits.str(x) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Nat>>, mp: tx.MNP(s2, d)) -> tx.JP(s, FTh.get_jstr.at(x, d)):
  match d:
    case Wr.Got{+m, +r}:
      (e, f) = mp
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_str(x, s2)), Wr.put_nat(0n, Wr.put_str(x, Tw.mnat(m, r))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_str(x, z)), s2, Tw.mnat(m, r), e)), tx.and(Tw.fits.str(x), Tw.fits.mnat(m), fx, f))
    case Wr.Bad{}:
      Unit{}

def tx.jstr(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> tx.JP(s, FTh.get_jstr(d)):
  match d:
    case Wr.Got{+x, +s2}:
      +ee = ed
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_str(x, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_str(x, s2), Wire.wire_str_exact(s1, x, s2, ee)))
      tx.jstr.at(s, x, s2, pre2, Wire.wire_str_decoded_fits(s1, x, s2, ee), FTh.get_mnat(Wr.get_nat(s2)), tx.mnat(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.jnum(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> tx.JP(s, FTh.get_jnum(d)):
  match d:
    case Wr.Got{+x, +s2}:
      +ee = ed
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(x, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_str(x, s2), Wire.wire_str_exact(s1, x, s2, ee))), Wire.wire_str_decoded_fits(s1, x, s2, ee))
    case Wr.Bad{}:
      Unit{}

def tx.jother(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> tx.JP(s, FTh.get_jother(d)):
  match d:
    case Wr.Got{+x, +s2}:
      +ee = ed
      (Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_str(x, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_str(x, s2), Wire.wire_str_exact(s1, x, s2, ee))), Wire.wire_str_decoded_fits(s1, x, s2, ee))
    case Wr.Bad{}:
      Unit{}

# a JSON value read was spelled
def tx.json(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.JP(s, FTh.get_json.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          tx.jstr(s, s1, Wire.wire_nat_exact(s, 0n, s1, ed), Wr.get_str(s1), {==})
        case 1n:
          tx.jnum(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_str(s1), {==})
        case 2n:
          tx.jother(s, s1, Wire.wire_nat_exact(s, 2n, s1, ed), Wr.get_str(s1), {==})
        case 3n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# Variables
# ---------

def tx.fvar(v: TFile.Var) -> Bool:
  match v:
    case TFile.Var{n, j}:
      Bool.and(Tw.fits.str(n), Tw.fits.json(j))

def tx.VP(s: String, d: Wr.Dec<TFile.Var>) -> Type:
  match d:
    case Wr.Got{v, r}:
      {s == Tw.var(v, r) : String} & {tx.fvar(v) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.var.val(-s: String, +n: String, -s1: String, pre: {s == Wr.put_str(n, s1) : String}, fn: {Tw.fits.str(n) == True{} : Bool}, d: Wr.Dec<TFile.Json>, jp: tx.JP(s1, d)) -> tx.VP(s, FTh.get_var.val(n, d)):
  match d:
    case Wr.Got{+j, +r}:
      (e, f) = jp
      (Equal.trans(String, s, Wr.put_str(n, s1), Wr.put_str(n, Tw.json(j, r)), pre, Equal.cong(String, String, z => Wr.put_str(n, z), s1, Tw.json(j, r), e)), tx.and(Tw.fits.str(n), Tw.fits.json(j), fn, f))
    case Wr.Bad{}:
      Unit{}

def tx.var.go(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> tx.VP(s, FTh.get_var.go(d)):
  match d:
    case Wr.Got{+n, +s1}:
      +ee = ed
      tx.var.val(s, n, s1, Wire.wire_str_exact(s, n, s1, ee), Wire.wire_str_decoded_fits(s, n, s1, ee), FTh.get_json.go(Wr.get_nat(s1)), tx.json(s1, Wr.get_nat(s1), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.var(+s: String) -> tx.VP(s, FTh.get_var(s)):
  tx.var.go(s, Wr.get_str(s), {==})

# the variables read after a count of 1 + n
def tx.VGP(s: String, n: Nat, d: Wr.Dec<List<&2, TFile.Var>>) -> Type:
  match d:
    case Wr.Got{vs, r}:
      {s == Tw.vars.items(vs, r) : String} & ({Tw.fits.vars(vs) == True{} : Bool} & {List.length(&2, TFile.Var, vs) == 1n+n : Nat})
    case Wr.Bad{}:
      Unit

def tx.VSP(s: String, d: Wr.Dec<List<&2, TFile.Var>>) -> Type:
  match d:
    case Wr.Got{vs, r}:
      {s == Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, r)) : String} & ({LawsBase.wire_fits(List.length(&2, TFile.Var, vs)) == True{} : Bool} & {Tw.fits.vars(vs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def tx.vars.cons(d: Wr.Dec<List<&2, TFile.Var>>, v: TFile.Var, -s: String, -s1: String, pre: {s == Tw.var(v, s1) : String}, fv: {tx.fvar(v) == True{} : Bool}, +m: Nat, gp: tx.VGP(s1, m, d)) -> tx.VGP(s, 1n+m, FTh.get_vars.cons(v, d)):
  match d:
    case Wr.Got{+vs, +r}:
      match v:
        case TFile.Var{+nm, +j}:
          (e, fl) = gp
          (f, l) = fl
          +fv0 = fv
          (Equal.trans(String, s, Tw.var(TFile.Var{nm, j}, s1), Tw.var(TFile.Var{nm, j}, Tw.vars.items(vs, r)), pre, Equal.cong(String, String, z => Tw.var(TFile.Var{nm, j}, z), s1, Tw.vars.items(vs, r), e)),
            (tx.and(Tw.fits.str(nm), Bool.and(Tw.fits.json(j), Tw.fits.vars(vs)), tx.and_l(Tw.fits.str(nm), Tw.fits.json(j), fv0), tx.and(Tw.fits.json(j), Tw.fits.vars(vs), tx.and_r(Tw.fits.str(nm), Tw.fits.json(j), fv0), f)),
             Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, TFile.Var, vs), 1n+m, l)))
    case Wr.Bad{}:
      Unit{}

def tx.vars.one(v: TFile.Var, fv: {tx.fvar(v) == True{} : Bool}) -> {Tw.fits.vars([v]) == True{} : Bool}:
  match v:
    case TFile.Var{+nm, +j}:
      +fv0 = fv
      tx.and(Tw.fits.str(nm), Bool.and(Tw.fits.json(j), True{}), tx.and_l(Tw.fits.str(nm), Tw.fits.json(j), fv0), tx.and(Tw.fits.json(j), True{}, tx.and_r(Tw.fits.str(nm), Tw.fits.json(j), fv0), {==}))

def tx.vars.go(m: Nat, +s: String, d: Wr.Dec<TFile.Var>, vp: tx.VP(s, d)) -> tx.VGP(s, m, FTh.get_vars.go(m, d)):
  match m:
    case 0n:
      match d:
        case Wr.Got{+v, +r}:
          (e, f) = vp
          (e, (tx.vars.one(v, f), {==}))
        case Wr.Bad{}:
          Unit{}
    case 1n++p:
      match d:
        case Wr.Got{+v, +r}:
          (e, f) = vp
          tx.vars.cons(FTh.get_vars.go(p, FTh.get_var(r)), v, s, r, e, f, p, tx.vars.go(p, r, FTh.get_var(r), tx.var(r)))
        case Wr.Bad{}:
          Unit{}

def tx.vars.top(d: Wr.Dec<List<&2, TFile.Var>>, -s: String, -s1: String, +m: Nat, pre: {s == Wr.put_nat(1n+m, s1) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, gp: tx.VGP(s1, m, d)) -> tx.VSP(s, d):
  match d:
    case Wr.Got{+vs, +r}:
      (e, fl) = gp
      (f, l) = fl
      %Equal.sym(Nat, List.length(&2, TFile.Var, vs), 1n+m, l) : {s == Wr.put_nat(_, Tw.vars.items(vs, r)) : String} & ({LawsBase.wire_fits(_) == True{} : Bool} & {Tw.fits.vars(vs) == True{} : Bool})
      (Equal.trans(String, s, Wr.put_nat(1n+m, s1), Wr.put_nat(1n+m, Tw.vars.items(vs, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n+m, z), s1, Tw.vars.items(vs, r), e)), (fn, f))
    case Wr.Bad{}:
      Unit{}

# a count and the variables read were spelled
def tx.vars(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.VSP(s, FTh.get_vars(d)):
  match d:
    case Wr.Got{+n, +s1}:
      match n:
        case 0n:
          +ee = ed
          (Wire.wire_nat_exact(s, 0n, s1, ee), (Wire.wire_nat_decoded_fits(s, 0n, s1, ee), {==}))
        case 1n++m:
          +ee = ed
          tx.vars.top(FTh.get_vars.go(m, FTh.get_var(s1)), s, s1, m, Wire.wire_nat_exact(s, 1n+m, s1, ee), Wire.wire_nat_decoded_fits(s, 1n+m, s1, ee), tx.vars.go(m, s1, FTh.get_var(s1), tx.var(s1)))
    case Wr.Bad{}:
      Unit{}

# Colors
# ------

def tx.MUP(s: String, d: Wr.Dec<Maybe<&2, U32>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Tw.mu32(m, r) : String}
    case Wr.Bad{}:
      Unit

def tx.mu32.some(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<U32>, ed: {Wr.get_u32(s1) == d : Wr.Dec<U32>}) -> tx.MUP(s, FTh.get_mu32.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_u32(x, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_u32(x, r), Wire.wire_u32_exact(s1, x, r, ed)))
    case Wr.Bad{}:
      Unit{}

def tx.mu32(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.MUP(s, FTh.get_mu32(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s1, ed)
        case 1n:
          tx.mu32.some(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_u32(s1), {==})
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def tx.fcol(e: TFile.REnt) -> Bool:
  match e:
    case TFile.REnt{k, x, j}:
      Bool.and(Tw.fits.str(k), Tw.fits.json(j))

def tx.CP(s: String, d: Wr.Dec<TFile.REnt>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == Tw.col(e, r) : String} & {tx.fcol(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.col.val(-s: String, +k: String, +t: Maybe<&2, U32>, -s2: String, pre: {s == Wr.put_str(k, Tw.mu32(t, s2)) : String}, fk: {Tw.fits.str(k) == True{} : Bool}, d: Wr.Dec<TFile.Json>, jp: tx.JP(s2, d)) -> tx.CP(s, FTh.get_col.val(k, t, d)):
  match d:
    case Wr.Got{+j, +r}:
      (e, f) = jp
      (Equal.trans(String, s, Wr.put_str(k, Tw.mu32(t, s2)), Wr.put_str(k, Tw.mu32(t, Tw.json(j, r))), pre, Equal.cong(String, String, z => Wr.put_str(k, Tw.mu32(t, z)), s2, Tw.json(j, r), e)), tx.and(Tw.fits.str(k), Tw.fits.json(j), fk, f))
    case Wr.Bad{}:
      Unit{}

def tx.col.tok(-s: String, +k: String, -s1: String, pre: {s == Wr.put_str(k, s1) : String}, fk: {Tw.fits.str(k) == True{} : Bool}, d: Wr.Dec<Maybe<&2, U32>>, mp: tx.MUP(s1, d)) -> tx.CP(s, FTh.get_col.tok(k, d)):
  match d:
    case Wr.Got{+t, +s2}:
      tx.col.val(s, k, t, s2, Equal.trans(String, s, Wr.put_str(k, s1), Wr.put_str(k, Tw.mu32(t, s2)), pre, Equal.cong(String, String, z => Wr.put_str(k, z), s1, Tw.mu32(t, s2), mp)), fk, FTh.get_json.go(Wr.get_nat(s2)), tx.json(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.col.go(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> tx.CP(s, FTh.get_col.go(d)):
  match d:
    case Wr.Got{+k, +s1}:
      +ee = ed
      tx.col.tok(s, k, s1, Wire.wire_str_exact(s, k, s1, ee), Wire.wire_str_decoded_fits(s, k, s1, ee), FTh.get_mu32(Wr.get_nat(s1)), tx.mu32(s1, Wr.get_nat(s1), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.col(+s: String) -> tx.CP(s, FTh.get_col(s)):
  tx.col.go(s, Wr.get_str(s), {==})

def tx.CGP(s: String, n: Nat, d: Wr.Dec<List<&2, TFile.REnt>>) -> Type:
  match d:
    case Wr.Got{es, r}:
      {s == Tw.cols.items(es, r) : String} & ({Tw.fits.cols(es) == True{} : Bool} & {List.length(&2, TFile.REnt, es) == 1n+n : Nat})
    case Wr.Bad{}:
      Unit

def tx.CSP(s: String, d: Wr.Dec<List<&2, TFile.REnt>>) -> Type:
  match d:
    case Wr.Got{es, r}:
      {s == Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, r)) : String} & ({LawsBase.wire_fits(List.length(&2, TFile.REnt, es)) == True{} : Bool} & {Tw.fits.cols(es) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def tx.cols.cons(d: Wr.Dec<List<&2, TFile.REnt>>, c: TFile.REnt, -s: String, -s1: String, pre: {s == Tw.col(c, s1) : String}, fc: {tx.fcol(c) == True{} : Bool}, +m: Nat, gp: tx.CGP(s1, m, d)) -> tx.CGP(s, 1n+m, FTh.get_cols.cons(c, d)):
  match d:
    case Wr.Got{+es, +r}:
      match c:
        case TFile.REnt{+k, +x, +j}:
          (e, fl) = gp
          (f, l) = fl
          +fc0 = fc
          (Equal.trans(String, s, Tw.col(TFile.REnt{k, x, j}, s1), Tw.col(TFile.REnt{k, x, j}, Tw.cols.items(es, r)), pre, Equal.cong(String, String, z => Tw.col(TFile.REnt{k, x, j}, z), s1, Tw.cols.items(es, r), e)),
            (tx.and(Tw.fits.str(k), Bool.and(Tw.fits.json(j), Tw.fits.cols(es)), tx.and_l(Tw.fits.str(k), Tw.fits.json(j), fc0), tx.and(Tw.fits.json(j), Tw.fits.cols(es), tx.and_r(Tw.fits.str(k), Tw.fits.json(j), fc0), f)),
             Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, TFile.REnt, es), 1n+m, l)))
    case Wr.Bad{}:
      Unit{}

def tx.cols.one(c: TFile.REnt, fc: {tx.fcol(c) == True{} : Bool}) -> {Tw.fits.cols([c]) == True{} : Bool}:
  match c:
    case TFile.REnt{+k, +x, +j}:
      +fc0 = fc
      tx.and(Tw.fits.str(k), Bool.and(Tw.fits.json(j), True{}), tx.and_l(Tw.fits.str(k), Tw.fits.json(j), fc0), tx.and(Tw.fits.json(j), True{}, tx.and_r(Tw.fits.str(k), Tw.fits.json(j), fc0), {==}))

def tx.cols.go(m: Nat, +s: String, d: Wr.Dec<TFile.REnt>, cp: tx.CP(s, d)) -> tx.CGP(s, m, FTh.get_cols.go(m, d)):
  match m:
    case 0n:
      match d:
        case Wr.Got{+c, +r}:
          (e, f) = cp
          (e, (tx.cols.one(c, f), {==}))
        case Wr.Bad{}:
          Unit{}
    case 1n++p:
      match d:
        case Wr.Got{+c, +r}:
          (e, f) = cp
          tx.cols.cons(FTh.get_cols.go(p, FTh.get_col(r)), c, s, r, e, f, p, tx.cols.go(p, r, FTh.get_col(r), tx.col(r)))
        case Wr.Bad{}:
          Unit{}

def tx.cols.top(d: Wr.Dec<List<&2, TFile.REnt>>, -s: String, -s1: String, +m: Nat, pre: {s == Wr.put_nat(1n+m, s1) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, gp: tx.CGP(s1, m, d)) -> tx.CSP(s, d):
  match d:
    case Wr.Got{+es, +r}:
      (e, fl) = gp
      (f, l) = fl
      %Equal.sym(Nat, List.length(&2, TFile.REnt, es), 1n+m, l) : {s == Wr.put_nat(_, Tw.cols.items(es, r)) : String} & ({LawsBase.wire_fits(_) == True{} : Bool} & {Tw.fits.cols(es) == True{} : Bool})
      (Equal.trans(String, s, Wr.put_nat(1n+m, s1), Wr.put_nat(1n+m, Tw.cols.items(es, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n+m, z), s1, Tw.cols.items(es, r), e)), (fn, f))
    case Wr.Bad{}:
      Unit{}

# a count and the colors read were spelled
def tx.cols(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.CSP(s, FTh.get_cols(d)):
  match d:
    case Wr.Got{+n, +s1}:
      match n:
        case 0n:
          +ee = ed
          (Wire.wire_nat_exact(s, 0n, s1, ee), (Wire.wire_nat_decoded_fits(s, 0n, s1, ee), {==}))
        case 1n++m:
          +ee = ed
          tx.cols.top(FTh.get_cols.go(m, FTh.get_col(s1)), s, s1, m, Wire.wire_nat_exact(s, 1n+m, s1, ee), Wire.wire_nat_decoded_fits(s, 1n+m, s1, ee), tx.cols.go(m, s1, FTh.get_col(s1), tx.col(s1)))
    case Wr.Bad{}:
      Unit{}

# Files
# -----

def tx.MJP(s: String, d: Wr.Dec<Maybe<&2, TFile.Json>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Tw.mjson(m, r) : String} & {Tw.fits.mjson(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.mjson.some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<TFile.Json>, jp: tx.JP(s1, d)) -> tx.MJP(s, FTh.get_mjson.some(d)):
  match d:
    case Wr.Got{+j, +r}:
      (e, f) = jp
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Tw.json(j, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Tw.json(j, r), e)), f)
    case Wr.Bad{}:
      Unit{}

def tx.mjson(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.MJP(s, FTh.get_mjson(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, ed), {==})
        case 1n:
          tx.mjson.some(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), FTh.get_json.go(Wr.get_nat(s1)), tx.json(s1, Wr.get_nat(s1), {==}))
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def tx.FP(s: String, d: Wr.Dec<TFile.RFile>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == Tw.file(f, r) : String} & {Tw.fits.file(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.file.info(d: Wr.Dec<Maybe<&2, TFile.Json>>, -s: String, +nm: String, +vs: List<&2, TFile.Var>, +es: List<&2, TFile.REnt>, +pg: Maybe<&2, TFile.Json>, +cd: Maybe<&2, TFile.Json>, -s5: String,
  pre: {s == Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, Tw.mjson(pg, Tw.mjson(cd, s5))))))) : String},
  fnm: {Tw.fits.str(nm) == True{} : Bool}, flv: {LawsBase.wire_fits(List.length(&2, TFile.Var, vs)) == True{} : Bool}, fvs: {Tw.fits.vars(vs) == True{} : Bool}, fle: {LawsBase.wire_fits(List.length(&2, TFile.REnt, es)) == True{} : Bool}, fes: {Tw.fits.cols(es) == True{} : Bool}, fpg: {Tw.fits.mjson(pg) == True{} : Bool}, fcd: {Tw.fits.mjson(cd) == True{} : Bool},
  mp: tx.MJP(s5, d)) -> tx.FP(s, FTh.get_file.info(nm, vs, es, pg, cd, d)):
  match d:
    case Wr.Got{+io, +r}:
      (e, fio) = mp
      (Equal.trans(String, s, Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, Tw.mjson(pg, Tw.mjson(cd, s5))))))), Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, Tw.mjson(pg, Tw.mjson(cd, Tw.mjson(io, r)))))))), pre,
         Equal.cong(String, String, z => Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, Tw.mjson(pg, Tw.mjson(cd, z))))))), s5, Tw.mjson(io, r), e)),
       tx.and(Tw.fits.str(nm), Bool.and(LawsBase.wire_fits(List.length(&2, TFile.Var, vs)), Bool.and(Tw.fits.vars(vs), Bool.and(LawsBase.wire_fits(List.length(&2, TFile.REnt, es)), Bool.and(Tw.fits.cols(es), Bool.and(Tw.fits.mjson(pg), Bool.and(Tw.fits.mjson(cd), Tw.fits.mjson(io))))))), fnm,
         tx.and(LawsBase.wire_fits(List.length(&2, TFile.Var, vs)), Bool.and(Tw.fits.vars(vs), Bool.and(LawsBase.wire_fits(List.length(&2, TFile.REnt, es)), Bool.and(Tw.fits.cols(es), Bool.and(Tw.fits.mjson(pg), Bool.and(Tw.fits.mjson(cd), Tw.fits.mjson(io)))))), flv,
           tx.and(Tw.fits.vars(vs), Bool.and(LawsBase.wire_fits(List.length(&2, TFile.REnt, es)), Bool.and(Tw.fits.cols(es), Bool.and(Tw.fits.mjson(pg), Bool.and(Tw.fits.mjson(cd), Tw.fits.mjson(io))))), fvs,
             tx.and(LawsBase.wire_fits(List.length(&2, TFile.REnt, es)), Bool.and(Tw.fits.cols(es), Bool.and(Tw.fits.mjson(pg), Bool.and(Tw.fits.mjson(cd), Tw.fits.mjson(io)))), fle,
               tx.and(Tw.fits.cols(es), Bool.and(Tw.fits.mjson(pg), Bool.and(Tw.fits.mjson(cd), Tw.fits.mjson(io))), fes,
                 tx.and(Tw.fits.mjson(pg), Bool.and(Tw.fits.mjson(cd), Tw.fits.mjson(io)), fpg,
                   tx.and(Tw.fits.mjson(cd), Tw.fits.mjson(io), fcd, fio))))))))
    case Wr.Bad{}:
      Unit{}

def tx.file.card(d: Wr.Dec<Maybe<&2, TFile.Json>>, -s: String, +nm: String, +vs: List<&2, TFile.Var>, +es: List<&2, TFile.REnt>, +pg: Maybe<&2, TFile.Json>, -s4: String,
  pre: {s == Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, Tw.mjson(pg, s4)))))) : String},
  fnm: {Tw.fits.str(nm) == True{} : Bool}, flv: {LawsBase.wire_fits(List.length(&2, TFile.Var, vs)) == True{} : Bool}, fvs: {Tw.fits.vars(vs) == True{} : Bool}, fle: {LawsBase.wire_fits(List.length(&2, TFile.REnt, es)) == True{} : Bool}, fes: {Tw.fits.cols(es) == True{} : Bool}, fpg: {Tw.fits.mjson(pg) == True{} : Bool},
  mp: tx.MJP(s4, d)) -> tx.FP(s, FTh.get_file.card(nm, vs, es, pg, d)):
  match d:
    case Wr.Got{+cd, +s5}:
      (e, fcd) = mp
      +pre2 = Equal.trans(String, s, Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, Tw.mjson(pg, s4)))))), Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, Tw.mjson(pg, Tw.mjson(cd, s5))))))), pre,
        Equal.cong(String, String, z => Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, Tw.mjson(pg, z)))))), s4, Tw.mjson(cd, s5), e))
      tx.file.info(FTh.get_mjson(Wr.get_nat(s5)), s, nm, vs, es, pg, cd, s5, pre2, fnm, flv, fvs, fle, fes, fpg, fcd, tx.mjson(s5, Wr.get_nat(s5), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.file.page(d: Wr.Dec<Maybe<&2, TFile.Json>>, -s: String, +nm: String, +vs: List<&2, TFile.Var>, +es: List<&2, TFile.REnt>, -s3: String,
  pre: {s == Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, s3))))) : String},
  fnm: {Tw.fits.str(nm) == True{} : Bool}, flv: {LawsBase.wire_fits(List.length(&2, TFile.Var, vs)) == True{} : Bool}, fvs: {Tw.fits.vars(vs) == True{} : Bool}, fle: {LawsBase.wire_fits(List.length(&2, TFile.REnt, es)) == True{} : Bool}, fes: {Tw.fits.cols(es) == True{} : Bool},
  mp: tx.MJP(s3, d)) -> tx.FP(s, FTh.get_file.page(nm, vs, es, d)):
  match d:
    case Wr.Got{+pg, +s4}:
      (e, fpg) = mp
      +pre2 = Equal.trans(String, s, Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, s3))))), Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, Tw.mjson(pg, s4)))))), pre,
        Equal.cong(String, String, z => Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, z))))), s3, Tw.mjson(pg, s4), e))
      tx.file.card(FTh.get_mjson(Wr.get_nat(s4)), s, nm, vs, es, pg, s4, pre2, fnm, flv, fvs, fle, fes, fpg, tx.mjson(s4, Wr.get_nat(s4), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.file.cols(d: Wr.Dec<List<&2, TFile.REnt>>, -s: String, +nm: String, +vs: List<&2, TFile.Var>, -s2: String,
  pre: {s == Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, s2))) : String},
  fnm: {Tw.fits.str(nm) == True{} : Bool}, flv: {LawsBase.wire_fits(List.length(&2, TFile.Var, vs)) == True{} : Bool}, fvs: {Tw.fits.vars(vs) == True{} : Bool},
  cp: tx.CSP(s2, d)) -> tx.FP(s, FTh.get_file.cols(nm, vs, d)):
  match d:
    case Wr.Got{+es, +s3}:
      (e, fl) = cp
      (fle, fes) = fl
      +pre2 = Equal.trans(String, s, Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, s2))), Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, s3))))), pre,
        Equal.cong(String, String, z => Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, z))), s2, Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, s3)), e))
      tx.file.page(FTh.get_mjson(Wr.get_nat(s3)), s, nm, vs, es, s3, pre2, fnm, flv, fvs, fle, fes, tx.mjson(s3, Wr.get_nat(s3), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.file.vars(d: Wr.Dec<List<&2, TFile.Var>>, -s: String, +nm: String, -s1: String, pre: {s == Wr.put_str(nm, s1) : String}, fnm: {Tw.fits.str(nm) == True{} : Bool}, vp: tx.VSP(s1, d)) -> tx.FP(s, FTh.get_file.vars(nm, d)):
  match d:
    case Wr.Got{+vs, +s2}:
      (e, fl) = vp
      (flv, fvs) = fl
      +pre2 = Equal.trans(String, s, Wr.put_str(nm, s1), Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, s2))), pre, Equal.cong(String, String, z => Wr.put_str(nm, z), s1, Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, s2)), e))
      tx.file.cols(FTh.get_cols(Wr.get_nat(s2)), s, nm, vs, s2, pre2, fnm, flv, fvs, tx.cols(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

# a theme file read was spelled
def tx.file(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> tx.FP(s, FTh.get_file(d)):
  match d:
    case Wr.Got{+nm, +s1}:
      +ee = ed
      tx.file.vars(FTh.get_vars(Wr.get_nat(s1)), s, nm, s1, Wire.wire_str_exact(s, nm, s1, ee), Wire.wire_str_decoded_fits(s, nm, s1, ee), tx.vars(s1, Wr.get_nat(s1), {==}))
    case Wr.Bad{}:
      Unit{}

# Sources
# -------

def tx.fmstr(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Tw.fits.str(x)

def tx.MSP(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Tw.mstr(m, r) : String} & {tx.fmstr(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.mstr.some(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> tx.MSP(s, FTh.get_mstr.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      +ee = ed
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(x, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_str(x, r), Wire.wire_str_exact(s1, x, r, ee))), Wire.wire_str_decoded_fits(s1, x, r, ee))
    case Wr.Bad{}:
      Unit{}

def tx.mstr(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.MSP(s, FTh.get_mstr(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, ed), {==})
        case 1n:
          tx.mstr.some(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_str(s1), {==})
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def tx.fmfile(m: Maybe<&2, TFile.RFile>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{f}:
      Tw.fits.file(f)

def tx.MFP(s: String, d: Wr.Dec<Maybe<&2, TFile.RFile>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Tw.mfile(m, r) : String} & {tx.fmfile(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.mfile.some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<TFile.RFile>, fp: tx.FP(s1, d)) -> tx.MFP(s, FTh.get_mfile.some(d)):
  match d:
    case Wr.Got{+f, +r}:
      (e, ff) = fp
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Tw.file(f, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Tw.file(f, r), e)), ff)
    case Wr.Bad{}:
      Unit{}

def tx.mfile(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.MFP(s, FTh.get_mfile(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, ed), {==})
        case 1n:
          tx.mfile.some(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), FTh.get_file(Wr.get_str(s1)), tx.file(s1, Wr.get_str(s1), {==}))
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def tx.fsrc(st: Maybe<&2, String>, b: Maybe<&2, TFile.RFile>, -c: Bool, hs: {tx.fmstr(st) == True{} : Bool}, hb: {tx.fmfile(b) == True{} : Bool}) -> {Tw.fits.src(TResolve.Src{c, st, b}) == True{} : Bool}:
  match st:
    case None{}:
      match b:
        case None{}:
          {==}
        case Some{f}:
          hb
    case Some{+x}:
      match b:
        case None{}:
          hs
        case Some{+f}:
          tx.and(Tw.fits.str(x), Tw.fits.file(f), hs, hb)

def tx.SP(s: String, d: Wr.Dec<TResolve.Src>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Tw.src(x, r) : String} & {Tw.fits.src(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.src.body(d: Wr.Dec<Maybe<&2, TFile.RFile>>, -s: String, +c: Bool, +st: Maybe<&2, String>, -s2: String, pre: {s == Wr.put_bool(c, Tw.mstr(st, s2)) : String}, fs: {tx.fmstr(st) == True{} : Bool}, mp: tx.MFP(s2, d)) -> tx.SP(s, FTh.get_src.body(c, st, d)):
  match d:
    case Wr.Got{+b, +r}:
      (e, fb) = mp
      (Equal.trans(String, s, Wr.put_bool(c, Tw.mstr(st, s2)), Wr.put_bool(c, Tw.mstr(st, Tw.mfile(b, r))), pre, Equal.cong(String, String, z => Wr.put_bool(c, Tw.mstr(st, z)), s2, Tw.mfile(b, r), e)), tx.fsrc(st, b, c, fs, fb))
    case Wr.Bad{}:
      Unit{}

def tx.src.stem(d: Wr.Dec<Maybe<&2, String>>, -s: String, +c: Bool, -s1: String, pre: {s == Wr.put_bool(c, s1) : String}, mp: tx.MSP(s1, d)) -> tx.SP(s, FTh.get_src.stem(c, d)):
  match d:
    case Wr.Got{+st, +s2}:
      (e, fs) = mp
      tx.src.body(FTh.get_mfile(Wr.get_nat(s2)), s, c, st, s2, Equal.trans(String, s, Wr.put_bool(c, s1), Wr.put_bool(c, Tw.mstr(st, s2)), pre, Equal.cong(String, String, z => Wr.put_bool(c, z), s1, Tw.mstr(st, s2), e)), fs, tx.mfile(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.src.go(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> tx.SP(s, FTh.get_src.go(d)):
  match d:
    case Wr.Got{+c, +s1}:
      tx.src.stem(FTh.get_mstr(Wr.get_nat(s1)), s, c, s1, Wire.wire_bool_exact(s, c, s1, ed), tx.mstr(s1, Wr.get_nat(s1), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.src(+s: String) -> tx.SP(s, FTh.get_src(s)):
  tx.src.go(s, Wr.get_bool(s), {==})

def tx.SGP(s: String, n: Nat, d: Wr.Dec<List<&2, TResolve.Src>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Tw.srcs.items(xs, r) : String} & ({Tw.fits.srcs(xs) == True{} : Bool} & {List.length(&2, TResolve.Src, xs) == 1n+n : Nat})
    case Wr.Bad{}:
      Unit

def tx.SSP(s: String, d: Wr.Dec<List<&2, TResolve.Src>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_nat(List.length(&2, TResolve.Src, xs), Tw.srcs.items(xs, r)) : String} & ({LawsBase.wire_fits(List.length(&2, TResolve.Src, xs)) == True{} : Bool} & {Tw.fits.srcs(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def tx.srcs.cons(d: Wr.Dec<List<&2, TResolve.Src>>, +x: TResolve.Src, -s: String, -s1: String, pre: {s == Tw.src(x, s1) : String}, fx: {Tw.fits.src(x) == True{} : Bool}, +m: Nat, gp: tx.SGP(s1, m, d)) -> tx.SGP(s, 1n+m, FTh.get_srcs.cons(x, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e, fl) = gp
      (f, l) = fl
      (Equal.trans(String, s, Tw.src(x, s1), Tw.src(x, Tw.srcs.items(xs, r)), pre, Equal.cong(String, String, z => Tw.src(x, z), s1, Tw.srcs.items(xs, r), e)),
        (tx.and(Tw.fits.src(x), Tw.fits.srcs(xs), fx, f), Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, TResolve.Src, xs), 1n+m, l)))
    case Wr.Bad{}:
      Unit{}

def tx.srcs.go(m: Nat, +s: String, d: Wr.Dec<TResolve.Src>, sp: tx.SP(s, d)) -> tx.SGP(s, m, FTh.get_srcs.go(m, d)):
  match m:
    case 0n:
      match d:
        case Wr.Got{+x, +r}:
          (e, f) = sp
          (e, (tx.and(Tw.fits.src(x), True{}, f, {==}), {==}))
        case Wr.Bad{}:
          Unit{}
    case 1n++p:
      match d:
        case Wr.Got{+x, +r}:
          (e, f) = sp
          tx.srcs.cons(FTh.get_srcs.go(p, FTh.get_src(r)), x, s, r, e, f, p, tx.srcs.go(p, r, FTh.get_src(r), tx.src(r)))
        case Wr.Bad{}:
          Unit{}

def tx.srcs.top(d: Wr.Dec<List<&2, TResolve.Src>>, -s: String, -s1: String, +m: Nat, pre: {s == Wr.put_nat(1n+m, s1) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, gp: tx.SGP(s1, m, d)) -> tx.SSP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e, fl) = gp
      (f, l) = fl
      %Equal.sym(Nat, List.length(&2, TResolve.Src, xs), 1n+m, l) : {s == Wr.put_nat(_, Tw.srcs.items(xs, r)) : String} & ({LawsBase.wire_fits(_) == True{} : Bool} & {Tw.fits.srcs(xs) == True{} : Bool})
      (Equal.trans(String, s, Wr.put_nat(1n+m, s1), Wr.put_nat(1n+m, Tw.srcs.items(xs, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n+m, z), s1, Tw.srcs.items(xs, r), e)), (fn, f))
    case Wr.Bad{}:
      Unit{}

# a count and the sources read were spelled
def tx.srcs(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.SSP(s, FTh.get_srcs(d)):
  match d:
    case Wr.Got{+n, +s1}:
      match n:
        case 0n:
          +ee = ed
          (Wire.wire_nat_exact(s, 0n, s1, ee), (Wire.wire_nat_decoded_fits(s, 0n, s1, ee), {==}))
        case 1n++m:
          +ee = ed
          tx.srcs.top(FTh.get_srcs.go(m, FTh.get_src(s1)), s, s1, m, Wire.wire_nat_exact(s, 1n+m, s1, ee), Wire.wire_nat_decoded_fits(s, 1n+m, s1, ee), tx.srcs.go(m, s1, FTh.get_src(s1), tx.src(s1)))
    case Wr.Bad{}:
      Unit{}

# Requests
# --------

def tx.RQP(s: String, d: Wr.Dec<FTh.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Tw.req(q, r) : String} & {Tw.fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.load(d: Wr.Dec<TFile.RFile>, -s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, fp: tx.FP(s1, d)) -> tx.RQP(s, FTh.get_load(d)):
  match d:
    case Wr.Got{+f, +r}:
      (e, ff) = fp
      (Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Tw.file(f, r)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Tw.file(f, r), e)), ff)
    case Wr.Bad{}:
      Unit{}

def tx.resolve.files(d: Wr.Dec<List<&2, TResolve.Src>>, -s: String, +n: String, -s2: String, pre: {s == Wr.put_nat(1n, Wr.put_str(n, s2)) : String}, fn: {Tw.fits.str(n) == True{} : Bool}, sp: tx.SSP(s2, d)) -> tx.RQP(s, FTh.get_resolve.files(n, d)):
  match d:
    case Wr.Got{+ss, +r}:
      (e, fl) = sp
      (fln, fss) = fl
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_str(n, s2)), Wr.put_nat(1n, Wr.put_str(n, Wr.put_nat(List.length(&2, TResolve.Src, ss), Tw.srcs.items(ss, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_str(n, z)), s2, Wr.put_nat(List.length(&2, TResolve.Src, ss), Tw.srcs.items(ss, r)), e)),
        tx.and(Tw.fits.str(n), Bool.and(LawsBase.wire_fits(List.length(&2, TResolve.Src, ss)), Tw.fits.srcs(ss)), fn, tx.and(LawsBase.wire_fits(List.length(&2, TResolve.Src, ss)), Tw.fits.srcs(ss), fln, fss)))
    case Wr.Bad{}:
      Unit{}

def tx.resolve(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> tx.RQP(s, FTh.get_resolve(d)):
  match d:
    case Wr.Got{+n, +s2}:
      +ee = ed
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(n, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_str(n, s2), Wire.wire_str_exact(s1, n, s2, ee)))
      tx.resolve.files(FTh.get_srcs(Wr.get_nat(s2)), s, n, s2, pre2, Wire.wire_str_decoded_fits(s1, n, s2, ee), tx.srcs(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.shipped(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> tx.RQP(s, FTh.get_shipped(d)):
  match d:
    case Wr.Got{+t, +r}:
      match t:
        case 0n:
          (Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_nat(0n, r)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_nat(0n, r), Wire.wire_nat_exact(s1, 0n, r, ed))), {==})
        case 1n:
          (Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_nat(1n, r)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_nat(1n, r), Wire.wire_nat_exact(s1, 1n, r, ed))), {==})
        case 2n:
          (Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_nat(2n, r)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_nat(2n, r), Wire.wire_nat_exact(s1, 2n, r, ed))), {==})
        case 3n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a request read was spelled, every text, count and index within the wire
def tx.req(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.RQP(s, FTh.get_req.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          tx.load(FTh.get_file(Wr.get_str(s1)), s, s1, Wire.wire_nat_exact(s, 0n, s1, ed), tx.file(s1, Wr.get_str(s1), {==}))
        case 1n:
          tx.resolve(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_str(s1), {==})
        case 2n:
          tx.shipped(s, s1, Wire.wire_nat_exact(s, 2n, s1, ed), Wr.get_nat(s1), {==})
        case 3n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# Replies
# -------

def tx.parsed_ok(p: TPalette.Parsed) -> {LawsBase.wire_opens_err(FTh.put_parsed(p, "")) == False{} : Bool}:
  match p:
    case TPalette.Rejected{f}:
      {==}
    case TPalette.Painted{vs, l, d, pg, cd, io}:
      {==}

def tx.resolved_ok(r: TResolve.Resolved) -> {LawsBase.wire_opens_err(FTh.put_resolved(r)) == False{} : Bool}:
  match r:
    case TResolve.Resolved{res, c, +k, +b, +os, p}:
      match res:
        case TName.Res{+id, w}:
          Wire.wire_nat_not_err(U32.to_nat(id), Wr.put_bool(w, FTh.put_mcause(c, Wr.put_nat(List.length(&2, TChoice.Clash, k), FTh.put_clashes.items(k, Wr.put_nat(List.length(&2, Nat, b), FTh.put_nats.items(b, Wr.put_nat(List.length(&2, TResolve.Out, os), FTh.put_outs.items(os, FTh.put_mparsed(p, ""))))))))))

# no reply opens with 'E'
def tx.reply_ok(q: FTh.Req) -> {LawsBase.wire_opens_err(FTh.reply(q)) == False{} : Bool}:
  match q:
    case FTh.Load{f}:
      tx.parsed_ok(TPalette.parse(f))
    case FTh.Resolve{n, fs}:
      tx.resolved_ok(TResolve.resolve(n, fs))
    case FTh.Shipped{+s}:
      Wire.wire_nat_not_err(List.length(&2, Co.Rgb, TBundled.table(s)), FTh.put_rgbs.items(TBundled.table(s), ""))
