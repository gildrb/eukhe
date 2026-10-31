# eukhe: lemmas of the entry proofs of area arg_repair: a decoded request
# is spelled (rd.*: a predicate per decoder answer, carried stage by stage
# with the wire exactness lemmas dcw.nat, dcw.str and wire_bool_exact),
# and every length it holds fits the wire

import Base
import ../../../bend/arg_repair.bend as Ar
import ../../../bend/ffi_arg_repair.bend as FAr
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/arg_repair.bend as ArgRepair
import ../../base/wire_dec.bend as LE
import ../../base/staging.bend as LStg
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ./step.bend as SV

# Maybe<String>
# -------------

def rd.MS(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == ArgRepair.ar_w_ms(m, r) : String} & {ArgRepair.ar_fit_ms(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rd.ms_some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rd.MS(s, FAr.get_ms.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fit) = sp
      (LE.dcw.after(s, 1n, s1, Wr.put_str(x, r), pre, e), fit)
    case Wr.Bad{}:
      Unit{}

def rd.ms_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rd.MS(s, FAr.get_ms.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (np, {==})
        case 1n:
          rd.ms_some(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a Maybe<String> decoded is spelled, and fits
def rd.ms(+s: String) -> rd.MS(s, FAr.get_ms(s)):
  rd.ms_at(s, Wr.get_nat(s), LE.dcw.nat(s))

# Declared arguments
# ------------------

def rd.PP(s: String, d: Wr.Dec<Ar.Prop>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == ArgRepair.ar_w_prop(p, r) : String} & {ArgRepair.ar_fit_prop(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rd.prop_items(-s: String, +n: String, +k: Maybe<&2, String>, -s2: String, pre: {s == Wr.put_str(n, ArgRepair.ar_w_ms(k, s2)) : String}, fn: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}, fk: {ArgRepair.ar_fit_ms(k) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, mp: rd.MS(s2, d)) -> rd.PP(s, FAr.get_prop.items(n, k, d)):
  match d:
    case Wr.Got{+i, +r}:
      (e, fi) = mp
      (Equal.trans(String, s, Wr.put_str(n, ArgRepair.ar_w_ms(k, s2)), Wr.put_str(n, ArgRepair.ar_w_ms(k, ArgRepair.ar_w_ms(i, r))), pre, Equal.cong(String, String, z => Wr.put_str(n, ArgRepair.ar_w_ms(k, z)), s2, ArgRepair.ar_w_ms(i, r), e)), SV.sv.and2(LawsBase.wire_fits(String.length(n)), Bool.and(ArgRepair.ar_fit_ms(k), ArgRepair.ar_fit_ms(i)), fn, SV.sv.and2(ArgRepair.ar_fit_ms(k), ArgRepair.ar_fit_ms(i), fk, fi)))
    case Wr.Bad{}:
      Unit{}

def rd.prop_kind(-s: String, +n: String, -s1: String, pre: {s == Wr.put_str(n, s1) : String}, fn: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, mp: rd.MS(s1, d)) -> rd.PP(s, FAr.get_prop.kind(n, d)):
  match d:
    case Wr.Got{+k, +r}:
      (e, fk) = mp
      rd.prop_items(s, n, k, r, Equal.trans(String, s, Wr.put_str(n, s1), Wr.put_str(n, ArgRepair.ar_w_ms(k, r)), pre, Equal.cong(String, String, z => Wr.put_str(n, z), s1, ArgRepair.ar_w_ms(k, r), e)), fn, fk, FAr.get_ms(r), rd.ms(r))
    case Wr.Bad{}:
      Unit{}

def rd.prop_name(-s: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s, d)) -> rd.PP(s, FAr.get_prop.name(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, fn) = sp
      rd.prop_kind(s, n, r, e, fn, FAr.get_ms(r), rd.ms(r))
    case Wr.Bad{}:
      Unit{}

# a declared argument decoded is spelled, and fits
def rd.prop(+s: String) -> rd.PP(s, FAr.get_prop(s)):
  rd.prop_name(s, Wr.get_str(s), LE.dcw.str(s))

# Aliases and refused keys
# ------------------------

def rd.KP(s: String, d: Wr.Dec<Ar.KV>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == ArgRepair.ar_w_kv(e, r) : String} & {ArgRepair.ar_fit_kv(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rd.kv_text(-s: String, +k: String, -s1: String, pre: {s == Wr.put_str(k, s1) : String}, fk: {LawsBase.wire_fits(String.length(k)) == True{} : Bool}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rd.KP(s, FAr.get_kv.text(k, d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = sp
      (Equal.trans(String, s, Wr.put_str(k, s1), Wr.put_str(k, Wr.put_str(x, r)), pre, Equal.cong(String, String, z => Wr.put_str(k, z), s1, Wr.put_str(x, r), e)), SV.sv.and2(LawsBase.wire_fits(String.length(k)), LawsBase.wire_fits(String.length(x)), fk, fx))
    case Wr.Bad{}:
      Unit{}

def rd.kv_key(-s: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s, d)) -> rd.KP(s, FAr.get_kv.key(d)):
  match d:
    case Wr.Got{+k, +r}:
      (e, fk) = sp
      rd.kv_text(s, k, r, e, fk, Wr.get_str(r), LE.dcw.str(r))
    case Wr.Bad{}:
      Unit{}

# an alias or a refused key decoded is spelled, and fits
def rd.kv(+s: String) -> rd.KP(s, FAr.get_kv(s)):
  rd.kv_key(s, Wr.get_str(s), LE.dcw.str(s))

# Values
# ------

def rd.SH(s: String, d: Wr.Dec<Ar.Shape>) -> Type:
  match d:
    case Wr.Got{sh, r}:
      {s == ArgRepair.ar_w_shape(sh, r) : String}
    case Wr.Bad{}:
      Unit

def rd.shape_brace(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> rd.SH(s, FAr.get_shape.brace(d)):
  match d:
    case Wr.Got{+b, +r}:
      LE.dcw.after(s, 1n, s1, Wr.put_bool(b, r), pre, Wire.wire_bool_exact(s1, b, r, ed))
    case Wr.Bad{}:
      Unit{}

def rd.shape_bracket(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> rd.SH(s, FAr.get_shape.bracket(d)):
  match d:
    case Wr.Got{+b, +r}:
      LE.dcw.after(s, 2n, s1, Wr.put_bool(b, r), pre, Wire.wire_bool_exact(s1, b, r, ed))
    case Wr.Bad{}:
      Unit{}

def rd.shape_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rd.SH(s, FAr.get_shape(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          np
        case 1n:
          rd.shape_brace(s, s1, np, Wr.get_bool(s1), {==})
        case 2n:
          rd.shape_bracket(s, s1, np, Wr.get_bool(s1), {==})
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a shape decoded is spelled
def rd.shape(+s: String) -> rd.SH(s, FAr.get_shape(Wr.get_nat(s))):
  rd.shape_at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rd.VP(s: String, d: Wr.Dec<Ar.Val>) -> Type:
  match d:
    case Wr.Got{v, r}:
      {s == ArgRepair.ar_w_val(v, r) : String} & {ArgRepair.ar_fit_val(v) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rd.val_bool(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> rd.VP(s, FAr.get_bool.val(d)):
  match d:
    case Wr.Got{+b, +r}:
      (LE.dcw.after(s, 1n, s1, Wr.put_bool(b, r), pre, Wire.wire_bool_exact(s1, b, r, ed)), {==})
    case Wr.Bad{}:
      Unit{}

def rd.val_num(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rd.VP(s, FAr.get_num.val(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = sp
      (LE.dcw.after(s, 2n, s1, Wr.put_str(x, r), pre, e), fx)
    case Wr.Bad{}:
      Unit{}

def rd.val_shape(-s: String, +t: Maybe<&2, String>, +n: Maybe<&2, String>, -s3: String, pre: {s == Wr.put_nat(3n, ArgRepair.ar_w_ms(t, ArgRepair.ar_w_ms(n, s3))) : String}, ft: {ArgRepair.ar_fit_ms(t) == True{} : Bool}, fn: {ArgRepair.ar_fit_ms(n) == True{} : Bool}, d: Wr.Dec<Ar.Shape>, hp: rd.SH(s3, d)) -> rd.VP(s, FAr.get_str.shape(t, n, d)):
  match d:
    case Wr.Got{+sh, +r}:
      (Equal.trans(String, s, Wr.put_nat(3n, ArgRepair.ar_w_ms(t, ArgRepair.ar_w_ms(n, s3))), Wr.put_nat(3n, ArgRepair.ar_w_ms(t, ArgRepair.ar_w_ms(n, ArgRepair.ar_w_shape(sh, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(3n, ArgRepair.ar_w_ms(t, ArgRepair.ar_w_ms(n, z))), s3, ArgRepair.ar_w_shape(sh, r), hp)), SV.sv.and2(ArgRepair.ar_fit_ms(t), ArgRepair.ar_fit_ms(n), ft, fn))
    case Wr.Bad{}:
      Unit{}

def rd.val_strnum(-s: String, +t: Maybe<&2, String>, -s2: String, pre: {s == Wr.put_nat(3n, ArgRepair.ar_w_ms(t, s2)) : String}, ft: {ArgRepair.ar_fit_ms(t) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, mp: rd.MS(s2, d)) -> rd.VP(s, FAr.get_str.num(t, d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, fn) = mp
      rd.val_shape(s, t, n, r, Equal.trans(String, s, Wr.put_nat(3n, ArgRepair.ar_w_ms(t, s2)), Wr.put_nat(3n, ArgRepair.ar_w_ms(t, ArgRepair.ar_w_ms(n, r))), pre, Equal.cong(String, String, z => Wr.put_nat(3n, ArgRepair.ar_w_ms(t, z)), s2, ArgRepair.ar_w_ms(n, r), e)), ft, fn, FAr.get_shape(Wr.get_nat(r)), rd.shape(r))
    case Wr.Bad{}:
      Unit{}

def rd.val_str(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Maybe<&2, String>>, mp: rd.MS(s1, d)) -> rd.VP(s, FAr.get_str.text(d)):
  match d:
    case Wr.Got{+t, +r}:
      (e, ft) = mp
      rd.val_strnum(s, t, r, LE.dcw.after(s, 3n, s1, ArgRepair.ar_w_ms(t, r), pre, e), ft, FAr.get_ms(r), rd.ms(r))
    case Wr.Bad{}:
      Unit{}

def rd.val_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rd.VP(s, FAr.get_val(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (np, {==})
        case 1n:
          rd.val_bool(s, s1, np, Wr.get_bool(s1), {==})
        case 2n:
          rd.val_num(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 3n:
          rd.val_str(s, s1, np, FAr.get_ms(s1), rd.ms(s1))
        case 4n:
          (np, {==})
        case 5n:
          (np, {==})
        case 6n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value decoded is spelled, and fits
def rd.val(+s: String) -> rd.VP(s, FAr.get_val(Wr.get_nat(s))):
  rd.val_at(s, Wr.get_nat(s), LE.dcw.nat(s))

# Sent arguments
# --------------

def rd.AP(s: String, d: Wr.Dec<Ar.Arg>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == ArgRepair.ar_w_arg(a, r) : String} & {ArgRepair.ar_fit_arg(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rd.arg_val(-s: String, +k: String, +p: Maybe<&2, String>, -s2: String, pre: {s == Wr.put_str(k, ArgRepair.ar_w_ms(p, s2)) : String}, fk: {LawsBase.wire_fits(String.length(k)) == True{} : Bool}, fp: {ArgRepair.ar_fit_ms(p) == True{} : Bool}, d: Wr.Dec<Ar.Val>, vp: rd.VP(s2, d)) -> rd.AP(s, FAr.get_arg.val(k, p, d)):
  match d:
    case Wr.Got{+v, +r}:
      (e, fv) = vp
      (Equal.trans(String, s, Wr.put_str(k, ArgRepair.ar_w_ms(p, s2)), Wr.put_str(k, ArgRepair.ar_w_ms(p, ArgRepair.ar_w_val(v, r))), pre, Equal.cong(String, String, z => Wr.put_str(k, ArgRepair.ar_w_ms(p, z)), s2, ArgRepair.ar_w_val(v, r), e)), SV.sv.and2(LawsBase.wire_fits(String.length(k)), Bool.and(ArgRepair.ar_fit_ms(p), ArgRepair.ar_fit_val(v)), fk, SV.sv.and2(ArgRepair.ar_fit_ms(p), ArgRepair.ar_fit_val(v), fp, fv)))
    case Wr.Bad{}:
      Unit{}

def rd.arg_plain(-s: String, +k: String, -s1: String, pre: {s == Wr.put_str(k, s1) : String}, fk: {LawsBase.wire_fits(String.length(k)) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, mp: rd.MS(s1, d)) -> rd.AP(s, FAr.get_arg.plain(k, d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, fp) = mp
      rd.arg_val(s, k, p, r, Equal.trans(String, s, Wr.put_str(k, s1), Wr.put_str(k, ArgRepair.ar_w_ms(p, r)), pre, Equal.cong(String, String, z => Wr.put_str(k, z), s1, ArgRepair.ar_w_ms(p, r), e)), fk, fp, FAr.get_val(Wr.get_nat(r)), rd.val(r))
    case Wr.Bad{}:
      Unit{}

def rd.arg_key(-s: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s, d)) -> rd.AP(s, FAr.get_arg.key(d)):
  match d:
    case Wr.Got{+k, +r}:
      (e, fk) = sp
      rd.arg_plain(s, k, r, e, fk, FAr.get_ms(r), rd.ms(r))
    case Wr.Bad{}:
      Unit{}

# a sent argument decoded is spelled, and fits
def rd.arg(+s: String) -> rd.AP(s, FAr.get_arg(s)):
  rd.arg_key(s, Wr.get_str(s), LE.dcw.str(s))

# Lists
# -----

# what the props loop's answer says about its input s (m + 1 items)
def rd.props.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Ar.Prop>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ArgRepair.ar_w_props.items(xs, r) : String} & ({List.length(&2, Ar.Prop, xs) == 1n+m : Nat} & {ArgRepair.ar_fit_props(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def rd.props.step(-s: String, +x: Ar.Prop, +s3: String, -k: Nat, ex: {s == ArgRepair.ar_w_prop(x, s3) : String}, fx: {ArgRepair.ar_fit_prop(x) == True{} : Bool}, d: Wr.Dec<List<&2, Ar.Prop>>, ih: rd.props.PL(s3, k, d)) -> rd.props.PL(s, 1n+k, Wr.get_list.cons(Ar.Prop, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, ArgRepair.ar_w_prop(x, s3), ArgRepair.ar_w_prop(x, ArgRepair.ar_w_props.items(ys, r)), ex, Equal.cong(String, String, z => ArgRepair.ar_w_prop(x, z), s3, ArgRepair.ar_w_props.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Ar.Prop, ys), 1n+k, e2), SV.sv.and2(ArgRepair.ar_fit_prop(x), ArgRepair.ar_fit_props(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def rd.props.loop(m: Nat, cur: Wr.Dec<Ar.Prop>, +s: String, pc: rd.PP(s, cur)) -> rd.props.PL(s, m, Wr.get_list.go(~Ar.Prop, ~FAr.get_prop, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, SV.sv.and2(ArgRepair.ar_fit_prop(x), ArgRepair.ar_fit_props(Nil{}), f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      rd.props.step(s, x, s3, k, e, f, Wr.get_list.go(~Ar.Prop, ~FAr.get_prop, k, FAr.get_prop(s3)), rd.props.loop(k, FAr.get_prop(s3), s3, rd.prop(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a props list decoder's answer says about its input s
def rd.props.LS(s: String, d: Wr.Dec<List<&2, Ar.Prop>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Ar.Prop, xs), ArgRepair.ar_w_props.items(xs, r)) : String} & ({LawsBase.wire_fits(List.length(&2, Ar.Prop, xs)) == True{} : Bool} & {ArgRepair.ar_fit_props(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def rd.props.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Ar.Prop>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == ArgRepair.ar_w_props.items(xs, r) : String}, e2: {List.length(&2, Ar.Prop, xs) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, Ar.Prop, xs), ArgRepair.ar_w_props.items(xs, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Ar.Prop, xs), 1n+m, e2) : {s == Wr.put_nat(_, ArgRepair.ar_w_props.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def rd.props.conv_f(-m: Nat, -xs: List<&2, Ar.Prop>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Ar.Prop, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Ar.Prop, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Ar.Prop, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def rd.props.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Ar.Prop>>, pl: rd.props.PL(s2, m, d)) -> rd.props.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (rd.props.conv_s(s, s2, m, xs, r, en, e1, e2), (rd.props.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def rd.props.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> rd.props.LS(s, Wr.get_list.start(~Ar.Prop, ~FAr.get_prop, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      rd.props.conv(s, s2, m, en, fn, Wr.get_list.go(~Ar.Prop, ~FAr.get_prop, m, FAr.get_prop(s2)), rd.props.loop(m, FAr.get_prop(s2), s2, rd.prop(s2)))

def rd.props.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rd.props.LS(s, Wr.get_list.start(~Ar.Prop, ~FAr.get_prop, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      rd.props.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a props list decoded is spelled, and what it holds fits the wire
def rd.props.list(+s: String) -> rd.props.LS(s, Wr.get_list(~Ar.Prop, ~FAr.get_prop, s)):
  rd.props.top(s, Wr.get_nat(s), {==})

# what the kvs loop's answer says about its input s (m + 1 items)
def rd.kvs.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Ar.KV>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ArgRepair.ar_w_kvs.items(xs, r) : String} & ({List.length(&2, Ar.KV, xs) == 1n+m : Nat} & {ArgRepair.ar_fit_kvs(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def rd.kvs.step(-s: String, +x: Ar.KV, +s3: String, -k: Nat, ex: {s == ArgRepair.ar_w_kv(x, s3) : String}, fx: {ArgRepair.ar_fit_kv(x) == True{} : Bool}, d: Wr.Dec<List<&2, Ar.KV>>, ih: rd.kvs.PL(s3, k, d)) -> rd.kvs.PL(s, 1n+k, Wr.get_list.cons(Ar.KV, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, ArgRepair.ar_w_kv(x, s3), ArgRepair.ar_w_kv(x, ArgRepair.ar_w_kvs.items(ys, r)), ex, Equal.cong(String, String, z => ArgRepair.ar_w_kv(x, z), s3, ArgRepair.ar_w_kvs.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Ar.KV, ys), 1n+k, e2), SV.sv.and2(ArgRepair.ar_fit_kv(x), ArgRepair.ar_fit_kvs(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def rd.kvs.loop(m: Nat, cur: Wr.Dec<Ar.KV>, +s: String, pc: rd.KP(s, cur)) -> rd.kvs.PL(s, m, Wr.get_list.go(~Ar.KV, ~FAr.get_kv, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, SV.sv.and2(ArgRepair.ar_fit_kv(x), ArgRepair.ar_fit_kvs(Nil{}), f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      rd.kvs.step(s, x, s3, k, e, f, Wr.get_list.go(~Ar.KV, ~FAr.get_kv, k, FAr.get_kv(s3)), rd.kvs.loop(k, FAr.get_kv(s3), s3, rd.kv(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a kvs list decoder's answer says about its input s
def rd.kvs.LS(s: String, d: Wr.Dec<List<&2, Ar.KV>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Ar.KV, xs), ArgRepair.ar_w_kvs.items(xs, r)) : String} & ({LawsBase.wire_fits(List.length(&2, Ar.KV, xs)) == True{} : Bool} & {ArgRepair.ar_fit_kvs(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def rd.kvs.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Ar.KV>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == ArgRepair.ar_w_kvs.items(xs, r) : String}, e2: {List.length(&2, Ar.KV, xs) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, Ar.KV, xs), ArgRepair.ar_w_kvs.items(xs, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Ar.KV, xs), 1n+m, e2) : {s == Wr.put_nat(_, ArgRepair.ar_w_kvs.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def rd.kvs.conv_f(-m: Nat, -xs: List<&2, Ar.KV>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Ar.KV, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Ar.KV, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Ar.KV, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def rd.kvs.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Ar.KV>>, pl: rd.kvs.PL(s2, m, d)) -> rd.kvs.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (rd.kvs.conv_s(s, s2, m, xs, r, en, e1, e2), (rd.kvs.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def rd.kvs.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> rd.kvs.LS(s, Wr.get_list.start(~Ar.KV, ~FAr.get_kv, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      rd.kvs.conv(s, s2, m, en, fn, Wr.get_list.go(~Ar.KV, ~FAr.get_kv, m, FAr.get_kv(s2)), rd.kvs.loop(m, FAr.get_kv(s2), s2, rd.kv(s2)))

def rd.kvs.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rd.kvs.LS(s, Wr.get_list.start(~Ar.KV, ~FAr.get_kv, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      rd.kvs.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a kvs list decoded is spelled, and what it holds fits the wire
def rd.kvs.list(+s: String) -> rd.kvs.LS(s, Wr.get_list(~Ar.KV, ~FAr.get_kv, s)):
  rd.kvs.top(s, Wr.get_nat(s), {==})

# what the args loop's answer says about its input s (m + 1 items)
def rd.args.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Ar.Arg>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ArgRepair.ar_w_args.items(xs, r) : String} & ({List.length(&2, Ar.Arg, xs) == 1n+m : Nat} & {ArgRepair.ar_fit_args(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def rd.args.step(-s: String, +x: Ar.Arg, +s3: String, -k: Nat, ex: {s == ArgRepair.ar_w_arg(x, s3) : String}, fx: {ArgRepair.ar_fit_arg(x) == True{} : Bool}, d: Wr.Dec<List<&2, Ar.Arg>>, ih: rd.args.PL(s3, k, d)) -> rd.args.PL(s, 1n+k, Wr.get_list.cons(Ar.Arg, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, ArgRepair.ar_w_arg(x, s3), ArgRepair.ar_w_arg(x, ArgRepair.ar_w_args.items(ys, r)), ex, Equal.cong(String, String, z => ArgRepair.ar_w_arg(x, z), s3, ArgRepair.ar_w_args.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Ar.Arg, ys), 1n+k, e2), SV.sv.and2(ArgRepair.ar_fit_arg(x), ArgRepair.ar_fit_args(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def rd.args.loop(m: Nat, cur: Wr.Dec<Ar.Arg>, +s: String, pc: rd.AP(s, cur)) -> rd.args.PL(s, m, Wr.get_list.go(~Ar.Arg, ~FAr.get_arg, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, SV.sv.and2(ArgRepair.ar_fit_arg(x), ArgRepair.ar_fit_args(Nil{}), f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      rd.args.step(s, x, s3, k, e, f, Wr.get_list.go(~Ar.Arg, ~FAr.get_arg, k, FAr.get_arg(s3)), rd.args.loop(k, FAr.get_arg(s3), s3, rd.arg(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a args list decoder's answer says about its input s
def rd.args.LS(s: String, d: Wr.Dec<List<&2, Ar.Arg>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, r)) : String} & ({LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)) == True{} : Bool} & {ArgRepair.ar_fit_args(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def rd.args.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Ar.Arg>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == ArgRepair.ar_w_args.items(xs, r) : String}, e2: {List.length(&2, Ar.Arg, xs) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Ar.Arg, xs), 1n+m, e2) : {s == Wr.put_nat(_, ArgRepair.ar_w_args.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def rd.args.conv_f(-m: Nat, -xs: List<&2, Ar.Arg>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Ar.Arg, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Ar.Arg, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def rd.args.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Ar.Arg>>, pl: rd.args.PL(s2, m, d)) -> rd.args.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (rd.args.conv_s(s, s2, m, xs, r, en, e1, e2), (rd.args.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def rd.args.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> rd.args.LS(s, Wr.get_list.start(~Ar.Arg, ~FAr.get_arg, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      rd.args.conv(s, s2, m, en, fn, Wr.get_list.go(~Ar.Arg, ~FAr.get_arg, m, FAr.get_arg(s2)), rd.args.loop(m, FAr.get_arg(s2), s2, rd.arg(s2)))

def rd.args.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rd.args.LS(s, Wr.get_list.start(~Ar.Arg, ~FAr.get_arg, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      rd.args.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a args list decoded is spelled, and what it holds fits the wire
def rd.args.list(+s: String) -> rd.args.LS(s, Wr.get_list(~Ar.Arg, ~FAr.get_arg, s)):
  rd.args.top(s, Wr.get_nat(s), {==})

# The request
# -----------

def rd.RP(s: String, d: Wr.Dec<FAr.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ArgRepair.ar_w_req(q, r) : String} & {ArgRepair.ar_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rd.req_args(-s: String, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, -s4: String, pre: {s == Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, s4))))))) : String}, f0: {LawsBase.wire_fits(List.length(&2, Ar.Prop, ps)) == True{} : Bool}, f1: {ArgRepair.ar_fit_props(ps) == True{} : Bool}, f2: {LawsBase.wire_fits(List.length(&2, Ar.KV, als)) == True{} : Bool}, f3: {ArgRepair.ar_fit_kvs(als) == True{} : Bool}, f4: {LawsBase.wire_fits(List.length(&2, Ar.KV, rs)) == True{} : Bool}, f5: {ArgRepair.ar_fit_kvs(rs) == True{} : Bool}, d: Wr.Dec<List<&2, Ar.Arg>>, lp: rd.args.LS(s4, d)) -> rd.RP(s, FAr.get_req.args(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e, f67) = lp
      (f6, f7) = f67
      (Equal.trans(String, s, Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, s4))))))), Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, r))))))))), pre, Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, z))))))), s4, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, r)), e)), SV.sv.and2(LawsBase.wire_fits(List.length(&2, Ar.Prop, ps)), Bool.and(ArgRepair.ar_fit_props(ps), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, als)), Bool.and(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs))))))), f0, SV.sv.and2(ArgRepair.ar_fit_props(ps), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, als)), Bool.and(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs)))))), f1, SV.sv.and2(LawsBase.wire_fits(List.length(&2, Ar.KV, als)), Bool.and(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs))))), f2, SV.sv.and2(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs)))), f3, SV.sv.and2(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs))), f4, SV.sv.and2(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs)), f5, SV.sv.and2(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs), f6, f7))))))))
    case Wr.Bad{}:
      Unit{}

def rd.req_refused(-s: String, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, -s3: String, pre: {s == Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, s3))))) : String}, f0: {LawsBase.wire_fits(List.length(&2, Ar.Prop, ps)) == True{} : Bool}, f1: {ArgRepair.ar_fit_props(ps) == True{} : Bool}, f2: {LawsBase.wire_fits(List.length(&2, Ar.KV, als)) == True{} : Bool}, f3: {ArgRepair.ar_fit_kvs(als) == True{} : Bool}, d: Wr.Dec<List<&2, Ar.KV>>, lp: rd.kvs.LS(s3, d)) -> rd.RP(s, FAr.get_req.refused(Ar.Schema{ps, cl}, als, d)):
  match d:
    case Wr.Got{+rs, +r}:
      (e, f45) = lp
      (f4, f5) = f45
      rd.req_args(s, ps, cl, als, rs, r, Equal.trans(String, s, Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, s3))))), Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, r))))))), pre, Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, z))))), s3, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, r)), e)), f0, f1, f2, f3, f4, f5, Wr.get_list(~Ar.Arg, ~FAr.get_arg, r), rd.args.list(r))
    case Wr.Bad{}:
      Unit{}

def rd.req_aliases(-s: String, +ps: List<&2, Ar.Prop>, +cl: Bool, -s2: String, pre: {s == Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, s2))) : String}, f0: {LawsBase.wire_fits(List.length(&2, Ar.Prop, ps)) == True{} : Bool}, f1: {ArgRepair.ar_fit_props(ps) == True{} : Bool}, d: Wr.Dec<List<&2, Ar.KV>>, lp: rd.kvs.LS(s2, d)) -> rd.RP(s, FAr.get_req.aliases(Ar.Schema{ps, cl}, d)):
  match d:
    case Wr.Got{+als, +r}:
      (e, f23) = lp
      (f2, f3) = f23
      rd.req_refused(s, ps, cl, als, r, Equal.trans(String, s, Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, s2))), Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, r))))), pre, Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, z))), s2, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, r)), e)), f0, f1, f2, f3, Wr.get_list(~Ar.KV, ~FAr.get_kv, r), rd.kvs.list(r))
    case Wr.Bad{}:
      Unit{}

def rd.req_closed(-s: String, +ps: List<&2, Ar.Prop>, +s1: String, pre: {s == Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, s1)) : String}, f0: {LawsBase.wire_fits(List.length(&2, Ar.Prop, ps)) == True{} : Bool}, f1: {ArgRepair.ar_fit_props(ps) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> rd.RP(s, FAr.get_req.closed(ps, d)):
  match d:
    case Wr.Got{+cl, +r}:
      rd.req_aliases(s, ps, cl, r, Equal.trans(String, s, Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, s1)), Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, r))), pre, Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, z)), s1, Wr.put_bool(cl, r), Wire.wire_bool_exact(s1, cl, r, ed))), f0, f1, Wr.get_list(~Ar.KV, ~FAr.get_kv, r), rd.kvs.list(r))
    case Wr.Bad{}:
      Unit{}

def rd.req_props(+s: String, d: Wr.Dec<List<&2, Ar.Prop>>, lp: rd.props.LS(s, d)) -> rd.RP(s, FAr.get_req.props(d)):
  match d:
    case Wr.Got{+ps, +r}:
      (e, f01) = lp
      (f0, f1) = f01
      rd.req_closed(s, ps, r, e, f0, f1, Wr.get_bool(r), {==})
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and fits
def rd.req(+s: String) -> rd.RP(s, FAr.get_req(s)):
  rd.req_props(s, Wr.get_list(~Ar.Prop, ~FAr.get_prop, s), rd.props.list(s))

def rd.T(s: String) -> Type:
  Sigma<&1, &1, FAr.Req, q => {s == ArgRepair.ar_w_req(q, "") : String} & {ArgRepair.ar_fit_req(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def rd.top(-s: String, d: Wr.Dec<FAr.Req>, rp: rd.RP(s, d), ok: {LawsBase.wire_opens_err(FAr.ffi.got(d)) == False{} : Bool}) -> rd.T(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(rd.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(rd.T(s), ok)
