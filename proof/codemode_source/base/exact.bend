# eukhe: lemmas of the entry proofs of area codemode_source: only spelled
# requests decode
#
# Each decoder of bend/ffi_codemode_source.bend answers Got only for the
# spec's spelling of a value whose numbers fit (Nats, Bools and the
# options lines: proof/context_order/base/exact.bend; strings:
# wire_str_exact, wire_str_decoded_fits).

import Base
import ../../../bend/codemode_source.bend as Src
import ../../../bend/ffi_codemode_source.bend as FSrc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/codemode_source.bend as CodemodeSource
import ../../context_order/base.bend as LACo
import ../../context_order/base/exact.bend as LACoExact

# ---- strings ----

def cse.PS(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{+a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cse.ps_go(+s: String, d: Wr.Dec<String>, +ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> cse.PS(s, d):
  match d:
    case Wr.Got{+a, +r}:
      (Wire.wire_str_exact(s, a, r, ed), Wire.wire_str_decoded_fits(s, a, r, ed))
    case Wr.Bad{}:
      Unit{}

def cse.ps(+s: String) -> cse.PS(s, Wr.get_str(s)):
  cse.ps_go(s, Wr.get_str(s), {==})

# ---- values ----

def cse.NU(s: String, d: Wr.Dec<Src.Num>) -> Type:
  match d:
    case Wr.Got{+v, r}:
      {s == CodemodeSource.spell_num(v, r) : String} & {CodemodeSource.num_fits(v) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cse.nu.n(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s1, d)) -> cse.NU(s, FSrc.get_num.n(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(n, r)), e0, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(n, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def cse.nu.top(-s: String, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s, d)) -> cse.NU(s, FSrc.get_num.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          (e0, {==})
        case 1n:
          (e0, f0) = p
          cse.nu.n(s, s1, e0, Wr.get_nat(s1), LACoExact.coe.pnf(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value decoded is spelled, and its integer fits
def cse.num(+s: String) -> cse.NU(s, FSrc.get_num(s)):
  cse.nu.top(s, Wr.get_nat(s), LACoExact.coe.pnf(s))

# ---- fields ----

def cse.FI(s: String, d: Wr.Dec<Src.Field>) -> Type:
  match d:
    case Wr.Got{+f, r}:
      {s == CodemodeSource.spell_field(f, r) : String} & {CodemodeSource.field_fits(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cse.fi.num(-s: String, -s1: String, +k: String, e0: {s == Wr.put_str(k, s1) : String}, fk: {LawsBase.wire_fits(String.length(k)) == True{} : Bool}, d: Wr.Dec<Src.Num>, p: cse.NU(s1, d)) -> cse.FI(s, FSrc.get_field.num(k, d)):
  match d:
    case Wr.Got{+v, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_str(k, s1), Wr.put_str(k, CodemodeSource.spell_num(v, r)), e0, Equal.cong(String, String, z => Wr.put_str(k, z), s1, CodemodeSource.spell_num(v, r), e1)), LACo.co.and_tt(LawsBase.wire_fits(String.length(k)), CodemodeSource.num_fits(v), fk, f1))
    case Wr.Bad{}:
      Unit{}

def cse.fi.key(-s: String, d: Wr.Dec<String>, p: cse.PS(s, d)) -> cse.FI(s, FSrc.get_field.key(d)):
  match d:
    case Wr.Got{+k, +s1}:
      (e0, f0) = p
      cse.fi.num(s, s1, k, e0, f0, FSrc.get_num(s1), cse.num(s1))
    case Wr.Bad{}:
      Unit{}

# a field decoded is spelled, and its key and integer fit
def cse.field(+s: String) -> cse.FI(s, FSrc.get_field(s)):
  cse.fi.key(s, Wr.get_str(s), cse.ps(s))

# what the item loop over fields answers says about its input s (m + 1 items)
def cse.fl.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Src.Field>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == CodemodeSource.spell_fields.items(xs, r) : String} & ({List.length(&2, Src.Field, xs) == 1n+m : Nat} & {CodemodeSource.fields_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def cse.fl.step(-s: String, +x: Src.Field, +s3: String, -k: Nat, ex: {s == CodemodeSource.spell_field(x, s3) : String}, fx: {CodemodeSource.field_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Src.Field>>, ih: cse.fl.PL(s3, k, d)) -> cse.fl.PL(s, 1n+k, Wr.get_list.cons(Src.Field, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, rest) = ih
      (e2, e3) = rest
      (Equal.trans(String, s, CodemodeSource.spell_field(x, s3), CodemodeSource.spell_field(x, CodemodeSource.spell_fields.items(ys, r)), ex, Equal.cong(String, String, z => CodemodeSource.spell_field(x, z), s3, CodemodeSource.spell_fields.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Src.Field, ys), 1n+k, e2), LACo.co.and_tt(CodemodeSource.field_fits(x), CodemodeSource.fields_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled fields whose numbers fit
def cse.fl.loop(m: Nat, cur: Wr.Dec<Src.Field>, +s: String, pc: cse.FI(s, cur)) -> cse.fl.PL(s, m, Wr.get_list.go(~Src.Field, ~FSrc.get_field, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LACo.co.and_tt(CodemodeSource.field_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      cse.fl.step(s, x, s3, k, e, f, Wr.get_list.go(~Src.Field, ~FSrc.get_field, k, FSrc.get_field(s3)), cse.fl.loop(k, FSrc.get_field(s3), s3, cse.field(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def cse.fl.LS(s: String, d: Wr.Dec<List<&2, Src.Field>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Src.Field, xs), CodemodeSource.spell_fields.items(xs, r)) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Src.Field, xs)), CodemodeSource.fields_all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cse.fl.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Src.Field>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == CodemodeSource.spell_fields.items(xs, r) : String}, e2: {List.length(&2, Src.Field, xs) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, Src.Field, xs), CodemodeSource.spell_fields.items(xs, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Src.Field, xs), 1n+m, e2) : {s == Wr.put_nat(_, CodemodeSource.spell_fields.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def cse.fl.conv_f(+m: Nat, +xs: List<&2, Src.Field>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Src.Field, xs) == 1n+m : Nat}, e3: {CodemodeSource.fields_all(xs) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Src.Field, xs)), CodemodeSource.fields_all(xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Src.Field, xs), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), CodemodeSource.fields_all(xs)) == True{} : Bool}
  LACo.co.and_tt(LawsBase.wire_fits(1n+m), CodemodeSource.fields_all(xs), fn, e3)

def cse.fl.conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Src.Field>>, pl: cse.fl.PL(s2, m, d)) -> cse.fl.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, rest) = pl
      (+e2, e3) = rest
      (cse.fl.conv_s(s, s2, m, xs, r, en, e1, e2), cse.fl.conv_f(m, xs, fn, e2, e3))
    case Wr.Bad{}:
      Unit{}

def cse.fl.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> cse.fl.LS(s, Wr.get_list.start(~Src.Field, ~FSrc.get_field, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      cse.fl.conv(s, s2, m, en, fn, Wr.get_list.go(~Src.Field, ~FSrc.get_field, m, FSrc.get_field(s2)), cse.fl.loop(m, FSrc.get_field(s2), s2, cse.field(s2)))

def cse.fl.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cse.fl.LS(s, Wr.get_list.start(~Src.Field, ~FSrc.get_field, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      cse.fl.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of fields decoded is spelled, and its count and fields fit
def cse.fl.list(+s: String) -> cse.fl.LS(s, Wr.get_list(~Src.Field, ~FSrc.get_field, s)):
  cse.fl.top(s, Wr.get_nat(s), {==})

# ---- what serde_json read ----

def cse.JS(s: String, d: Wr.Dec<Src.Json>) -> Type:
  match d:
    case Wr.Got{+j, r}:
      {s == CodemodeSource.spell_json(j, r) : String} & {CodemodeSource.json_fits(j) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cse.js.text(-s: String, -s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, p: cse.PS(s1, d)) -> cse.JS(s, FSrc.get_json.text(d)):
  match d:
    case Wr.Got{+t, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_str(t, r)), e0, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_str(t, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def cse.js.fields(-s: String, -s1: String, e0: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<List<&2, Src.Field>>, p: cse.fl.LS(s1, d)) -> cse.JS(s, FSrc.get_json.fields(d)):
  match d:
    case Wr.Got{+fs, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_nat(List.length(&2, Src.Field, fs), CodemodeSource.spell_fields.items(fs, r))), e0, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_nat(List.length(&2, Src.Field, fs), CodemodeSource.spell_fields.items(fs, r)), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def cse.js.top(-s: String, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s, d)) -> cse.JS(s, FSrc.get_json.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          cse.js.text(s, s1, e0, Wr.get_str(s1), cse.ps(s1))
        case 1n:
          (e0, f0) = p
          (e0, {==})
        case 2n:
          (e0, f0) = p
          cse.js.fields(s, s1, e0, Wr.get_list(~Src.Field, ~FSrc.get_field, s1), cse.fl.list(s1))
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# what serde_json read, decoded, is spelled, and its numbers fit
def cse.json(+s: String) -> cse.JS(s, FSrc.get_json(s)):
  cse.js.top(s, Wr.get_nat(s), LACoExact.coe.pnf(s))

# ---- directives ----

def cse.DI(s: String, d: Wr.Dec<Src.Dir>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == CodemodeSource.spell_dir(x, r) : String} & {CodemodeSource.dir_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cse.di.json(-s: String, -s1: String, +e: Bool, e0: {s == Wr.put_bool(e, s1) : String}, d: Wr.Dec<Src.Json>, p: cse.JS(s1, d)) -> cse.DI(s, FSrc.get_dir.json(e, d)):
  match d:
    case Wr.Got{+j, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_bool(e, s1), Wr.put_bool(e, CodemodeSource.spell_json(j, r)), e0, Equal.cong(String, String, z => Wr.put_bool(e, z), s1, CodemodeSource.spell_json(j, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def cse.di.top(-s: String, d: Wr.Dec<Bool>, p: LACoExact.coe.PB(s, d)) -> cse.DI(s, FSrc.get_dir.empty(d)):
  match d:
    case Wr.Got{+e, +s1}:
      cse.di.json(s, s1, e, p, FSrc.get_json(s1), cse.json(s1))
    case Wr.Bad{}:
      Unit{}

def cse.dir(+s: String) -> cse.DI(s, FSrc.get_dir(s)):
  cse.di.top(s, Wr.get_bool(s), LACoExact.coe.pb(s))

def cse.MD(s: String, d: Wr.Dec<Maybe<&2, Src.Dir>>) -> Type:
  match d:
    case Wr.Got{+m, r}:
      {s == CodemodeSource.spell_mdir(m, r) : String} & {CodemodeSource.mdir_fits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cse.md.dir(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Src.Dir>, p: cse.DI(s1, d)) -> cse.MD(s, FSrc.get_mdir.dir(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, CodemodeSource.spell_dir(x, r)), e0, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, CodemodeSource.spell_dir(x, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def cse.md.top(-s: String, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s, d)) -> cse.MD(s, FSrc.get_mdir.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          (e0, {==})
        case 1n:
          (e0, f0) = p
          cse.md.dir(s, s1, e0, FSrc.get_dir(s1), cse.dir(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def cse.mdir(+s: String) -> cse.MD(s, FSrc.get_mdir(s)):
  cse.md.top(s, Wr.get_nat(s), LACoExact.coe.pnf(s))

# ---- requests ----

def cse.RQ(s: String, d: Wr.Dec<Src.Facts>) -> Type:
  match d:
    case Wr.Got{+f, r}:
      {s == CodemodeSource.spell_req(f, r) : String} & {CodemodeSource.req_fits(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cse.rq.dir(-s: String, -s3: String, +b: Bool, +ms: List<&2, Nat>, +rb: Bool, e0: {s == Wr.put_bool(b, LawsBase.wire_spell_nats(ms, Wr.put_bool(rb, s3))) : String}, fm: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ms)), LawsBase.wire_nats_fit(ms)) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Src.Dir>>, p: cse.MD(s3, d)) -> cse.RQ(s, FSrc.get_req.dir(b, ms, rb, d)):
  match d:
    case Wr.Got{+m, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_bool(b, LawsBase.wire_spell_nats(ms, Wr.put_bool(rb, s3))), Wr.put_bool(b, LawsBase.wire_spell_nats(ms, Wr.put_bool(rb, CodemodeSource.spell_mdir(m, r)))), e0, Equal.cong(String, String, z => Wr.put_bool(b, LawsBase.wire_spell_nats(ms, Wr.put_bool(rb, z))), s3, CodemodeSource.spell_mdir(m, r), e1)), LACo.co.and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ms)), LawsBase.wire_nats_fit(ms)), CodemodeSource.mdir_fits(m), fm, f1))
    case Wr.Bad{}:
      Unit{}

def cse.rq.rest(-s: String, -s2: String, +b: Bool, +ms: List<&2, Nat>, e0: {s == Wr.put_bool(b, LawsBase.wire_spell_nats(ms, s2)) : String}, fm: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ms)), LawsBase.wire_nats_fit(ms)) == True{} : Bool}, d: Wr.Dec<Bool>, p: LACoExact.coe.PB(s2, d)) -> cse.RQ(s, FSrc.get_req.rest(b, ms, d)):
  match d:
    case Wr.Got{+rb, +s3}:
      cse.rq.dir(s, s3, b, ms, rb, Equal.trans(String, s, Wr.put_bool(b, LawsBase.wire_spell_nats(ms, s2)), Wr.put_bool(b, LawsBase.wire_spell_nats(ms, Wr.put_bool(rb, s3))), e0, Equal.cong(String, String, z => Wr.put_bool(b, LawsBase.wire_spell_nats(ms, z)), s2, Wr.put_bool(rb, s3), p)), fm, FSrc.get_mdir(s3), cse.mdir(s3))
    case Wr.Bad{}:
      Unit{}

def cse.rq.marks(-s: String, -s1: String, +b: Bool, e0: {s == Wr.put_bool(b, s1) : String}, d: Wr.Dec<List<&2, Nat>>, p: LACoExact.coe.nl.LS(s1, d)) -> cse.RQ(s, FSrc.get_req.marks(b, d)):
  match d:
    case Wr.Got{+ms, +s2}:
      (e1, f1) = p
      cse.rq.rest(s, s2, b, ms, Equal.trans(String, s, Wr.put_bool(b, s1), Wr.put_bool(b, LawsBase.wire_spell_nats(ms, s2)), e0, Equal.cong(String, String, z => Wr.put_bool(b, z), s1, LawsBase.wire_spell_nats(ms, s2), e1)), f1, Wr.get_bool(s2), LACoExact.coe.pb(s2))
    case Wr.Bad{}:
      Unit{}

def cse.rq.top(-s: String, d: Wr.Dec<Bool>, p: LACoExact.coe.PB(s, d)) -> cse.RQ(s, FSrc.get_req.blank(d)):
  match d:
    case Wr.Got{+b, +s1}:
      cse.rq.marks(s, s1, b, p, Wr.get_list(~Nat, ~Wr.get_nat, s1), LACoExact.coe.nl.list(s1))
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and its numbers fit
def cse.req(+s: String) -> cse.RQ(s, FSrc.get_req(s)):
  cse.rq.top(s, Wr.get_bool(s), LACoExact.coe.pb(s))
