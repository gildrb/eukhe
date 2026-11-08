# eukhe: the proof of LAW wire_entry_exact
#
# PROOF: the entry answers a value only when each field decodes and nothing
# is left. Each decoded field is exactly its encoding before the rest
# (wire_nat_exact, wire_u32_exact, wire_bool_exact, wire_str_exact,
# wire_list_exact), which is the spec's spelling (wire_nat_decimal,
# wire_u32_decimal, wire_bool_spelled, wire_str_decimal,
# wire_nats_decimal), and fits the wire (wire_nat_decoded_fits,
# wire_str_decoded_fits; the list: web.list_fits, from
# wire_list_reads_items and wire_nat_decoded_fits). Stage by stage, as the
# entry reads, s is the spelling of the fields read so far before the rest.

import Base
import ../../bend/ffi_wire.bend as FW
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/wire_entry.bend as WireEntry
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_u32_exact.bend as PWireU32Exact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_list_exact.bend as PWireListExact
import ../wire/wire_nat_decimal.bend as PWireNatDecimal
import ../wire/wire_u32_decimal.bend as PWireU32Decimal
import ../wire/wire_bool_spelled.bend as PWireBoolSpelled
import ../wire/wire_str_decimal.bend as PWireStrDecimal
import ../wire/wire_nats_decimal.bend as PWireNatsDecimal
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ./base.bend as LAWireEntry

def wex.Goal(s: String) -> Type:
  Sigma<&1, &1, Nat, n => Sigma<&1, &1, U32, x => Sigma<&1, &1, Bool, b => Sigma<&1, &1, String, a => Sigma<&1, &1, List<&2, Nat>, xs =>
    {s == WireEntry.wire_entry_spell(n, x, b, a, xs, "") : String} & {WireEntry.wire_entry_fits(n, a, xs) == True{} : Bool}>>>>>

# the spelling of n, x, b, a before t
def wex.pre(+n: Nat, +x: U32, b: Bool, a: String, t: String) -> String:
  LawsBase.wire_dec(n, LawsBase.wire_dec(U32.to_nat(x), SCon{LawsBase.wire_bool_char(b), LawsBase.wire_dec_str(a, t)}))

# the error form opens with 'E'
def wex.no(-s: String, ok: {LawsBase.wire_opens_err(FW.bad()) == False{} : Bool}) -> wex.Goal(s):
  LAWireEntry.web.absurd(wex.Goal(s), Equal.sym(Bool, True{}, False{}, ok))

# the list, then nothing left
def wex.l(-s: String, +n: Nat, +x: U32, +b: Bool, +a: String, +s4: String,
  e: {s == wex.pre(n, x, b, a, s4) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}, fa: {LawsBase.wire_fits(String.length(a)) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s4) == d : Wr.Dec<List<&2, Nat>>},
  ok: {LawsBase.wire_opens_err(FW.at.end(d, n, x, b, a)) == False{} : Bool}) -> wex.Goal(s):
  match d:
    case Wr.Got{+xs, s5}:
      match s5:
        case SNil{}:
          +h = ed
          +e5 = Equal.trans(String, s4, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""), LawsBase.wire_dec_nats(xs, ""),
            Wire.wire_list_exact(s4, xs, "", h), Wire.wire_nats_decimal(xs, ""))
          +eq = Equal.trans(String, s, wex.pre(n, x, b, a, s4), wex.pre(n, x, b, a, LawsBase.wire_dec_nats(xs, "")), e,
            Equal.cong(String, String, z => wex.pre(n, x, b, a, z), s4, LawsBase.wire_dec_nats(xs, ""), e5))
          +fl = LAWireEntry.web.list_fits(s4, xs, "", h)
          +ft = LAWireEntry.web.and_tt(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), fa, fl)
          (n, (x, (b, (a, (xs, (eq, LAWireEntry.web.and_tt(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))), fn, ft)))))))
        case SCon{c, t}:
          wex.no(s, ok)
    case Wr.Bad{}:
      wex.no(s, ok)

# the string
def wex.a(-s: String, +n: Nat, +x: U32, +b: Bool, +s3: String,
  e: {s == LawsBase.wire_dec(n, LawsBase.wire_dec(U32.to_nat(x), SCon{LawsBase.wire_bool_char(b), s3})) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool},
  d: Wr.Dec<String>, ed: {Wr.get_str(s3) == d : Wr.Dec<String>},
  ok: {LawsBase.wire_opens_err(FW.at.str(d, n, x, b)) == False{} : Bool}) -> wex.Goal(s):
  match d:
    case Wr.Got{+a, +s4}:
      +h = ed
      +e4 = Equal.trans(String, s3, Wr.put_str(a, s4), LawsBase.wire_dec_str(a, s4),
        Wire.wire_str_exact(s3, a, s4, h), Wire.wire_str_decimal(a, s4))
      +eq = Equal.trans(String, s, LawsBase.wire_dec(n, LawsBase.wire_dec(U32.to_nat(x), SCon{LawsBase.wire_bool_char(b), s3})), wex.pre(n, x, b, a, s4), e,
        Equal.cong(String, String, z => LawsBase.wire_dec(n, LawsBase.wire_dec(U32.to_nat(x), SCon{LawsBase.wire_bool_char(b), z})), s3, LawsBase.wire_dec_str(a, s4), e4))
      wex.l(s, n, x, b, a, s4, eq, fn, Wire.wire_str_decoded_fits(s3, a, s4, h), Wr.get_list(~Nat, ~Wr.get_nat, s4), {==}, ok)
    case Wr.Bad{}:
      wex.no(s, ok)

# the Bool
def wex.b(-s: String, +n: Nat, +x: U32, +s2: String,
  e: {s == LawsBase.wire_dec(n, LawsBase.wire_dec(U32.to_nat(x), s2)) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool},
  d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>},
  ok: {LawsBase.wire_opens_err(FW.at.bool(d, n, x)) == False{} : Bool}) -> wex.Goal(s):
  match d:
    case Wr.Got{+b, +s3}:
      +e3 = Equal.trans(String, s2, Wr.put_bool(b, s3), SCon{LawsBase.wire_bool_char(b), s3},
        Wire.wire_bool_exact(s2, b, s3, ed), Wire.wire_bool_spelled(b, s3))
      +eq = Equal.trans(String, s, LawsBase.wire_dec(n, LawsBase.wire_dec(U32.to_nat(x), s2)), LawsBase.wire_dec(n, LawsBase.wire_dec(U32.to_nat(x), SCon{LawsBase.wire_bool_char(b), s3})), e,
        Equal.cong(String, String, z => LawsBase.wire_dec(n, LawsBase.wire_dec(U32.to_nat(x), z)), s2, SCon{LawsBase.wire_bool_char(b), s3}, e3))
      wex.a(s, n, x, b, s3, eq, fn, Wr.get_str(s3), {==}, ok)
    case Wr.Bad{}:
      wex.no(s, ok)

# the U32
def wex.u(-s: String, +n: Nat, +s1: String,
  e: {s == LawsBase.wire_dec(n, s1) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool},
  d: Wr.Dec<U32>, ed: {Wr.get_u32(s1) == d : Wr.Dec<U32>},
  ok: {LawsBase.wire_opens_err(FW.at.u32(d, n)) == False{} : Bool}) -> wex.Goal(s):
  match d:
    case Wr.Got{+x, +s2}:
      +e2 = Equal.trans(String, s1, Wr.put_u32(x, s2), LawsBase.wire_dec(U32.to_nat(x), s2),
        Wire.wire_u32_exact(s1, x, s2, ed), Wire.wire_u32_decimal(x, s2))
      +eq = Equal.trans(String, s, LawsBase.wire_dec(n, s1), LawsBase.wire_dec(n, LawsBase.wire_dec(U32.to_nat(x), s2)), e,
        Equal.cong(String, String, z => LawsBase.wire_dec(n, z), s1, LawsBase.wire_dec(U32.to_nat(x), s2), e2))
      wex.b(s, n, x, s2, eq, fn, Wr.get_bool(s2), {==}, ok)
    case Wr.Bad{}:
      wex.no(s, ok)

# the Nat
def wex.n(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>},
  ok: {LawsBase.wire_opens_err(FW.at.nat(d)) == False{} : Bool}) -> wex.Goal(s):
  match d:
    case Wr.Got{+n, +s1}:
      +h = ed
      +e1 = Equal.trans(String, s, Wr.put_nat(n, s1), LawsBase.wire_dec(n, s1),
        Wire.wire_nat_exact(s, n, s1, h), Wire.wire_nat_decimal(n, s1))
      wex.u(s, n, s1, e1, Wire.wire_nat_decoded_fits(s, n, s1, h), Wr.get_u32(s1), {==}, ok)
    case Wr.Bad{}:
      wex.no(s, ok)

def WireEntry.wire_entry_exact(s, ok):
  wex.n(s, Wr.get_nat(s), {==}, ok)
