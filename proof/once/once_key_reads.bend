# eukhe: the proof of LAW once_key_reads
#
# PROOF: an input the laws' reader reads as the scope a and the id b is
# a spelled before b spelled (Wire.wire_str_exact, twice): the spelled
# request itself.

import Base
import ../../bend/ffi_once.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/once.bend as Once
import ../../laws/wire.bend as Wire
import ../wire/wire_str_exact.bend as PWireStrExact
import ./base.bend as LA

def or.scope_of(k: Once.OnKey) -> String:
  match k:
    case Once.OnKey{a, b}:
      a

def or.id_of(k: Once.OnKey) -> String:
  match k:
    case Once.OnKey{a, b}:
      b

def or.spelled(-s: String, -x: String, -b: String, e: {s == Wr.put_str(x, "") : String}, xb: {x == b : String}) -> {s == Wr.put_str(b, "") : String}:
  %xb : {s == Wr.put_str(_, "") : String}
  e

def or.join(-i: String, -a0: String, -s: String, -a: String, -b: String, e: {i == Wr.put_str(a0, s) : String}, p: {a0 == a : String} & {s == Wr.put_str(b, "") : String}) -> {i == Wr.put_str(a, Wr.put_str(b, "")) : String}:
  (ea, es) = p
  %es : {i == Wr.put_str(a, _) : String}
  %ea : {i == Wr.put_str(_, s) : String}
  e

# the string after the scope is the id spelled, and the scope read is
# the scope asked
def or.id(+a0: String, +s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}, +a: String, +b: String, +got: {Once.on_read_key.id(a0, d) == Some{Once.OnKey{a, b}} : Maybe<&2, Once.OnKey>}) -> ({a0 == a : String} & {s == Wr.put_str(b, "") : String}):
  match d:
    case Wr.Got{+x, rest}:
      match rest:
        case SNil{}:
          (Equal.cong(Once.OnKey, String, k => or.scope_of(k), Once.OnKey{a0, x}, Once.OnKey{a, b}, LA.ob.some_inj(Once.OnKey, Once.OnKey{a0, x}, Once.OnKey{a, b}, got)), or.spelled(s, x, b, Wire.wire_str_exact(s, x, "", ed), Equal.cong(Once.OnKey, String, k => or.id_of(k), Once.OnKey{a0, x}, Once.OnKey{a, b}, LA.ob.some_inj(Once.OnKey, Once.OnKey{a0, x}, Once.OnKey{a, b}, got))))
        case SCon{h, t}:
          LA.ob.none_some(Once.OnKey, ({a0 == a : String} & {s == Wr.put_str(b, "") : String}), Once.OnKey{a, b}, got)
    case Wr.Bad{}:
      LA.ob.none_some(Once.OnKey, ({a0 == a : String} & {s == Wr.put_str(b, "") : String}), Once.OnKey{a, b}, got)

# an input the laws' reader reads as a and b is the request spelled
def or.scope(+i: String, d: Wr.Dec<String>, ed: {Wr.get_str(i) == d : Wr.Dec<String>}, +a: String, +b: String, got: {Once.on_read_key.scope(d) == Some{Once.OnKey{a, b}} : Maybe<&2, Once.OnKey>}) -> {i == Once.on_spell_key(a, b) : String}:
  match d:
    case Wr.Got{+a0, +s}:
      or.join(i, a0, s, a, b, Wire.wire_str_exact(i, a0, s, ed), or.id(a0, s, Wr.get_str(s), {==}, a, b, got))
    case Wr.Bad{}:
      LA.ob.none_some(Once.OnKey, {i == Once.on_spell_key(a, b) : String}, Once.OnKey{a, b}, got)

def Once.once_key_reads(i, a, b, got):
  Equal.cong(String, String, x => FO.ffi(x), i, Once.on_spell_key(a, b), or.scope(i, Wr.get_str(i), {==}, a, b, got))
