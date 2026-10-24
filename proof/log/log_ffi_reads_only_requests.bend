# eukhe: the proof of LAW log_ffi_reads_only_requests
#
# Each decoder layer that answers Got gives the prefix of the encoding
# (the wire's exactness laws): the length, the Maybe's tag, its index; a
# Bad layer, an unknown tag or input left over answers the error form,
# which the premise refutes.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nat_exact.bend as PWireNatExact

# nothing is left after the last newline m: s is the spelling
def pl.lastq(s2: String, +s: String, +n: Nat, -s1: String, +m: Maybe<&2, Nat>, ex: {s == Wr.put_nat(n, s1) : String}, ex1: {s1 == Log.log_spell_last(m, s2) : String}, ok: {LawsBase.wire_opens_err(FLg.ffi.end(Wr.end(s2), FLg.Req{n, m})) == False{} : Bool}) -> &len: Nat -> &last: Maybe<&2, Nat> -> {s == Log.log_spell_req(len, last) : String}:
  match s2:
    case SNil{}:
      (n, (m, (%ex1 : {s == Wr.put_nat(n, _) : String}; ex)))
    case SCon{c, t}:
      LLogicLogic.pt.absurd(&len: Nat -> &last: Maybe<&2, Nat> -> {s == Log.log_spell_req(len, last) : String}, ok)

# the index of a last newline (tag 1)
def pl.some(+s: String, +n: Nat, -s1: String, +s2: String, ex: {s == Wr.put_nat(n, s1) : String}, ex1: {s1 == Wr.put_nat(1n, s2) : String}, r: Wr.Dec<Nat>, er: {Wr.get_nat(s2) == r : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FLg.ffi.go(FLg.get_req.last(n, FLg.get_last.some(r)))) == False{} : Bool}) -> &len: Nat -> &last: Maybe<&2, Nat> -> {s == Log.log_spell_req(len, last) : String}:
  match r:
    case Wr.Got{+i, +s3}:
      +ex2 = Wire.wire_nat_exact(s2, i, s3, er)
      pl.lastq(s3, s, n, s1, Some{i}, ex, (%ex2 : {s1 == Wr.put_nat(1n, _) : String}; ex1), ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(&len: Nat -> &last: Maybe<&2, Nat> -> {s == Log.log_spell_req(len, last) : String}, ok)

# the tag of the last newline
def pl.tag(+s: String, +n: Nat, +s1: String, ex: {s == Wr.put_nat(n, s1) : String}, r: Wr.Dec<Nat>, er: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FLg.ffi.go(FLg.get_req.last(n, FLg.get_last.tag(r)))) == False{} : Bool}) -> &len: Nat -> &last: Maybe<&2, Nat> -> {s == Log.log_spell_req(len, last) : String}:
  match r:
    case Wr.Got{+t, +s2}:
      match t:
        case 0n:
          pl.lastq(s2, s, n, s1, None{}, ex, Wire.wire_nat_exact(s1, 0n, s2, er), ok)
        case 1n:
          pl.some(s, n, s1, s2, ex, Wire.wire_nat_exact(s1, 1n, s2, er), Wr.get_nat(s2), {==}, ok)
        case 2n+k:
          LLogicLogic.pt.absurd(&len: Nat -> &last: Maybe<&2, Nat> -> {s == Log.log_spell_req(len, last) : String}, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(&len: Nat -> &last: Maybe<&2, Nat> -> {s == Log.log_spell_req(len, last) : String}, ok)

# the length
def pl.req(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FLg.ffi.go(FLg.get_req.len(r))) == False{} : Bool}) -> &len: Nat -> &last: Maybe<&2, Nat> -> {s == Log.log_spell_req(len, last) : String}:
  match r:
    case Wr.Got{+n, +s1}:
      pl.tag(s, n, s1, Wire.wire_nat_exact(s, n, s1, er), Wr.get_nat(s1), {==}, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(&len: Nat -> &last: Maybe<&2, Nat> -> {s == Log.log_spell_req(len, last) : String}, ok)

def Log.log_ffi_reads_only_requests(s, ok):
  pl.req(s, Wr.get_nat(s), {==}, ok)
