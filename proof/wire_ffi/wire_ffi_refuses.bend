# eukhe: the proof of LAW wire_ffi_refuses
#
# PROOF: the entry answers either the request written again, which opens
# with a Nat (never 'E': wire_nat_not_err), or the one error form; so an
# answer that opens with 'E' is that error form.

import Base
import ../../bend/ffi_wire.bend as FWi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/wire_ffi.bend as WireFfi
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/base/spell.bend as LAWireSpell

def wf.end(+n: Nat, +x: U32, +b: Bool, +a: String, d: Wr.Dec<List<&2, Nat>>, bad: {LawsBase.wire_opens_err(FWi.at.end(d, n, x, b, a)) == True{} : Bool}) -> {FWi.at.end(d, n, x, b, a) == Wr.err("malformed wire request") : String}:
  match d:
    case Wr.Got{+xs, rest}:
      match rest:
        case SNil{}:
          +r1 = Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""))))
          LAWireSpell.ws_absurd({Wr.put_nat(n, r1) == Wr.err("malformed wire request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(Wr.put_nat(n, r1)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(Wr.put_nat(n, r1)), True{}, bad), Wire.wire_nat_not_err(n, r1)))
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def wf.str(+n: Nat, +x: U32, +b: Bool, d: Wr.Dec<String>, bad: {LawsBase.wire_opens_err(FWi.at.str(d, n, x, b)) == True{} : Bool}) -> {FWi.at.str(d, n, x, b) == Wr.err("malformed wire request") : String}:
  match d:
    case Wr.Got{+a, s}:
      wf.end(n, x, b, a, Wr.get_list(~Nat, ~Wr.get_nat, s), bad)
    case Wr.Bad{}:
      {==}

def wf.bool(+n: Nat, +x: U32, d: Wr.Dec<Bool>, bad: {LawsBase.wire_opens_err(FWi.at.bool(d, n, x)) == True{} : Bool}) -> {FWi.at.bool(d, n, x) == Wr.err("malformed wire request") : String}:
  match d:
    case Wr.Got{+b, s}:
      wf.str(n, x, b, Wr.get_str(s), bad)
    case Wr.Bad{}:
      {==}

def wf.u32(+n: Nat, d: Wr.Dec<U32>, bad: {LawsBase.wire_opens_err(FWi.at.u32(d, n)) == True{} : Bool}) -> {FWi.at.u32(d, n) == Wr.err("malformed wire request") : String}:
  match d:
    case Wr.Got{+x, s}:
      wf.bool(n, x, Wr.get_bool(s), bad)
    case Wr.Bad{}:
      {==}

def wf.nat(d: Wr.Dec<Nat>, bad: {LawsBase.wire_opens_err(FWi.at.nat(d)) == True{} : Bool}) -> {FWi.at.nat(d) == Wr.err("malformed wire request") : String}:
  match d:
    case Wr.Got{+n, s}:
      wf.u32(n, Wr.get_u32(s), bad)
    case Wr.Bad{}:
      {==}

def WireFfi.wire_ffi_refuses(s, bad):
  wf.nat(Wr.get_nat(s), bad)
