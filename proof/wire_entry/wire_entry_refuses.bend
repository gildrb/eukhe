# eukhe: the proof of LAW wire_entry_refuses
#
# PROOF: the entry answers either the values written again, which open with
# a Nat (never 'E': wire_nat_not_err), or the one error form; so an answer
# that opens with 'E' is that error form. Stage by stage, as the entry reads.

import Base
import ../../bend/ffi_wire.bend as FW
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/wire_entry.bend as WireEntry
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ./base.bend as LAWireEntry

def wer.end(d: Wr.Dec<List<&2, Nat>>, +n: Nat, +x: U32, +b: Bool, +a: String, bad: {LawsBase.wire_opens_err(FW.at.end(d, n, x, b, a)) == True{} : Bool}) ->
  {FW.at.end(d, n, x, b, a) == Wr.err("malformed wire request") : String}:
  match d:
    case Wr.Got{+xs, s}:
      match s:
        case SNil{}:
          +v = Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""))))
          LAWireEntry.web.absurd({Wr.put_nat(n, v) == Wr.err("malformed wire request") : String},
            Equal.trans(Bool, False{}, LawsBase.wire_opens_err(Wr.put_nat(n, v)), True{},
              Equal.sym(Bool, LawsBase.wire_opens_err(Wr.put_nat(n, v)), False{}, Wire.wire_nat_not_err(n, v)), bad))
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def wer.str(d: Wr.Dec<String>, +n: Nat, +x: U32, +b: Bool, bad: {LawsBase.wire_opens_err(FW.at.str(d, n, x, b)) == True{} : Bool}) ->
  {FW.at.str(d, n, x, b) == Wr.err("malformed wire request") : String}:
  match d:
    case Wr.Got{+a, s}:
      wer.end(Wr.get_list(~Nat, ~Wr.get_nat, s), n, x, b, a, bad)
    case Wr.Bad{}:
      {==}

def wer.bool(d: Wr.Dec<Bool>, +n: Nat, +x: U32, bad: {LawsBase.wire_opens_err(FW.at.bool(d, n, x)) == True{} : Bool}) ->
  {FW.at.bool(d, n, x) == Wr.err("malformed wire request") : String}:
  match d:
    case Wr.Got{+b, s}:
      wer.str(Wr.get_str(s), n, x, b, bad)
    case Wr.Bad{}:
      {==}

def wer.u32(d: Wr.Dec<U32>, +n: Nat, bad: {LawsBase.wire_opens_err(FW.at.u32(d, n)) == True{} : Bool}) ->
  {FW.at.u32(d, n) == Wr.err("malformed wire request") : String}:
  match d:
    case Wr.Got{+x, s}:
      wer.bool(Wr.get_bool(s), n, x, bad)
    case Wr.Bad{}:
      {==}

def wer.nat(d: Wr.Dec<Nat>, bad: {LawsBase.wire_opens_err(FW.at.nat(d)) == True{} : Bool}) ->
  {FW.at.nat(d) == Wr.err("malformed wire request") : String}:
  match d:
    case Wr.Got{+n, s}:
      wer.u32(Wr.get_u32(s), n, bad)
    case Wr.Bad{}:
      {==}

def WireEntry.wire_entry_refuses(s, bad):
  wer.nat(Wr.get_nat(s), bad)
