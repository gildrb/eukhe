# eukhe: lemmas of the proofs of area scan

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../base/logic/logic.bend as LLogicLogic
import ../../laws/scan.bend as Scan

def sc_fallback(+x: String, +x5: String, A: Maybe<&2, Sc.Order>, C: Maybe<&2, Sc.Cursor>, es: {x == Wr.put_nat(0n, Scan.spell_asked(A, Scan.spell_cursor(C, x5))) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x5) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSc.ffi.got(FSc.get_start.fallback(A, C, FSc.get_order(d)))) == False{} : Bool}) -> Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+t, +x6}:
      match t:
        case 0n:
          match x6:
            case SNil{}:
              (FSc.QStart{A, C, Sc.Asc{}}, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, Scan.spell_cursor(C, x5))), Wr.put_nat(0n, Scan.spell_asked(A, Scan.spell_cursor(C, Wr.put_nat(0n, x6)))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, Scan.spell_cursor(C, z))), x5, Wr.put_nat(0n, x6), Wire.wire_nat_exact(x5, 0n, x6, ed))))
            case SCon{h, r}:
              LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
        case 1n:
          match x6:
            case SNil{}:
              (FSc.QStart{A, C, Sc.Desc{}}, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, Scan.spell_cursor(C, x5))), Wr.put_nat(0n, Scan.spell_asked(A, Scan.spell_cursor(C, Wr.put_nat(1n, x6)))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, Scan.spell_cursor(C, z))), x5, Wr.put_nat(1n, x6), Wire.wire_nat_exact(x5, 1n, x6, ed))))
            case SCon{h, r}:
              LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
        case 2n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)

def sc_mark(+x: String, +x4: String, A: Maybe<&2, Sc.Order>, Af: Sc.After, es: {x == Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, x4)))) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x4) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSc.ffi.got(FSc.get_start.cursor(A, FSc.get_cursor.mark(Af, FSc.get_mark(d))))) == False{} : Bool}) -> Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+t, +x5}:
      match t:
        case 0n:
          sc_fallback(x, x5, A, Some{Sc.Cursor{Af, Sc.NoMark{}}}, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, x4)))), Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, Wr.put_nat(0n, x5))))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, z)))), x4, Wr.put_nat(0n, x5), Wire.wire_nat_exact(x4, 0n, x5, ed))), Wr.get_nat(x5), {==}, ok)
        case 1n:
          sc_fallback(x, x5, A, Some{Sc.Cursor{Af, Sc.AscMark{}}}, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, x4)))), Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, Wr.put_nat(1n, x5))))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, z)))), x4, Wr.put_nat(1n, x5), Wire.wire_nat_exact(x4, 1n, x5, ed))), Wr.get_nat(x5), {==}, ok)
        case 2n:
          sc_fallback(x, x5, A, Some{Sc.Cursor{Af, Sc.DescMark{}}}, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, x4)))), Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, Wr.put_nat(2n, x5))))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, z)))), x4, Wr.put_nat(2n, x5), Wire.wire_nat_exact(x4, 2n, x5, ed))), Wr.get_nat(x5), {==}, ok)
        case 3n:
          sc_fallback(x, x5, A, Some{Sc.Cursor{Af, Sc.BadMark{}}}, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, x4)))), Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, Wr.put_nat(3n, x5))))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Scan.spell_after(Af, z)))), x4, Wr.put_nat(3n, x5), Wire.wire_nat_exact(x4, 3n, x5, ed))), Wr.get_nat(x5), {==}, ok)
        case 4n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)

def sc_after(+x: String, +x3: String, A: Maybe<&2, Sc.Order>, es: {x == Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, x3))) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x3) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSc.ffi.got(FSc.get_start.cursor(A, FSc.get_cursor.after(FSc.get_after(d))))) == False{} : Bool}) -> Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+t, +x4}:
      match t:
        case 0n:
          sc_mark(x, x4, A, Sc.NoAfter{}, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, x3))), Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Wr.put_nat(0n, x4)))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, z))), x3, Wr.put_nat(0n, x4), Wire.wire_nat_exact(x3, 0n, x4, ed))), Wr.get_nat(x4), {==}, ok)
        case 1n:
          sc_mark(x, x4, A, Sc.BadAfter{}, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, x3))), Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Wr.put_nat(1n, x4)))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, z))), x3, Wr.put_nat(1n, x4), Wire.wire_nat_exact(x3, 1n, x4, ed))), Wr.get_nat(x4), {==}, ok)
        case 2n:
          sc_mark(x, x4, A, Sc.SafeAfter{}, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, x3))), Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, Wr.put_nat(2n, x4)))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, z))), x3, Wr.put_nat(2n, x4), Wire.wire_nat_exact(x3, 2n, x4, ed))), Wr.get_nat(x4), {==}, ok)
        case 3n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)

def sc_cursor(+x: String, +x2: String, A: Maybe<&2, Sc.Order>, es: {x == Wr.put_nat(0n, Scan.spell_asked(A, x2)) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x2) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSc.ffi.got(FSc.get_start.cursor(A, FSc.get_cursor(d)))) == False{} : Bool}) -> Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+t, +x3}:
      match t:
        case 0n:
          sc_fallback(x, x3, A, None{}, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, x2)), Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(0n, x3))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, z)), x2, Wr.put_nat(0n, x3), Wire.wire_nat_exact(x2, 0n, x3, ed))), Wr.get_nat(x3), {==}, ok)
        case 1n:
          sc_after(x, x3, A, Equal.trans(String, x, Wr.put_nat(0n, Scan.spell_asked(A, x2)), Wr.put_nat(0n, Scan.spell_asked(A, Wr.put_nat(1n, x3))), es, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(A, z)), x2, Wr.put_nat(1n, x3), Wire.wire_nat_exact(x2, 1n, x3, ed))), Wr.get_nat(x3), {==}, ok)
        case 2n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)

def sc_asked(+x: String, +x1: String, es: {x == Wr.put_nat(0n, x1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x1) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSc.ffi.got(FSc.get_start(FSc.get_asked(d)))) == False{} : Bool}) -> Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+t, +x2}:
      match t:
        case 0n:
          sc_cursor(x, x2, None{}, Equal.trans(String, x, Wr.put_nat(0n, x1), Wr.put_nat(0n, Wr.put_nat(0n, x2)), es, Equal.cong(String, String, z => Wr.put_nat(0n, z), x1, Wr.put_nat(0n, x2), Wire.wire_nat_exact(x1, 0n, x2, ed))), Wr.get_nat(x2), {==}, ok)
        case 1n:
          sc_cursor(x, x2, Some{Sc.Asc{}}, Equal.trans(String, x, Wr.put_nat(0n, x1), Wr.put_nat(0n, Wr.put_nat(1n, x2)), es, Equal.cong(String, String, z => Wr.put_nat(0n, z), x1, Wr.put_nat(1n, x2), Wire.wire_nat_exact(x1, 1n, x2, ed))), Wr.get_nat(x2), {==}, ok)
        case 2n:
          sc_cursor(x, x2, Some{Sc.Desc{}}, Equal.trans(String, x, Wr.put_nat(0n, x1), Wr.put_nat(0n, Wr.put_nat(2n, x2)), es, Equal.cong(String, String, z => Wr.put_nat(0n, z), x1, Wr.put_nat(2n, x2), Wire.wire_nat_exact(x1, 2n, x2, ed))), Wr.get_nat(x2), {==}, ok)
        case 3n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)

def sc_ida(+x: String, +x2: String, es: {x == Wr.put_nat(1n, Wr.put_nat(1n, x2)) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x2) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSc.ffi.got(FSc.get_id.after(FSc.get_after(d)))) == False{} : Bool}) -> Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+t, +x3}:
      match t:
        case 0n:
          match x3:
            case SNil{}:
              (FSc.QId{Some{Sc.NoAfter{}}}, Equal.trans(String, x, Wr.put_nat(1n, Wr.put_nat(1n, x2)), Wr.put_nat(1n, Wr.put_nat(1n, Wr.put_nat(0n, x3))), es, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(1n, z)), x2, Wr.put_nat(0n, x3), Wire.wire_nat_exact(x2, 0n, x3, ed))))
            case SCon{h, r}:
              LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
        case 1n:
          match x3:
            case SNil{}:
              (FSc.QId{Some{Sc.BadAfter{}}}, Equal.trans(String, x, Wr.put_nat(1n, Wr.put_nat(1n, x2)), Wr.put_nat(1n, Wr.put_nat(1n, Wr.put_nat(1n, x3))), es, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(1n, z)), x2, Wr.put_nat(1n, x3), Wire.wire_nat_exact(x2, 1n, x3, ed))))
            case SCon{h, r}:
              LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
        case 2n:
          match x3:
            case SNil{}:
              (FSc.QId{Some{Sc.SafeAfter{}}}, Equal.trans(String, x, Wr.put_nat(1n, Wr.put_nat(1n, x2)), Wr.put_nat(1n, Wr.put_nat(1n, Wr.put_nat(2n, x3))), es, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(1n, z)), x2, Wr.put_nat(2n, x3), Wire.wire_nat_exact(x2, 2n, x3, ed))))
            case SCon{h, r}:
              LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
        case 3n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)

def sc_idc(+x: String, +x1: String, es: {x == Wr.put_nat(1n, x1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x1) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSc.ffi.got(FSc.get_id(d))) == False{} : Bool}) -> Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+t, +x2}:
      match t:
        case 0n:
          match x2:
            case SNil{}:
              (FSc.QId{None{}}, Equal.trans(String, x, Wr.put_nat(1n, x1), Wr.put_nat(1n, Wr.put_nat(0n, x2)), es, Equal.cong(String, String, z => Wr.put_nat(1n, z), x1, Wr.put_nat(0n, x2), Wire.wire_nat_exact(x1, 0n, x2, ed))))
            case SCon{h, r}:
              LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
        case 1n:
          sc_ida(x, x2, Equal.trans(String, x, Wr.put_nat(1n, x1), Wr.put_nat(1n, Wr.put_nat(1n, x2)), es, Equal.cong(String, String, z => Wr.put_nat(1n, z), x1, Wr.put_nat(1n, x2), Wire.wire_nat_exact(x1, 1n, x2, ed))), Wr.get_nat(x2), {==}, ok)
        case 2n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)

def sc_ex(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSc.ffi.got(FSc.get_req(d))) == False{} : Bool}) -> Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+t, +x1}:
      match t:
        case 0n:
          sc_asked(x, x1, Wire.wire_nat_exact(x, 0n, x1, ed), Wr.get_nat(x1), {==}, ok)
        case 1n:
          sc_idc(x, x1, Wire.wire_nat_exact(x, 1n, x1, ed), Wr.get_nat(x1), {==}, ok)
        case 2n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FSc.Req, q => {x == Scan.spell_req(q, "") : String}>, ok)
