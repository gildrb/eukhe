# eukhe: the proof of LAW scan_ffi_malformed_exact

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/scan.bend as Scan

# PROOF of LAW scan_ffi_malformed_exact: the code's decoder and the spec reader read the same
# numbers stage by stage (sc_bad and the stages below it); where the reader
# answers Bad (a missing field, an unknown tag) the decoder answers Bad and the
# entry the malformed error form; where it reads a whole request the premise
# is false (sc_got_bad).

# no request decodes to Bad: a contradiction
def sc_dec_if(d: Wr.Dec<FSc.Req>, G: Type) -> Type:
  match d:
    case Wr.Got{q, s}:
      Unit
    case Wr.Bad{}:
      G

def sc_got_bad(-q: FSc.Req, -s: String, -G: Type, e: {Wr.Got{q, s} == Wr.Bad{} : Wr.Dec<FSc.Req>}) -> G:
  %e : sc_dec_if(_, G)
  Unit{}

def sc_bad_fb(-A: Maybe<&2, Sc.Order>, -C: Maybe<&2, Sc.Cursor>, d: Wr.Dec<Nat>, no: {Scan.read_start.order(A, C, Scan.read_order(d)) == Wr.Bad{} : Wr.Dec<FSc.Req>}) -> {FSc.ffi.got(FSc.get_start.fallback(A, C, FSc.get_order(d))) == Wr.err("scan: malformed request") : String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sc_got_bad(FSc.QStart{A, C, Sc.Asc{}}, s, {FSc.ffi.got(FSc.get_start.fallback(A, C, FSc.get_order(Wr.Got{0n, s}))) == Wr.err("scan: malformed request") : String}, no)
        case 1n:
          sc_got_bad(FSc.QStart{A, C, Sc.Desc{}}, s, {FSc.ffi.got(FSc.get_start.fallback(A, C, FSc.get_order(Wr.Got{1n, s}))) == Wr.err("scan: malformed request") : String}, no)
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sc_bad_mark(-A: Maybe<&2, Sc.Order>, -Af: Sc.After, d: Wr.Dec<Nat>, no: {Scan.read_start.cursor(A, Scan.read_cursor.mark(Af, Scan.read_mark(d))) == Wr.Bad{} : Wr.Dec<FSc.Req>}) -> {FSc.ffi.got(FSc.get_start.cursor(A, FSc.get_cursor.mark(Af, FSc.get_mark(d)))) == Wr.err("scan: malformed request") : String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sc_bad_fb(A, Some{Sc.Cursor{Af, Sc.NoMark{}}}, Wr.get_nat(s), no)
        case 1n:
          sc_bad_fb(A, Some{Sc.Cursor{Af, Sc.AscMark{}}}, Wr.get_nat(s), no)
        case 2n:
          sc_bad_fb(A, Some{Sc.Cursor{Af, Sc.DescMark{}}}, Wr.get_nat(s), no)
        case 3n:
          sc_bad_fb(A, Some{Sc.Cursor{Af, Sc.BadMark{}}}, Wr.get_nat(s), no)
        case 4n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sc_bad_after(-A: Maybe<&2, Sc.Order>, d: Wr.Dec<Nat>, no: {Scan.read_start.cursor(A, Scan.read_cursor.after(Scan.read_after(d))) == Wr.Bad{} : Wr.Dec<FSc.Req>}) -> {FSc.ffi.got(FSc.get_start.cursor(A, FSc.get_cursor.after(FSc.get_after(d)))) == Wr.err("scan: malformed request") : String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sc_bad_mark(A, Sc.NoAfter{}, Wr.get_nat(s), no)
        case 1n:
          sc_bad_mark(A, Sc.BadAfter{}, Wr.get_nat(s), no)
        case 2n:
          sc_bad_mark(A, Sc.SafeAfter{}, Wr.get_nat(s), no)
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sc_bad_cursor(-A: Maybe<&2, Sc.Order>, d: Wr.Dec<Nat>, no: {Scan.read_start.cursor(A, Scan.read_cursor(d)) == Wr.Bad{} : Wr.Dec<FSc.Req>}) -> {FSc.ffi.got(FSc.get_start.cursor(A, FSc.get_cursor(d))) == Wr.err("scan: malformed request") : String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sc_bad_fb(A, None{}, Wr.get_nat(s), no)
        case 1n:
          sc_bad_after(A, Wr.get_nat(s), no)
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sc_bad_asked(d: Wr.Dec<Nat>, no: {Scan.read_start(Scan.read_asked(d)) == Wr.Bad{} : Wr.Dec<FSc.Req>}) -> {FSc.ffi.got(FSc.get_start(FSc.get_asked(d))) == Wr.err("scan: malformed request") : String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sc_bad_cursor(None{}, Wr.get_nat(s), no)
        case 1n:
          sc_bad_cursor(Some{Sc.Asc{}}, Wr.get_nat(s), no)
        case 2n:
          sc_bad_cursor(Some{Sc.Desc{}}, Wr.get_nat(s), no)
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sc_bad_ida(d: Wr.Dec<Nat>, no: {Scan.read_id.after(Scan.read_after(d)) == Wr.Bad{} : Wr.Dec<FSc.Req>}) -> {FSc.ffi.got(FSc.get_id.after(FSc.get_after(d))) == Wr.err("scan: malformed request") : String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sc_got_bad(FSc.QId{Some{Sc.NoAfter{}}}, s, {FSc.ffi.got(FSc.get_id.after(FSc.get_after(Wr.Got{0n, s}))) == Wr.err("scan: malformed request") : String}, no)
        case 1n:
          sc_got_bad(FSc.QId{Some{Sc.BadAfter{}}}, s, {FSc.ffi.got(FSc.get_id.after(FSc.get_after(Wr.Got{1n, s}))) == Wr.err("scan: malformed request") : String}, no)
        case 2n:
          sc_got_bad(FSc.QId{Some{Sc.SafeAfter{}}}, s, {FSc.ffi.got(FSc.get_id.after(FSc.get_after(Wr.Got{2n, s}))) == Wr.err("scan: malformed request") : String}, no)
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sc_bad_id(d: Wr.Dec<Nat>, no: {Scan.read_id(d) == Wr.Bad{} : Wr.Dec<FSc.Req>}) -> {FSc.ffi.got(FSc.get_id(d)) == Wr.err("scan: malformed request") : String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sc_got_bad(FSc.QId{None{}}, s, {FSc.ffi.got(FSc.get_id(Wr.Got{0n, s})) == Wr.err("scan: malformed request") : String}, no)
        case 1n:
          sc_bad_ida(Wr.get_nat(s), no)
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sc_bad(d: Wr.Dec<Nat>, no: {Scan.read_spec.tag(d) == Wr.Bad{} : Wr.Dec<FSc.Req>}) -> {FSc.ffi.got(FSc.get_req(d)) == Wr.err("scan: malformed request") : String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sc_bad_asked(Wr.get_nat(s), no)
        case 1n:
          sc_bad_id(Wr.get_nat(s), no)
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def Scan.scan_ffi_malformed_exact(s, no):
  sc_bad(Wr.get_nat(s), no)
