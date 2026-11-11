# eukhe: the proof of LAW scan_ffi_malformed_unless_request
#
# PROOF: each decoder stage answers a value only for an input that spells
# it before the rest (wire_nat_exact; scm.* carry the spelled prefix stage
# by stage); when the decoder reads no request the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/scan.bend as Scan
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../base/staging.bend as LStg

def scm.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String}
    case Wr.Bad{}:
      Unit

def scm.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> scm.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      Wire.wire_nat_exact(s, n, r, ed)
    case Wr.Bad{}:
      Unit{}

def scm.nat(+s: String) -> scm.NP(s, Wr.get_nat(s)):
  scm.nat.at(s, Wr.get_nat(s), {==})

def scm.AfterP(s: String, d: Wr.Dec<Sc.After>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Scan.spell_after(x, r) : String}
    case Wr.Bad{}:
      Unit

def scm.after(-s: String, d: Wr.Dec<Nat>, np: scm.NP(s, d)) -> scm.AfterP(s, FSc.get_after(d)):
  match d:
    case Wr.Got{t, r}:
      match t:
        case 0n:
          np
        case 1n:
          np
        case 2n:
          np
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def scm.MarkP(s: String, d: Wr.Dec<Sc.Mark>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Scan.spell_mark(x, r) : String}
    case Wr.Bad{}:
      Unit

def scm.mark(-s: String, d: Wr.Dec<Nat>, np: scm.NP(s, d)) -> scm.MarkP(s, FSc.get_mark(d)):
  match d:
    case Wr.Got{t, r}:
      match t:
        case 0n:
          np
        case 1n:
          np
        case 2n:
          np
        case 3n:
          np
        case 4n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def scm.OrderP(s: String, d: Wr.Dec<Sc.Order>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Scan.spell_order(x, r) : String}
    case Wr.Bad{}:
      Unit

def scm.order(-s: String, d: Wr.Dec<Nat>, np: scm.NP(s, d)) -> scm.OrderP(s, FSc.get_order(d)):
  match d:
    case Wr.Got{t, r}:
      match t:
        case 0n:
          np
        case 1n:
          np
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def scm.AskedP(s: String, d: Wr.Dec<Maybe<&2, Sc.Order>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Scan.spell_asked(x, r) : String}
    case Wr.Bad{}:
      Unit

def scm.asked(-s: String, d: Wr.Dec<Nat>, np: scm.NP(s, d)) -> scm.AskedP(s, FSc.get_asked(d)):
  match d:
    case Wr.Got{t, r}:
      match t:
        case 0n:
          np
        case 1n:
          np
        case 2n:
          np
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def scm.CursorP(s: String, d: Wr.Dec<Maybe<&2, Sc.Cursor>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Scan.spell_cursor(x, r) : String}
    case Wr.Bad{}:
      Unit

def scm.ReqP(s: String, d: Wr.Dec<FSc.Req>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Scan.spell_req(x, r) : String}
    case Wr.Bad{}:
      Unit

# the cursor: its `after`, then its `order`
def scm.cursor.mark(-s: String, +a: Sc.After, -s2: String, pre: {s == Wr.put_nat(1n, Scan.spell_after(a, s2)) : String}, d: Wr.Dec<Sc.Mark>, mp: scm.MarkP(s2, d)) -> scm.CursorP(s, FSc.get_cursor.mark(a, d)):
  match d:
    case Wr.Got{+m, +r}:
      Equal.trans(String, s, Wr.put_nat(1n, Scan.spell_after(a, s2)), Wr.put_nat(1n, Scan.spell_after(a, Scan.spell_mark(m, r))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Scan.spell_after(a, z)), s2, Scan.spell_mark(m, r), mp))
    case Wr.Bad{}:
      Unit{}

def scm.cursor.after(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Sc.After>, ap: scm.AfterP(s1, d)) -> scm.CursorP(s, FSc.get_cursor.after(d)):
  match d:
    case Wr.Got{+a, +r}:
      scm.cursor.mark(s, a, r, Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Scan.spell_after(a, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Scan.spell_after(a, r), ap)), FSc.get_mark(Wr.get_nat(r)), scm.mark(r, Wr.get_nat(r), scm.nat(r)))
    case Wr.Bad{}:
      Unit{}

def scm.cursor(-s: String, d: Wr.Dec<Nat>, np: scm.NP(s, d)) -> scm.CursorP(s, FSc.get_cursor(d)):
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          np
        case 1n:
          scm.cursor.after(s, r, np, FSc.get_after(Wr.get_nat(r)), scm.after(r, Wr.get_nat(r), scm.nat(r)))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a start: the order asked, the cursor, the default order
def scm.start.fallback(-s: String, +asked: Maybe<&2, Sc.Order>, +c: Maybe<&2, Sc.Cursor>, -s3: String, pre: {s == Wr.put_nat(0n, Scan.spell_asked(asked, Scan.spell_cursor(c, s3))) : String}, d: Wr.Dec<Sc.Order>, op: scm.OrderP(s3, d)) -> scm.ReqP(s, FSc.get_start.fallback(asked, c, d)):
  match d:
    case Wr.Got{+f, +r}:
      Equal.trans(String, s, Wr.put_nat(0n, Scan.spell_asked(asked, Scan.spell_cursor(c, s3))), Wr.put_nat(0n, Scan.spell_asked(asked, Scan.spell_cursor(c, Scan.spell_order(f, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(asked, Scan.spell_cursor(c, z))), s3, Scan.spell_order(f, r), op))
    case Wr.Bad{}:
      Unit{}

def scm.start.cursor(-s: String, +asked: Maybe<&2, Sc.Order>, -s2: String, pre: {s == Wr.put_nat(0n, Scan.spell_asked(asked, s2)) : String}, d: Wr.Dec<Maybe<&2, Sc.Cursor>>, cp: scm.CursorP(s2, d)) -> scm.ReqP(s, FSc.get_start.cursor(asked, d)):
  match d:
    case Wr.Got{+c, +r}:
      scm.start.fallback(s, asked, c, r, Equal.trans(String, s, Wr.put_nat(0n, Scan.spell_asked(asked, s2)), Wr.put_nat(0n, Scan.spell_asked(asked, Scan.spell_cursor(c, r))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Scan.spell_asked(asked, z)), s2, Scan.spell_cursor(c, r), cp)), FSc.get_order(Wr.get_nat(r)), scm.order(r, Wr.get_nat(r), scm.nat(r)))
    case Wr.Bad{}:
      Unit{}

def scm.start(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Maybe<&2, Sc.Order>>, ap: scm.AskedP(s1, d)) -> scm.ReqP(s, FSc.get_start(d)):
  match d:
    case Wr.Got{+asked, +r}:
      scm.start.cursor(s, asked, r, Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Scan.spell_asked(asked, r)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Scan.spell_asked(asked, r), ap)), FSc.get_cursor(Wr.get_nat(r)), scm.cursor(r, Wr.get_nat(r), scm.nat(r)))
    case Wr.Bad{}:
      Unit{}

# a cursor id: the cursor, then its `after`
def scm.id.after(-s: String, -s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(1n, s2)) : String}, d: Wr.Dec<Sc.After>, ap: scm.AfterP(s2, d)) -> scm.ReqP(s, FSc.get_id.after(d)):
  match d:
    case Wr.Got{+a, +r}:
      Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(1n, s2)), Wr.put_nat(1n, Wr.put_nat(1n, Scan.spell_after(a, r))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(1n, z)), s2, Scan.spell_after(a, r), ap))
    case Wr.Bad{}:
      Unit{}

def scm.id(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, np: scm.NP(s1, d)) -> scm.ReqP(s, FSc.get_id(d)):
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(0n, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(0n, r), np))
        case 1n:
          scm.id.after(s, r, Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(1n, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(1n, r), np)), FSc.get_after(Wr.get_nat(r)), scm.after(r, Wr.get_nat(r), scm.nat(r)))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def scm.req(-s: String, d: Wr.Dec<Nat>, np: scm.NP(s, d)) -> scm.ReqP(s, FSc.get_req(d)):
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          scm.start(s, r, np, FSc.get_asked(Wr.get_nat(r)), scm.asked(r, Wr.get_nat(r), scm.nat(r)))
        case 1n:
          scm.id(s, r, np, Wr.get_nat(r), scm.nat(r))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# The entry
# ---------

def scm.goal(+s: String) -> Type:
  &q: FSc.Req -> &rest: String -> {s == Scan.spell_req(q, rest) : String}

def scm.main(+s: String, d: Wr.Dec<FSc.Req>, qp: scm.ReqP(s, d), other: {String.eq(FSc.ffi.got(d), Wr.err("scan: malformed request")) == False{} : Bool}) -> scm.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (q, (rest, qp))
    case Wr.Bad{}:
      LStg.stg.absurd(scm.goal(s), other)

def Scan.scan_ffi_malformed_unless_request(s, other):
  scm.main(s, FSc.get_req(Wr.get_nat(s)), scm.req(s, Wr.get_nat(s), scm.nat(s)), other)
