# eukhe: the laws of area scan

import Base
import ../bend/scan.bend as Sc
import ../bend/ffi_scan.bend as FSc
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1): where a built-in storage scan starts (bend/scan.bend, the
# port of pi-durable `storage/scan.ts` and the backends' `cursorId`). Each
# law is an open claim about Sc.start or Sc.cursor_id; PROOF.bend proves
# them (as Scan.<law>) with the lemmas of proof/scan/.
#
# R1: without a cursor a scan starts at the beginning, in the order the
#     query asks for, else in the scan's default order.
# R2: a cursor continues after its `after` id, in the order it was written
#     with (`order` "ascending" or "descending"); a cursor without an
#     `order` (written before scans had one) in the scan's default order.
# R3: a cursor whose `after` is absent or not a safe integer, or whose
#     `order` is anything but absent, "ascending" or "descending", is
#     refused: "Invalid storage cursor".
# R4: a query that asks for another order than its cursor's is refused:
#     "The cursor continues a <order> scan; the query asks for <asked>".
# R5: a backend's cursor id: none without a cursor or without `after`; the
#     id when `after` is a safe integer; else "Invalid storage cursor".
# Every query, cursor and default order is free.

# Terms
# -----

def asc_spec() -> String:
  "ascending"

def desc_spec() -> String:
  "descending"

def name_spec(o: Sc.Order) -> String:
  match o:
    case Sc.Asc{}:
      asc_spec()
    case Sc.Desc{}:
      desc_spec()

def invalid_spec() -> String:
  "Invalid storage cursor"

def mismatch_spec(o: Sc.Order, a: Sc.Order) -> String:
  String.concat(["The cursor continues a ", name_spec(o), " scan; the query asks for ", name_spec(a)])

# the order a cursor was written with, if it names one; else a bad mark
def mark_order_spec(m: Sc.Mark, fallback: Sc.Order) -> Maybe<&2, Sc.Order>:
  match m:
    case Sc.NoMark{}:
      Some{fallback}
    case Sc.AscMark{}:
      Some{Sc.Asc{}}
    case Sc.DescMark{}:
      Some{Sc.Desc{}}
    case Sc.BadMark{}:
      None{}

def eq_spec(a: Sc.Order, b: Sc.Order) -> Bool:
  match a b:
    case Sc.Asc{} Sc.Asc{}:
      True{}
    case Sc.Asc{} Sc.Desc{}:
      False{}
    case Sc.Desc{} Sc.Asc{}:
      False{}
    case Sc.Desc{} Sc.Desc{}:
      True{}

def go_on_spec.cmp(b: Bool, +o: Sc.Order, +a: Sc.Order) -> Sc.Start:
  match b:
    case True{}:
      Sc.Begin{o, True{}}
    case False{}:
      Sc.Refuse{mismatch_spec(o, a)}

# a cursor of order o goes on, unless the query asks for another
def go_on_spec(asked: Maybe<&2, Sc.Order>, +o: Sc.Order) -> Sc.Start:
  match asked:
    case None{}:
      Sc.Begin{o, True{}}
    case Some{+a}:
      go_on_spec.cmp(eq_spec(o, a), o, a)

def with_order_spec(asked: Maybe<&2, Sc.Order>, m: Maybe<&2, Sc.Order>) -> Sc.Start:
  match m:
    case None{}:
      Sc.Refuse{invalid_spec()}
    case Some{o}:
      go_on_spec(asked, o)

def safe_spec(a: Sc.After) -> Bool:
  match a:
    case Sc.NoAfter{}:
      False{}
    case Sc.BadAfter{}:
      False{}
    case Sc.SafeAfter{}:
      True{}

def with_cursor_spec(b: Bool, asked: Maybe<&2, Sc.Order>, m: Sc.Mark, fallback: Sc.Order) -> Sc.Start:
  match b:
    case True{}:
      with_order_spec(asked, mark_order_spec(m, fallback))
    case False{}:
      Sc.Refuse{invalid_spec()}

def first_spec(asked: Maybe<&2, Sc.Order>, fallback: Sc.Order) -> Sc.Order:
  match asked:
    case None{}:
      fallback
    case Some{a}:
      a

# where a scan starts: R1-R4
def start_spec(asked: Maybe<&2, Sc.Order>, c: Maybe<&2, Sc.Cursor>, fallback: Sc.Order) -> Sc.Start:
  match c:
    case None{}:
      Sc.Begin{first_spec(asked, fallback), False{}}
    case Some{k}:
      match k:
        case Sc.Cursor{a, m}:
          with_cursor_spec(safe_spec(a), asked, m, fallback)

# the cursor id of a backend: R5
def id_spec(c: Maybe<&2, Sc.After>) -> Sc.Id:
  match c:
    case None{}:
      Sc.NoId{}
    case Some{a}:
      match a:
        case Sc.NoAfter{}:
          Sc.NoId{}
        case Sc.BadAfter{}:
          Sc.RefuseId{invalid_spec()}
        case Sc.SafeAfter{}:
          Sc.UseId{}

# the order of a start, when it starts
def order_of(x: Sc.Start) -> Maybe<&2, Sc.Order>:
  match x:
    case Sc.Begin{o, a}:
      Some{o}
    case Sc.Refuse{t}:
      None{}

# the mark a cursor of order o carries
def mark_of(o: Sc.Order) -> Sc.Mark:
  match o:
    case Sc.Asc{}:
      Sc.AscMark{}
    case Sc.Desc{}:
      Sc.DescMark{}

# Laws
# ----

# LAW scan_start_exact: a scan starts as R1-R4 say: no cursor, at the beginning in the order asked or the default; a cursor, after its id in its own order (the default when it names none), unless a field is bad (refused as invalid) or the query asks for another order (refused, naming both)
# EXCLUDES: a cursor's order overridden by the query, a cursor without an
#   order read as ascending, a bad field accepted or defaulted, a cursor
#   whose id is absent continuing from the start, another refusal text,
#   the two orders swapped in the refusal
law scan_start_exact:
  for asked: Maybe<&2, Sc.Order>
  for c: Maybe<&2, Sc.Cursor>
  for fallback: Sc.Order
  {Sc.start(asked, c, fallback) == start_spec(asked, c, fallback) : Sc.Start}

# LAW scan_cursor_keeps_its_order: a scan that continues a cursor runs in the order the cursor names, whether the query names no order or the same one, whatever the default
# EXCLUDES: pages of one scan in two orders (items skipped or repeated)
law scan_cursor_keeps_its_order:
  for +o: Sc.Order
  for +fallback: Sc.Order
  {order_of(Sc.start(None{}, Some{Sc.Cursor{Sc.SafeAfter{}, mark_of(o)}}, fallback)) == Some{o} : Maybe<&2, Sc.Order>} &
  {order_of(Sc.start(Some{o}, Some{Sc.Cursor{Sc.SafeAfter{}, mark_of(o)}}, fallback)) == Some{o} : Maybe<&2, Sc.Order>}

# LAW scan_id_exact: a backend's cursor id is none without a cursor or `after`, the id for a safe integer, else refused as invalid
# EXCLUDES: a bad id read as none (the scan restarts), an absent id
#   refused, another refusal text
law scan_id_exact:
  for c: Maybe<&2, Sc.After>
  {Sc.cursor_id(c) == id_spec(c) : Sc.Id}

# LAW scan_start_example: anchor: the refusal text of a descending query on an ascending cursor, and an old cursor going on in the default order
# EXCLUDES: a spec that is wrong on the backends' texts
law scan_start_example:
  {Sc.start(Some{Sc.Desc{}}, Some{Sc.Cursor{Sc.SafeAfter{}, Sc.AscMark{}}}, Sc.Asc{}) == Sc.Refuse{"The cursor continues a ascending scan; the query asks for descending"} : Sc.Start} &
  {Sc.start(None{}, Some{Sc.Cursor{Sc.SafeAfter{}, Sc.NoMark{}}}, Sc.Desc{}) == Sc.Begin{Sc.Desc{}, True{}} : Sc.Start} &
  {Sc.start(Some{Sc.Asc{}}, None{}, Sc.Desc{}) == Sc.Begin{Sc.Asc{}, False{}} : Sc.Start}

# LAWS (R6): the entry of the compiled Bend core that runs the rule
# (bend/ffi_scan.bend, called by crates/eukhe-durable storage through
# `eukhe_bend::rules::scan`). Each law is an open claim about FSc.ffi,
# stated with spec spellers built only from the wire primitives of
# bend/wire.bend (their round trips: laws/wire.bend).
#
# R6: a request is tag 0 (start: the order asked, the cursor, the default
#     order) or tag 1 (cursor id: the cursor), spelled as the header of
#     bend/ffi_scan.bend says; the reply is the answer of R1-R5. A
#     malformed request answers the error form "scan: malformed request",
#     input left after the request "scan: input left after the request",
#     never a default.

# Spec spellers
# -------------

def spell_order(o: Sc.Order, rest: String) -> String:
  match o:
    case Sc.Asc{}:
      Wr.put_nat(0n, rest)
    case Sc.Desc{}:
      Wr.put_nat(1n, rest)

def spell_asked(m: Maybe<&2, Sc.Order>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{o}:
      match o:
        case Sc.Asc{}:
          Wr.put_nat(1n, rest)
        case Sc.Desc{}:
          Wr.put_nat(2n, rest)

def spell_after(a: Sc.After, rest: String) -> String:
  match a:
    case Sc.NoAfter{}:
      Wr.put_nat(0n, rest)
    case Sc.BadAfter{}:
      Wr.put_nat(1n, rest)
    case Sc.SafeAfter{}:
      Wr.put_nat(2n, rest)

def spell_mark(m: Sc.Mark, rest: String) -> String:
  match m:
    case Sc.NoMark{}:
      Wr.put_nat(0n, rest)
    case Sc.AscMark{}:
      Wr.put_nat(1n, rest)
    case Sc.DescMark{}:
      Wr.put_nat(2n, rest)
    case Sc.BadMark{}:
      Wr.put_nat(3n, rest)

def spell_cursor(m: Maybe<&2, Sc.Cursor>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{k}:
      match k:
        case Sc.Cursor{a, mk}:
          Wr.put_nat(1n, spell_after(a, spell_mark(mk, rest)))

def spell_id_cursor(m: Maybe<&2, Sc.After>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{a}:
      Wr.put_nat(1n, spell_after(a, rest))

# a request, then rest
def spell_req(q: FSc.Req, rest: String) -> String:
  match q:
    case FSc.QStart{asked, c, f}:
      Wr.put_nat(0n, spell_asked(asked, spell_cursor(c, spell_order(f, rest))))
    case FSc.QId{c}:
      Wr.put_nat(1n, spell_id_cursor(c, rest))

def spell_start(x: Sc.Start) -> String:
  match x:
    case Sc.Begin{o, a}:
      Wr.put_nat(0n, spell_order(o, Wr.put_bool(a, "")))
    case Sc.Refuse{t}:
      Wr.put_nat(1n, Wr.put_str(t, ""))

def spell_id(x: Sc.Id) -> String:
  match x:
    case Sc.NoId{}:
      Wr.put_nat(0n, "")
    case Sc.UseId{}:
      Wr.put_nat(1n, "")
    case Sc.RefuseId{t}:
      Wr.put_nat(2n, Wr.put_str(t, ""))

# the reply to a request: R1-R5
def spell_reply(q: FSc.Req) -> String:
  match q:
    case FSc.QStart{asked, c, f}:
      spell_start(start_spec(asked, c, f))
    case FSc.QId{c}:
      spell_id(id_spec(c))

# Laws
# ----

# LAW scan_ffi_answers: every spelled request answers its spelled answer of R1-R5
# EXCLUDES: a field misread or swapped (the order asked and the default),
#   a tag of another field value, an answer in another spelling
law scan_ffi_answers:
  for +q: FSc.Req
  {FSc.ffi(spell_req(q, "")) == spell_reply(q) : String}

# LAW scan_ffi_exact: every input the entry answers with a value (not the error form) is a spelled request
# EXCLUDES: a default answer to a malformed request (an unknown tag, a
#   missing field) or one with input left over
law scan_ffi_exact:
  for +x: String
  for ok: {LawsBase.wire_opens_err(FSc.ffi(x)) == False{} : Bool}
  exs q: FSc.Req
  {x == spell_req(q, "") : String}

# LAW scan_ffi_left_over: a request followed by more input answers the left-over error form
# EXCLUDES: the input after the request ignored
law scan_ffi_left_over:
  for +q: FSc.Req
  for +h: Char
  for +t: String
  {FSc.ffi(spell_req(q, SCon{h, t})) == Wr.err("scan: input left after the request") : String}

# LAW scan_ffi_example: anchor: the exact bytes of a refused cursor, an old cursor and two malformed requests
# EXCLUDES: another spelling of a request or a reply, a default answer to
#   an unknown tag
law scan_ffi_example:
  {FSc.ffi("1,1,1,") == "2,22,Invalid storage cursor" : String} &
  {FSc.ffi("0,0,1,2,0,1,") == "0,1,T" : String} &
  {FSc.ffi("0,0,1,2,4,1,") == Wr.err("scan: malformed request") : String} &
  {FSc.ffi("2,") == Wr.err("scan: malformed request") : String}

# Spec reader
# -----------
# The request an input spells, read with the wire primitives alone, and the
# input after it; Bad when the input spells no request.

# an `after` field: 0 absent, 1 not a safe integer, 2 a safe integer
def read_after(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.After>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Sc.NoAfter{}, s}
        case 1n:
          Wr.Got{Sc.BadAfter{}, s}
        case 2n:
          Wr.Got{Sc.SafeAfter{}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# an `order` field: 0 absent, 1 ascending, 2 descending, 3 other
def read_mark(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Mark>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Sc.NoMark{}, s}
        case 1n:
          Wr.Got{Sc.AscMark{}, s}
        case 2n:
          Wr.Got{Sc.DescMark{}, s}
        case 3n:
          Wr.Got{Sc.BadMark{}, s}
        case 4n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# an order: 0 ascending, 1 descending
def read_order(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Order>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Sc.Asc{}, s}
        case 1n:
          Wr.Got{Sc.Desc{}, s}
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# the order asked: 0 none, 1 ascending, 2 descending
def read_asked(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Sc.Order>>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{None{}, s}
        case 1n:
          Wr.Got{Some{Sc.Asc{}}, s}
        case 2n:
          Wr.Got{Some{Sc.Desc{}}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def read_cursor.mark(a: Sc.After, m: Wr.Dec<Sc.Mark>) -> Wr.Dec<Maybe<&2, Sc.Cursor>>:
  match m:
    case Wr.Bad{}:
      Wr.Bad{}
    case Wr.Got{k, s}:
      Wr.Got{Some{Sc.Cursor{a, k}}, s}

def read_cursor.after(m: Wr.Dec<Sc.After>) -> Wr.Dec<Maybe<&2, Sc.Cursor>>:
  match m:
    case Wr.Bad{}:
      Wr.Bad{}
    case Wr.Got{a, s}:
      read_cursor.mark(a, read_mark(Wr.get_nat(s)))

# a cursor: 0 none; 1, its `after` field, its `order` field
def read_cursor(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Sc.Cursor>>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{None{}, s}
        case 1n:
          read_cursor.after(read_after(Wr.get_nat(s)))
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def read_start.order(asked: Maybe<&2, Sc.Order>, c: Maybe<&2, Sc.Cursor>, m: Wr.Dec<Sc.Order>) -> Wr.Dec<FSc.Req>:
  match m:
    case Wr.Bad{}:
      Wr.Bad{}
    case Wr.Got{f, s}:
      Wr.Got{FSc.QStart{asked, c, f}, s}

def read_start.cursor(asked: Maybe<&2, Sc.Order>, m: Wr.Dec<Maybe<&2, Sc.Cursor>>) -> Wr.Dec<FSc.Req>:
  match m:
    case Wr.Bad{}:
      Wr.Bad{}
    case Wr.Got{c, s}:
      read_start.order(asked, c, read_order(Wr.get_nat(s)))

def read_start(m: Wr.Dec<Maybe<&2, Sc.Order>>) -> Wr.Dec<FSc.Req>:
  match m:
    case Wr.Bad{}:
      Wr.Bad{}
    case Wr.Got{asked, s}:
      read_start.cursor(asked, read_cursor(Wr.get_nat(s)))

def read_id.after(m: Wr.Dec<Sc.After>) -> Wr.Dec<FSc.Req>:
  match m:
    case Wr.Bad{}:
      Wr.Bad{}
    case Wr.Got{a, s}:
      Wr.Got{FSc.QId{Some{a}}, s}

def read_id(r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{FSc.QId{None{}}, s}
        case 1n:
          read_id.after(read_after(Wr.get_nat(s)))
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def read_spec.tag(r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          read_start(read_asked(Wr.get_nat(s)))
        case 1n:
          read_id(Wr.get_nat(s))
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# the request s spells and the input after it, or Bad
def read_spec(s: String) -> Wr.Dec<FSc.Req>:
  read_spec.tag(Wr.get_nat(s))

# LAW scan_ffi_malformed_exact: every input that spells no request (an unknown tag, a missing field) answers exactly the error form "scan: malformed request"
# EXCLUDES: another error text for a malformed request (the left-over text,
#   a made-up one), a default answer
law scan_ffi_malformed_exact:
  for +s: String
  for no: {read_spec(s) == Wr.Bad{} : Wr.Dec<FSc.Req>}
  {FSc.ffi(s) == Wr.err("scan: malformed request") : String}

# LAW scan_ffi_read_example: anchor: the spec reader reads a spelled request and leaves the rest, and refuses an unknown tag
# EXCLUDES: a vacuous scan_ffi_malformed_exact (a reader that never reads)
law scan_ffi_read_example:
  {read_spec("1,1,2,x") == Wr.Got{FSc.QId{Some{Sc.SafeAfter{}}}, "x"} : Wr.Dec<FSc.Req>} &
  {read_spec("0,3,") == Wr.Bad{} : Wr.Dec<FSc.Req>}
