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

# R4: two orders are the same
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

# R3: an `after` field that is a safe integer
def safe_spec(a: Sc.After) -> Bool:
  match a:
    case Sc.NoAfter{}:
      False{}
    case Sc.BadAfter{}:
      False{}
    case Sc.SafeAfter{}:
      True{}

# the cursor id of a backend: R5, row by row as TS `cursorId` gives it
# (crates/eukhe-durable/src/storage/common.rs:76-78 ports it)
def id_spec(c: Maybe<&2, Sc.After>) -> Sc.Id:
  match c:
    case None{}:
      # R5: no cursor: no id
      Sc.NoId{}
    case Some{a}:
      match a:
        case Sc.NoAfter{}:
          # R5: a cursor without `after`: no id
          Sc.NoId{}
        case Sc.BadAfter{}:
          # R5: `after` not a safe integer: "Invalid storage cursor"
          Sc.RefuseId{invalid_spec()}
        case Sc.SafeAfter{}:
          # R5: a safe integer: the id (Rust test crates/eukhe-bend/src/rules/scan.rs:195)
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

# LAW scan_start_fresh (R1): with no cursor, for every default order, a
# scan starts at the beginning (not after an id) in the order the query
# asks for, or in the default when it asks for none
# EXCLUDES: a fresh scan that skips items, the default preferred to the
#   order asked, the asked order ignored
law scan_start_fresh:
  for +a: Sc.Order
  for +fallback: Sc.Order
  {Sc.start(None{}, None{}, fallback) == Sc.Begin{fallback, False{}} : Sc.Start} &
  {Sc.start(Some{a}, None{}, fallback) == Sc.Begin{a, False{}} : Sc.Start}

# LAW scan_start_continues (R2): a cursor with a safe `after` written with
# order o continues after its id in o, whether the query names no order or
# o, whatever the default
# EXCLUDES: a cursor's order overridden by the default, a continued scan
#   restarted from the beginning
law scan_start_continues:
  for +o: Sc.Order
  for +fallback: Sc.Order
  {Sc.start(None{}, Some{Sc.Cursor{Sc.SafeAfter{}, mark_of(o)}}, fallback) == Sc.Begin{o, True{}} : Sc.Start} &
  {Sc.start(Some{o}, Some{Sc.Cursor{Sc.SafeAfter{}, mark_of(o)}}, fallback) == Sc.Begin{o, True{}} : Sc.Start}

# LAW scan_start_old_cursor (R2): a cursor with a safe `after` and no
# `order` (written before scans had one) continues after its id in the
# default order, whether the query names no order or that one
# EXCLUDES: an old cursor read as ascending, an old cursor refused
law scan_start_old_cursor:
  for +fallback: Sc.Order
  {Sc.start(None{}, Some{Sc.Cursor{Sc.SafeAfter{}, Sc.NoMark{}}}, fallback) == Sc.Begin{fallback, True{}} : Sc.Start} &
  {Sc.start(Some{fallback}, Some{Sc.Cursor{Sc.SafeAfter{}, Sc.NoMark{}}}, fallback) == Sc.Begin{fallback, True{}} : Sc.Start}

# LAW scan_start_bad_after (R3): a cursor whose `after` is absent or not a
# safe integer is refused with exactly "Invalid storage cursor", whatever
# its order field, the order asked and the default
# EXCLUDES: an absent id continuing from the start, a bad id accepted,
#   another refusal text
law scan_start_bad_after:
  for asked: Maybe<&2, Sc.Order>
  for m: Sc.Mark
  for fallback: Sc.Order
  for +a: Sc.After
  for bad: {safe_spec(a) == False{} : Bool}
  {Sc.start(asked, Some{Sc.Cursor{a, m}}, fallback) == Sc.Refuse{"Invalid storage cursor"} : Sc.Start}

# LAW scan_start_bad_mark (R3): a cursor with a safe `after` whose `order`
# is anything but absent, "ascending" or "descending" is refused with
# exactly "Invalid storage cursor", whatever the order asked and the
# default
# EXCLUDES: a bad order field defaulted or read as an order
law scan_start_bad_mark:
  for asked: Maybe<&2, Sc.Order>
  for fallback: Sc.Order
  {Sc.start(asked, Some{Sc.Cursor{Sc.SafeAfter{}, Sc.BadMark{}}}, fallback) == Sc.Refuse{"Invalid storage cursor"} : Sc.Start}

# LAW scan_start_mismatch (R4): a query asking for order a on a cursor of
# order o != a (written with o, or written with none when the default is
# o) is refused with exactly "The cursor continues a <o> scan; the query
# asks for <a>"
# EXCLUDES: a cursor's order overridden by the query, the two orders
#   swapped in the refusal, another refusal text
law scan_start_mismatch:
  for +o: Sc.Order
  for +a: Sc.Order
  for +fallback: Sc.Order
  for other: {eq_spec(o, a) == False{} : Bool}
  {Sc.start(Some{a}, Some{Sc.Cursor{Sc.SafeAfter{}, mark_of(o)}}, fallback) == Sc.Refuse{mismatch_spec(o, a)} : Sc.Start} &
  {Sc.start(Some{a}, Some{Sc.Cursor{Sc.SafeAfter{}, Sc.NoMark{}}}, o) == Sc.Refuse{mismatch_spec(o, a)} : Sc.Start}

# LAW scan_cursor_keeps_its_order: a scan that continues a cursor runs in the order the cursor names, whether the query names no order or the same one, whatever the default
# EXCLUDES: pages of one scan in two orders (items skipped or repeated)
law scan_cursor_keeps_its_order:
  for +o: Sc.Order
  for +fallback: Sc.Order
  {order_of(Sc.start(None{}, Some{Sc.Cursor{Sc.SafeAfter{}, mark_of(o)}}, fallback)) == Some{o} : Maybe<&2, Sc.Order>} &
  {order_of(Sc.start(Some{o}, Some{Sc.Cursor{Sc.SafeAfter{}, mark_of(o)}}, fallback)) == Some{o} : Maybe<&2, Sc.Order>}

# LAW scan_id_exact (R5): a backend's cursor id is id_spec's row for each of
# the four inputs (the whole domain): none without a cursor or `after`, the
# id for a safe integer, "Invalid storage cursor" otherwise; each row cites
# R5 and TS `cursorId` (crates/eukhe-durable/src/storage/common.rs:76-78)
# EXCLUDES: a bad id read as none (the scan restarts), an absent id
#   refused, another refusal text
# waive L10-mirror: pin; the four rows of R5 / TS cursorId (pi-durable,
#   ported in crates/eukhe-durable/src/storage/common.rs:76-91), the safe
#   row also the Rust test crates/eukhe-bend/src/rules/scan.rs:195
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

# the reply to a request: the model's answer (Sc.start, Sc.cursor_id:
# pinned by the laws of R1-R5), spelled
def spell_reply(q: FSc.Req) -> String:
  match q:
    case FSc.QStart{asked, c, f}:
      spell_start(Sc.start(asked, c, f))
    case FSc.QId{c}:
      spell_id(Sc.cursor_id(c))

# Laws
# ----

# LAW scan_ffi_answers: every spelled request answers the spelled answer of the model (Sc.start, Sc.cursor_id: pinned by the laws of R1-R5)
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

# LAW scan_ffi_malformed_unless_request: every answer but the error form
# "scan: malformed request" comes from an input that is a spelled request
# (then, by scan_ffi_exact and scan_ffi_left_over, answered or refused as
# left over)
# EXCLUDES: a default answer or another error text for an input that
#   spells no request (an unknown tag, a missing field)
law scan_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FSc.ffi(s), Wr.err("scan: malformed request")) == False{} : Bool}
  exs q: FSc.Req
  exs rest: String
  {s == spell_req(q, rest) : String}
