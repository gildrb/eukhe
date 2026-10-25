# scan: where a built-in storage scan starts (port of pi-durable
# `storage/scan.ts` and the backends' `cursorId`; the Rust host is
# crates/eukhe-durable/src/storage/{scan,common}.rs). A page of a scan ends
# with a cursor: the `after` id of its last item and the scan's order. The
# host reads the cursor's fields and tells the model what each one is (the
# id itself stays with the host); the model decides the order the scan
# runs in, whether it continues after the cursor's id, or the refusal and
# its text. Pure: no IO, no @unsafe. laws/scan.bend states its laws.

import Base

# Types
# -----

# the order of a scan
type Order is Data:
  Asc{}
  Desc{}

# what a cursor's `after` field is
type After is Data:
  NoAfter{}
  BadAfter{}
  SafeAfter{}

# what a cursor's `order` field is
type Mark is Data:
  NoMark{}
  AscMark{}
  DescMark{}
  BadMark{}

# a cursor, as the host read it
type Cursor is Data:
  Cursor{after: After, mark: Mark}

# where a scan starts: its order and whether it continues after the
# cursor's id; or the refusal of the request
type Start is Data:
  Begin{order: Order, after: Bool}
  Refuse{text: String}

# the cursor id a backend scan reads: none, the cursor's id, or a refusal
type Id is Data:
  NoId{}
  UseId{}
  RefuseId{text: String}

# Texts
# -----

# the refusal of a cursor whose fields are not a scan's (TS: "Invalid
# storage cursor")
def invalid() -> String:
  "Invalid storage cursor"

# the name of an order, as a query and a cursor write it
def name(o: Order) -> String:
  match o:
    case Asc{}:
      "ascending"
    case Desc{}:
      "descending"

# the refusal of a query that asks for another order than its cursor's
def mismatch(+stored: Order, +asked: Order) -> String:
  String.append("The cursor continues a ", String.append(name(stored), String.append(" scan; the query asks for ", name(asked))))

# Rules
# -----

def same(a: Order, b: Order) -> Bool:
  match a:
    case Asc{}:
      match b:
        case Asc{}:
          True{}
        case Desc{}:
          False{}
    case Desc{}:
      match b:
        case Asc{}:
          False{}
        case Desc{}:
          True{}

def or_order(m: Maybe<&2, Order>, d: Order) -> Order:
  match m:
    case None{}:
      d
    case Some{o}:
      o

# the order a cursor goes on in, or the refusal of a query that asks
# for another one
def start.agree(ok: Bool, +a: Order, +order: Order) -> Start:
  match ok:
    case True{}:
      Begin{order, True{}}
    case False{}:
      Refuse{mismatch(order, a)}

# a cursor's order goes on, unless the query asks for another one
def start.check(+asked: Maybe<&2, Order>, +order: Order) -> Start:
  match asked:
    case None{}:
      Begin{order, True{}}
    case Some{+a}:
      start.agree(same(a, order), a, order)

# the cursor's order (a cursor without one, written before scans had an
# order, goes on in the scan's default order), or a refusal
def start.mark(asked: Maybe<&2, Order>, m: Mark, fallback: Order) -> Start:
  match m:
    case NoMark{}:
      start.check(asked, fallback)
    case AscMark{}:
      start.check(asked, Asc{})
    case DescMark{}:
      start.check(asked, Desc{})
    case BadMark{}:
      Refuse{invalid()}

def start.cursor(asked: Maybe<&2, Order>, c: Cursor, fallback: Order) -> Start:
  match c:
    case Cursor{a, m}:
      match a:
        case SafeAfter{}:
          start.mark(asked, m, fallback)
        case NoAfter{}:
          Refuse{invalid()}
        case BadAfter{}:
          Refuse{invalid()}

# where a scan starts: without a cursor, from the start in the order asked
# (else the default); with one, after its id in its order
def start(asked: Maybe<&2, Order>, c: Maybe<&2, Cursor>, fallback: Order) -> Start:
  match c:
    case None{}:
      Begin{or_order(asked, fallback), False{}}
    case Some{k}:
      start.cursor(asked, k, fallback)

# the cursor id of a backend scan: none without a cursor or `after`, the
# id when it is a safe integer, else a refusal
def cursor_id(c: Maybe<&2, After>) -> Id:
  match c:
    case None{}:
      NoId{}
    case Some{a}:
      match a:
        case NoAfter{}:
          NoId{}
        case SafeAfter{}:
          UseId{}
        case BadAfter{}:
          RefuseId{invalid()}
