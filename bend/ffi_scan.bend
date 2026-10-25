# ffi_scan: the compiled Bend core's entry for where a built-in storage
# scan starts (bend/scan.bend). Rust `eukhe_bend::rules::scan` calls it
# through `eukhe_bend::call` once per scan page.
#
# Request (crates/eukhe-bend/WIRE.md), a question:
#   tag 0  start: the order asked (0 none, 1 ascending, 2 descending), the
#          cursor (0 none; 1, then its `after` field: 0 absent, 1 not a safe
#          integer, 2 a safe integer; then its `order` field: 0 absent,
#          1 "ascending", 2 "descending", 3 anything else), the scan's
#          default order (0 ascending, 1 descending)
#          -> 0, the order (0 ascending, 1 descending), whether the scan
#             continues after the cursor's id (Bool) | 1, the refusal (String)
#   tag 1  cursor id: the cursor (0 none; 1, then its `after` field as above)
#          -> 0 no id | 1 the cursor's id | 2, the refusal (String)
# A malformed request answers the error form "scan: malformed request";
# input left after the request answers "scan: input left after the
# request": never a default. laws/scan.bend (section entry) states this
# file's laws. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./scan.bend as Sc

# A request of the entry
type Req is Data:
  QStart{asked: Maybe<&2, Sc.Order>, cursor: Maybe<&2, Sc.Cursor>, fallback: Sc.Order}
  QId{cursor: Maybe<&2, Sc.After>}

# Requests
# --------

def get_after(r: W.Dec<Nat>) -> W.Dec<Sc.After>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Sc.NoAfter{}, s}
        case 1n:
          W.Got{Sc.BadAfter{}, s}
        case 2n:
          W.Got{Sc.SafeAfter{}, s}
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_mark(r: W.Dec<Nat>) -> W.Dec<Sc.Mark>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Sc.NoMark{}, s}
        case 1n:
          W.Got{Sc.AscMark{}, s}
        case 2n:
          W.Got{Sc.DescMark{}, s}
        case 3n:
          W.Got{Sc.BadMark{}, s}
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_order(r: W.Dec<Nat>) -> W.Dec<Sc.Order>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Sc.Asc{}, s}
        case 1n:
          W.Got{Sc.Desc{}, s}
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_asked(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Sc.Order>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          W.Got{Some{Sc.Asc{}}, s}
        case 2n:
          W.Got{Some{Sc.Desc{}}, s}
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_cursor.mark(a: Sc.After, r: W.Dec<Sc.Mark>) -> W.Dec<Maybe<&2, Sc.Cursor>>:
  match r:
    case W.Got{m, s}:
      W.Got{Some{Sc.Cursor{a, m}}, s}
    case W.Bad{}:
      W.Bad{}

def get_cursor.after(r: W.Dec<Sc.After>) -> W.Dec<Maybe<&2, Sc.Cursor>>:
  match r:
    case W.Got{a, s}:
      get_cursor.mark(a, get_mark(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_cursor(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Sc.Cursor>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_cursor.after(get_after(W.get_nat(s)))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_start.fallback(asked: Maybe<&2, Sc.Order>, c: Maybe<&2, Sc.Cursor>, r: W.Dec<Sc.Order>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      W.Got{QStart{asked, c, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_start.cursor(asked: Maybe<&2, Sc.Order>, r: W.Dec<Maybe<&2, Sc.Cursor>>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_start.fallback(asked, c, get_order(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_start(r: W.Dec<Maybe<&2, Sc.Order>>) -> W.Dec<Req>:
  match r:
    case W.Got{asked, s}:
      get_start.cursor(asked, get_cursor(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_id.after(r: W.Dec<Sc.After>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QId{Some{a}}, s}
    case W.Bad{}:
      W.Bad{}

def get_id(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{QId{None{}}, s}
        case 1n:
          get_id.after(get_after(W.get_nat(s)))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_req(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_start(get_asked(W.get_nat(s)))
        case 1n:
          get_id(W.get_nat(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# Replies
# -------

def put_order(o: Sc.Order, rest: String) -> String:
  match o:
    case Sc.Asc{}:
      W.put_nat(0n, rest)
    case Sc.Desc{}:
      W.put_nat(1n, rest)

def put_start(x: Sc.Start) -> String:
  match x:
    case Sc.Begin{o, a}:
      W.put_nat(0n, put_order(o, W.put_bool(a, "")))
    case Sc.Refuse{t}:
      W.put_nat(1n, W.put_str(t, ""))

def put_id(x: Sc.Id) -> String:
  match x:
    case Sc.NoId{}:
      W.put_nat(0n, "")
    case Sc.UseId{}:
      W.put_nat(1n, "")
    case Sc.RefuseId{t}:
      W.put_nat(2n, W.put_str(t, ""))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QStart{asked, c, f}:
      put_start(Sc.start(asked, c, f))
    case QId{c}:
      put_id(Sc.cursor_id(c))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("scan: input left after the request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("scan: malformed request")

# the entry: decode the question, answer the model's answer
def ffi(input: String) -> String:
  ffi.got(get_req(W.get_nat(input)))
