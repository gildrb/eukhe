# ffi_shape: the entry of the compiled Bend core for line shapes
# (bend/shape.bend; the tables: bend/incident_shapes.bend and the tui's
# bend/image_marker_shapes.bend, arg_token_shapes.bend,
# autolink_shapes.bend, preview_shapes.bend; Rust: eukhe-bend
# rules/shape.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   shape id  a global Nat, each table a range from its base: 0-99 the
#             incident shapes, 100-109 the image marker, 110-119 the
#             argument tokens, 120-129 the autolinks, 130-199 the code
#             preview; id base + i is the shape at index i of that table
#             (incident `table`, the tui tables' `shape(i)`, which builds
#             only the shape asked); every other id is unknown
#   request   0, ids (List<Nat>), text (String)
#               reply Maybe: index in ids (Nat), start (Nat), end (Nat),
#               captures (List<Maybe<String>>): the first shape of ids
#               that fits the text (bend/shape.bend `first`)
#             1, id (Nat), text (String)
#               reply List of start (Nat), end (Nat), captures
#               (List<Maybe<String>>): every fit of the shape, left to
#               right (bend/shape.bend `all`)
#   starts and ends count chars; a capture is None when its Cap took no
#   part in the fit (an untaken regex group), Some "" when it read no char
#
# A request tag past 1, an unknown shape id, malformed input, or input
# left after the request answers `E shape: malformed request`, never a
# default. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./shape.bend as S
import ./incident_shapes.bend as IS
import ./image_marker_shapes.bend as IM
import ./arg_token_shapes.bend as AT
import ./autolink_shapes.bend as AL
import ./preview_shapes.bend as PS

# A request of the entry
type Req is Data:
  QFirst{ids: List<&2, Nat>, text: String}
  QAll{id: Nat, text: String}

def get_req.first(ids: List<&2, Nat>, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      W.Got{QFirst{ids, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.ids(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ids, s}:
      get_req.first(ids, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_req.all(id: Nat, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      W.Got{QAll{id, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.id(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{id, s}:
      get_req.all(id, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_req.ids(W.get_list(~Nat, ~W.get_nat, s))
        case 1n:
          get_req.id(W.get_nat(s))
        case 2n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# Shape ids
# ---------

# the shape of id in the first range whose end id is below (inc, img,
# arg, link, prev: id is below 100, 110, 120, 130, 200), at its index
# from the range's base
def shape_of.in(inc: Bool, img: Bool, arg: Bool, link: Bool, prev: Bool, +id: Nat) -> Maybe<&2, S.Shape>:
  match inc img arg link prev:
    case True{} _ _ _ _:
      List.get(&2, S.Shape, IS.table(), id)
    case False{} True{} _ _ _:
      IM.shape(Nat.sub(id, 100n))
    case False{} False{} True{} _ _:
      AT.shape(Nat.sub(id, 110n))
    case False{} False{} False{} True{} _:
      AL.shape(Nat.sub(id, 120n))
    case False{} False{} False{} False{} True{}:
      PS.shape(Nat.sub(id, 130n))
    case False{} False{} False{} False{} False{}:
      None{}

# the shape of a global id (none: unknown)
def shape_of(+id: Nat) -> Maybe<&2, S.Shape>:
  shape_of.in(Nat.is_lt(id, 100n), Nat.is_lt(id, 110n), Nat.is_lt(id, 120n), Nat.is_lt(id, 130n), Nat.is_lt(id, 200n), id)

def shapes_of.cons(m: Maybe<&2, S.Shape>, r: Maybe<&2, List<&2, S.Shape>>) -> Maybe<&2, List<&2, S.Shape>>:
  match m:
    case None{}:
      None{}
    case Some{sh}:
      match r:
        case None{}:
          None{}
        case Some{shs}:
          Some{sh <> shs}

# the shapes of the ids (none: one is unknown)
def shapes_of(ids: List<&2, Nat>) -> Maybe<&2, List<&2, S.Shape>>:
  match ids:
    case Nil{}:
      Some{Nil{}}
    case i <> t:
      shapes_of.cons(shape_of(i), shapes_of(t))

# Replies
# -------

def put_mstr(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{s}:
      W.put_nat(1n, W.put_str(s, rest))

def put_fit(f: S.Fit, rest: String) -> String:
  match f:
    case S.Fit{at, to, cs}:
      W.put_nat(at, W.put_nat(to, W.put_list(~Maybe<&2, String>, ~put_mstr, cs, rest)))

def put_found(m: Maybe<&2, S.Found>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{x}:
      match x:
        case S.Found{i, f}:
          W.put_nat(1n, W.put_nat(i, put_fit(f, "")))

def answer.first(m: Maybe<&2, List<&2, S.Shape>>, text: String) -> String:
  match m:
    case None{}:
      W.err("shape: malformed request")
    case Some{shs}:
      put_found(S.first(shs, text))

def answer.all(m: Maybe<&2, S.Shape>, text: String) -> String:
  match m:
    case None{}:
      W.err("shape: malformed request")
    case Some{sh}:
      W.put_list(~S.Fit, ~put_fit, S.all(sh, text), "")

# The entry
# ---------

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QFirst{ids, text}:
      answer.first(shapes_of(ids), text)
    case QAll{id, text}:
      answer.all(shape_of(id), text)

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("shape: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("shape: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
