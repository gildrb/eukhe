# eukhe: the laws of area shape: the entry

import Base
import ../../bend/shape.bend as S
import ../../bend/ffi_shape.bend as FS
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ../incident_shapes.bend as IncidentShapes
import ../image_marker_shapes.bend as ImageMarkerShapes
import ../arg_token_shapes.bend as ArgTokenShapes
import ../autolink_shapes.bend as AutolinkShapes
import ../preview_shapes.bend as PreviewShapes

# (S3) The entry of the compiled core for shapes
# ---------------------------------------------
# bend/ffi_shape.bend (entry 385; eukhe-bend rules/shape.rs). Every request,
# every string after it and every input is free. The model's answers are
# pinned by laws/shape/search.bend (shape_first_of, shape_all), the tables
# by laws/incident_shapes.bend (incident_shapes_table) and the tui's
# laws/image_marker_shapes.bend, arg_token_shapes.bend,
# autolink_shapes.bend and preview_shapes.bend (their `_table` laws).
#
# R1: a shape id is a Nat, each table a range of ids from its base: 0-99
#     the incident shapes (laws/incident_shapes.bend R32), 100-109 the
#     image marker (laws/image_marker_shapes.bend R2), 110-119 the argument
#     tokens (laws/arg_token_shapes.bend R3), 120-129 the autolinks
#     (laws/autolink_shapes.bend R4), 130-199 the code preview
#     (laws/preview_shapes.bend R48); id base + i is the shape at index i
#     of that table; every other id is unknown.
# R2: a request is tag 0, then the ids (a list of Nats: its count, then
#     each Nat), then the text (a string); or tag 1, then one id, then the
#     text. Tags, counts and Nats are spelled as wire Nats (laws/wire.bend).
# R3: the reply to tag 0 is 0 when no shape of the ids fits the text, else
#     1, then the index of the first shape that fits (from 0), its start,
#     its end, its captures (their count, then each: 0 for none, or 1 and
#     the text). The reply to tag 1 is its fits: their count, then each fit
#     as start, end, captures.
# R4: an unknown id in a request, a tag past 1, malformed input or input
#     left after the request answers exactly `E shape: malformed request`;
#     every request whose counts, lengths and Nats fit the wire is read,
#     and nothing else is.

# Spec helpers
# ------------

def sp_err() -> String:
  Wr.err("shape: malformed request")

# R1: the shape of id in the first range whose end id it is below (100,
# 110, 120, 130, 200), at its index from the range's base
def sp_shape_of.in(inc: Bool, img: Bool, arg: Bool, link: Bool, prev: Bool, +id: Nat) -> Maybe<&2, S.Shape>:
  match inc img arg link prev:
    case True{} _ _ _ _:
      List.get(&2, S.Shape, IncidentShapes.sp_table(), id)
    case False{} True{} _ _ _:
      List.get(&2, S.Shape, [ImageMarkerShapes.sp_marker()], Nat.sub(id, 100n))
    case False{} False{} True{} _ _:
      List.get(&2, S.Shape, ArgTokenShapes.sp_table(), Nat.sub(id, 110n))
    case False{} False{} False{} True{} _:
      List.get(&2, S.Shape, AutolinkShapes.sp_table(), Nat.sub(id, 120n))
    case False{} False{} False{} False{} True{}:
      List.get(&2, S.Shape, PreviewShapes.sp_table(), Nat.sub(id, 130n))
    case False{} False{} False{} False{} False{}:
      None{}

# R1: the shape of an id
def sp_shape_of(+id: Nat) -> Maybe<&2, S.Shape>:
  sp_shape_of.in(Nat.is_lt(id, 100n), Nat.is_lt(id, 110n), Nat.is_lt(id, 120n), Nat.is_lt(id, 130n), Nat.is_lt(id, 200n), id)

def sp_shapes.cons(m: Maybe<&2, S.Shape>, r: Maybe<&2, List<&2, S.Shape>>) -> Maybe<&2, List<&2, S.Shape>>:
  match m:
    case None{}:
      None{}
    case Some{sh}:
      match r:
        case None{}:
          None{}
        case Some{shs}:
          Some{sh <> shs}

# R1: the shapes of the ids, none when one is unknown
def sp_shapes(ids: List<&2, Nat>) -> Maybe<&2, List<&2, S.Shape>>:
  match ids:
    case Nil{}:
      Some{Nil{}}
    case i <> t:
      sp_shapes.cons(sp_shape_of(i), sp_shapes(t))

# R2: a request spelled, then rest
def sp_w_req(q: FS.Req, rest: String) -> String:
  match q:
    case FS.QFirst{ids, text}:
      Wr.put_nat(0n, LawsBase.wire_spell_nats(ids, Wr.put_str(text, rest)))
    case FS.QAll{id, text}:
      Wr.put_nat(1n, Wr.put_nat(id, Wr.put_str(text, rest)))

# R2: every count, length and Nat of the request fits the wire
def sp_fit_req(q: FS.Req) -> Bool:
  match q:
    case FS.QFirst{+ids, text}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ids)), LawsBase.wire_nats_fit(ids)), LawsBase.wire_fits(String.length(text)))
    case FS.QAll{id, text}:
      Bool.and(LawsBase.wire_fits(id), LawsBase.wire_fits(String.length(text)))

# R3: a capture: 0, or 1 and its text
def sp_w_cap(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{s}:
      Wr.put_nat(1n, Wr.put_str(s, rest))

def sp_w_caps.items(cs: List<&2, Maybe<&2, String>>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      sp_w_cap(c, sp_w_caps.items(t, rest))

# R3: a fit: start, end, the captures' count, then each capture
def sp_w_fit(f: S.Fit, rest: String) -> String:
  match f:
    case S.Fit{at, to, +cs}:
      Wr.put_nat(at, Wr.put_nat(to, Wr.put_nat(List.length(&2, Maybe<&2, String>, cs), sp_w_caps.items(cs, rest))))

def sp_w_fits.items(fs: List<&2, S.Fit>, rest: String) -> String:
  match fs:
    case Nil{}:
      rest
    case f <> t:
      sp_w_fit(f, sp_w_fits.items(t, rest))

# R3: the reply to tag 0
def sp_w_found(m: Maybe<&2, S.Found>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{x}:
      match x:
        case S.Found{i, f}:
          Wr.put_nat(1n, Wr.put_nat(i, sp_w_fit(f, "")))

def sp_w_first(m: Maybe<&2, List<&2, S.Shape>>, text: String) -> String:
  match m:
    case None{}:
      sp_err()
    case Some{shs}:
      sp_w_found(S.first(shs, text))

def sp_w_all(m: Maybe<&2, S.Shape>, text: String) -> String:
  match m:
    case None{}:
      sp_err()
    case Some{sh}:
      +fs = S.all(sh, text)
      Wr.put_nat(List.length(&2, S.Fit, fs), sp_w_fits.items(fs, ""))

# R3, R4: the reply to a request
def sp_w_reply(q: FS.Req) -> String:
  match q:
    case FS.QFirst{ids, text}:
      sp_w_first(sp_shapes(ids), text)
    case FS.QAll{id, text}:
      sp_w_all(sp_shape_of(id), text)

# Laws
# ----

# LAW shape_entry_decides (R1-R4): every request that fits is answered with
# the spelled answer of the model for the shapes its ids name
# EXCLUDES: another shape for an id, ids in another order, another fit or
#   capture order, a reply spelled another way, a default for an unknown id
law shape_entry_decides:
  for +q: FS.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FS.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW shape_entry_left_over (R4): input after a request is the error
# EXCLUDES: trailing input ignored, or read as part of the request
law shape_entry_left_over:
  for +q: FS.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FS.ffi(sp_w_req(q, rest)) == sp_err() : String}

# LAW shape_entry_reads_only_requests (R2-R4): an answer that is no error
# comes from a spelled request that fits, with nothing after it, and is
# that request's reply
# EXCLUDES: a lenient decoder: an unknown tag, a short string, a count or
#   Nat past the wire, a missing field answered with a default
law shape_entry_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FS.ffi(s)) == False{} : Bool}
  exs q: FS.Req
  {(s, (sp_fit_req(q), FS.ffi(s))) == (sp_w_req(q, ""), (True{}, sp_w_reply(q))) : String & (Bool & String)}

# LAW shape_entry_unknown_request (R4): a request tag past 1 is the error
# EXCLUDES: an unknown request read as a known one (exact error bytes)
law shape_entry_unknown_request:
  for +n: Nat
  for +rest: String
  {FS.ffi(Wr.put_nat(2n+n, rest)) == sp_err() : String}

# LAW shape_entry_unknown_shape (R1, R4): a request that names an unknown
# id, alone or in a list, is the error
# EXCLUDES: an unknown id read as a shape or skipped (exact error bytes)
law shape_entry_unknown_shape:
  for +id: Nat
  for +ids: List<&2, Nat>
  for +text: String
  for no: {sp_shape_of(id) == None{} : Maybe<&2, S.Shape>}
  for h1: {sp_fit_req(FS.QAll{id, text}) == True{} : Bool}
  for h2: {sp_fit_req(FS.QFirst{id <> ids, text}) == True{} : Bool}
  {(FS.ffi(sp_w_req(FS.QAll{id, text}, "")), FS.ffi(sp_w_req(FS.QFirst{id <> ids, text}, ""))) == (sp_err(), sp_err()) : String & String}

# LAW shape_entry_malformed_unless_request (R4): input whose answer is not
# the malformed error holds a request that fits, then a rest
# EXCLUDES: the left-over error, another error text or a reply for input
#   that holds no request
law shape_entry_malformed_unless_request:
  for +s: String
  for other: {String.eq(FS.ffi(s), sp_err()) == False{} : Bool}
  exs q: FS.Req
  exs rest: String
  {(s, sp_fit_req(q)) == (sp_w_req(q, rest), True{}) : String & Bool}

# LAW shape_entry_example (R1-R4): anchor: the exact strings Rust writes
# and reads: the first of the incident shapes 27 and 28 on a command error,
# every fit of shape 27, a request tag past 1, an unknown id, input left
# EXCLUDES: a field order other than Rust's, another reply spelling
law shape_entry_example:
  {[FS.ffi("0,2,27,28,33,Error: Unknown active session: ab"), FS.ffi("1,27,45,AUTHENTICATION FAILED x authentication failed"), FS.ffi("0,1,0,4,x.so"), FS.ffi("2,"), FS.ffi("1,99,1,x"), FS.ffi("1,27,1,x!")] == ["1,1,7,33,1,1,2,ab", "2,0,21,0,24,45,0,", "0,", sp_err(), sp_err(), sp_err()] : List<&2, String>}

# LAW shape_entry_premises_witness (R2, R4): a request that fits exists, an
# unknown id exists, and a malformed input exists
# EXCLUDES: vacuous entry laws whose premises nothing meets
law shape_entry_premises_witness:
  {(sp_fit_req(FS.QAll{31n, "a"}), (sp_fit_req(FS.QFirst{[31n], "a"}), (sp_shape_of(31n), FS.ffi("")))) == (True{}, (True{}, (None{}, sp_err()))) : Bool & (Bool & (Maybe<&2, S.Shape> & String))}
