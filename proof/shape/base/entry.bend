# eukhe: lemmas of the shape entry proofs: the ids name the spec tables'
# shapes (she.shapes, by the tables' `_table` laws), the encoders are the
# spellers (she.answer), a spelled request that fits reads back
# (she.req_rt), and each decoder stage answers Got only for the spelling of
# what it read, every count, length and Nat within the wire (she.rp_all;
# the decoded list of Nats fits: the ge.nats_fit argument of
# proof/glob/base/entry.bend).

import Base
import ../../../bend/shape.bend as S
import ../../../bend/incident_shapes.bend as IS
import ../../../bend/ffi_shape.bend as FS
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/incident_shapes.bend as IncidentShapes
import ../../../laws/image_marker_shapes.bend as ImageMarkerShapes
import ../../../laws/arg_token_shapes.bend as ArgTokenShapes
import ../../../laws/autolink_shapes.bend as AutolinkShapes
import ../../../laws/preview_shapes.bend as PreviewShapes
import ../../../laws/shape/entry.bend as ShapeEntry
import ../../incident_shapes/incident_shapes_table.bend as PIncidentShapesTable
import ../../image_marker_shapes/image_marker_shapes_table.bend as PImageMarkerShapesTable
import ../../arg_token_shapes/arg_token_shapes_table.bend as PArgTokenShapesTable
import ../../autolink_shapes/autolink_shapes_table.bend as PAutolinkShapesTable
import ../../preview_shapes/preview_shapes_table.bend as PPreviewShapesTable
import ../../base/wire.bend as LBaseWire
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../../wire/wire_list_exact.bend as PWireListExact
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_str_exact.bend as PWireStrExact
import ../../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../../wire/base/spell.bend as LAWireSpell

def she.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LAWireSpell.ws_absurd({False{} == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def she.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LAWireSpell.ws_absurd({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

# Shape ids
# ---------

def she.shape_of.in(inc: Bool, img: Bool, arg: Bool, link: Bool, prev: Bool, +id: Nat) -> {FS.shape_of.in(inc, img, arg, link, prev, id) == ShapeEntry.sp_shape_of.in(inc, img, arg, link, prev, id) : Maybe<&2, S.Shape>}:
  match inc img arg link prev:
    case True{} _ _ _ _:
      Equal.cong(List<&2, S.Shape>, Maybe<&2, S.Shape>, xs => List.get(&2, S.Shape, xs, id), IS.table(), IncidentShapes.sp_table(), IncidentShapes.incident_shapes_table())
    case False{} True{} _ _ _:
      ImageMarkerShapes.image_marker_shapes_table(Nat.sub(id, 100n))
    case False{} False{} True{} _ _:
      ArgTokenShapes.arg_token_shapes_table(Nat.sub(id, 110n))
    case False{} False{} False{} True{} _:
      AutolinkShapes.autolink_shapes_table(Nat.sub(id, 120n))
    case False{} False{} False{} False{} True{}:
      PreviewShapes.preview_shapes_table(Nat.sub(id, 130n))
    case False{} False{} False{} False{} False{}:
      {==}

# the entry's shape of an id is the spec's
def she.shape_of(+id: Nat) -> {FS.shape_of(id) == ShapeEntry.sp_shape_of(id) : Maybe<&2, S.Shape>}:
  she.shape_of.in(Nat.is_lt(id, 100n), Nat.is_lt(id, 110n), Nat.is_lt(id, 120n), Nat.is_lt(id, 130n), Nat.is_lt(id, 200n), id)

def she.cons(m: Maybe<&2, S.Shape>, r: Maybe<&2, List<&2, S.Shape>>) -> {FS.shapes_of.cons(m, r) == ShapeEntry.sp_shapes.cons(m, r) : Maybe<&2, List<&2, S.Shape>>}:
  match m:
    case None{}:
      {==}
    case Some{sh}:
      match r:
        case None{}:
          {==}
        case Some{shs}:
          {==}

def she.shapes(ids: List<&2, Nat>) -> {FS.shapes_of(ids) == ShapeEntry.sp_shapes(ids) : Maybe<&2, List<&2, S.Shape>>}:
  match ids:
    case Nil{}:
      {==}
    case +i <> +t:
      %Equal.sym(Maybe<&2, S.Shape>, FS.shape_of(i), ShapeEntry.sp_shape_of(i), she.shape_of(i)) : {FS.shapes_of.cons(_, FS.shapes_of(t)) == ShapeEntry.sp_shapes(i <> t) : Maybe<&2, List<&2, S.Shape>>}
      %Equal.sym(Maybe<&2, List<&2, S.Shape>>, FS.shapes_of(t), ShapeEntry.sp_shapes(t), she.shapes(t)) : {FS.shapes_of.cons(ShapeEntry.sp_shape_of(i), _) == ShapeEntry.sp_shapes(i <> t) : Maybe<&2, List<&2, S.Shape>>}
      she.cons(ShapeEntry.sp_shape_of(i), ShapeEntry.sp_shapes(t))

# The answer
# ----------

def she.mstr(m: Maybe<&2, String>, -rest: String) -> {FS.put_mstr(m, rest) == ShapeEntry.sp_w_cap(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      {==}

def she.caps_go(cs: List<&2, Maybe<&2, String>>, -rest: String) -> {Wr.put_list.go(~Maybe<&2, String>, ~FS.put_mstr, cs, rest) == (List.length(&2, Maybe<&2, String>, cs), ShapeEntry.sp_w_caps.items(cs, rest)) : Nat & String}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Maybe<&2, String>, ~FS.put_mstr, t, rest), (List.length(&2, Maybe<&2, String>, t), ShapeEntry.sp_w_caps.items(t, rest)), she.caps_go(t, rest)) : {Wr.put_list.step(~Maybe<&2, String>, ~FS.put_mstr, c, _) == (1n+List.length(&2, Maybe<&2, String>, t), ShapeEntry.sp_w_cap(c, ShapeEntry.sp_w_caps.items(t, rest))) : Nat & String}
      %Equal.sym(String, FS.put_mstr(c, ShapeEntry.sp_w_caps.items(t, rest)), ShapeEntry.sp_w_cap(c, ShapeEntry.sp_w_caps.items(t, rest)), she.mstr(c, ShapeEntry.sp_w_caps.items(t, rest))) : {(1n+List.length(&2, Maybe<&2, String>, t), _) == (1n+List.length(&2, Maybe<&2, String>, t), ShapeEntry.sp_w_cap(c, ShapeEntry.sp_w_caps.items(t, rest))) : Nat & String}
      {==}

def she.fit(f: S.Fit, -rest: String) -> {FS.put_fit(f, rest) == ShapeEntry.sp_w_fit(f, rest) : String}:
  match f:
    case S.Fit{+at, +to, +cs}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Maybe<&2, String>, ~FS.put_mstr, cs, rest), (List.length(&2, Maybe<&2, String>, cs), ShapeEntry.sp_w_caps.items(cs, rest)), she.caps_go(cs, rest)) : {Wr.put_nat(at, Wr.put_nat(to, Wr.put_list.fin(_))) == ShapeEntry.sp_w_fit(S.Fit{at, to, cs}, rest) : String}
      {==}

def she.fits_go(fs: List<&2, S.Fit>, -rest: String) -> {Wr.put_list.go(~S.Fit, ~FS.put_fit, fs, rest) == (List.length(&2, S.Fit, fs), ShapeEntry.sp_w_fits.items(fs, rest)) : Nat & String}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~S.Fit, ~FS.put_fit, t, rest), (List.length(&2, S.Fit, t), ShapeEntry.sp_w_fits.items(t, rest)), she.fits_go(t, rest)) : {Wr.put_list.step(~S.Fit, ~FS.put_fit, f, _) == (1n+List.length(&2, S.Fit, t), ShapeEntry.sp_w_fit(f, ShapeEntry.sp_w_fits.items(t, rest))) : Nat & String}
      %Equal.sym(String, FS.put_fit(f, ShapeEntry.sp_w_fits.items(t, rest)), ShapeEntry.sp_w_fit(f, ShapeEntry.sp_w_fits.items(t, rest)), she.fit(f, ShapeEntry.sp_w_fits.items(t, rest))) : {(1n+List.length(&2, S.Fit, t), _) == (1n+List.length(&2, S.Fit, t), ShapeEntry.sp_w_fit(f, ShapeEntry.sp_w_fits.items(t, rest))) : Nat & String}
      {==}

def she.found(m: Maybe<&2, S.Found>) -> {FS.put_found(m) == ShapeEntry.sp_w_found(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case S.Found{+i, +f}:
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(i, z)), FS.put_fit(f, ""), ShapeEntry.sp_w_fit(f, ""), she.fit(f, ""))

def she.first(m: Maybe<&2, List<&2, S.Shape>>, +text: String) -> {FS.answer.first(m, text) == ShapeEntry.sp_w_first(m, text) : String}:
  match m:
    case None{}:
      {==}
    case Some{+shs}:
      she.found(S.first(shs, text))

def she.all(m: Maybe<&2, S.Shape>, +text: String) -> {FS.answer.all(m, text) == ShapeEntry.sp_w_all(m, text) : String}:
  match m:
    case None{}:
      {==}
    case Some{+sh}:
      +fs = {S.all(sh, text) : List<&2, S.Fit>}
      %Equal.sym(Nat & String, Wr.put_list.go(~S.Fit, ~FS.put_fit, fs, ""), (List.length(&2, S.Fit, fs), ShapeEntry.sp_w_fits.items(fs, "")), she.fits_go(fs, "")) : {Wr.put_list.fin(_) == ShapeEntry.sp_w_all(Some{sh}, text) : String}
      {==}

# the entry's answer to a request is the spelled spec answer
def she.answer(q: FS.Req) -> {FS.answer(q) == ShapeEntry.sp_w_reply(q) : String}:
  match q:
    case FS.QFirst{+ids, +text}:
      %Equal.sym(Maybe<&2, List<&2, S.Shape>>, FS.shapes_of(ids), ShapeEntry.sp_shapes(ids), she.shapes(ids)) : {FS.answer.first(_, text) == ShapeEntry.sp_w_reply(FS.QFirst{ids, text}) : String}
      she.first(ShapeEntry.sp_shapes(ids), text)
    case FS.QAll{+id, +text}:
      %Equal.sym(Maybe<&2, S.Shape>, FS.shape_of(id), ShapeEntry.sp_shape_of(id), she.shape_of(id)) : {FS.answer.all(_, text) == ShapeEntry.sp_w_reply(FS.QAll{id, text}) : String}
      she.all(ShapeEntry.sp_shape_of(id), text)

# Reading back
# ------------

# a spelled request that fits reads back, the rest untouched
def she.req_rt(q: FS.Req, +rest: String, +h: {ShapeEntry.sp_fit_req(q) == True{} : Bool}) -> {FS.get_req(ShapeEntry.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FS.Req>}:
  match q:
    case FS.QFirst{+ids, +text}:
      +y = {Wr.put_str(text, rest) : String}
      +x = {LawsBase.wire_spell_nats(ids, y) : String}
      +hl = {she.and_l(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ids)), LawsBase.wire_nats_fit(ids)), LawsBase.wire_fits(String.length(text)), h) : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ids)), LawsBase.wire_nats_fit(ids)) == True{} : Bool}}
      +ht = {she.and_r(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ids)), LawsBase.wire_nats_fit(ids)), LawsBase.wire_fits(String.length(text)), h) : {LawsBase.wire_fits(String.length(text)) == True{} : Bool}}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, x)), Wr.Got{0n, x}, Wire.wire_nat_round_trip(0n, x, {==})) : {FS.get_req.tag(_) == Wr.Got{FS.QFirst{ids, text}, rest} : Wr.Dec<FS.Req>}
      %Wire.wire_nats_spells(ids, y) : {FS.get_req.ids(Wr.get_list(~Nat, ~Wr.get_nat, _)) == Wr.Got{FS.QFirst{ids, text}, rest} : Wr.Dec<FS.Req>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, ids, y)), Wr.Got{ids, y}, Wire.wire_list_round_trip(ids, y, hl)) : {FS.get_req.ids(_) == Wr.Got{FS.QFirst{ids, text}, rest} : Wr.Dec<FS.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(text, rest)), Wr.Got{text, rest}, Wire.wire_str_round_trip(text, rest, ht)) : {FS.get_req.first(ids, _) == Wr.Got{FS.QFirst{ids, text}, rest} : Wr.Dec<FS.Req>}
      {==}
    case FS.QAll{+id, +text}:
      +y = {Wr.put_str(text, rest) : String}
      +x = {Wr.put_nat(id, y) : String}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, x)), Wr.Got{1n, x}, Wire.wire_nat_round_trip(1n, x, {==})) : {FS.get_req.tag(_) == Wr.Got{FS.QAll{id, text}, rest} : Wr.Dec<FS.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(id, y)), Wr.Got{id, y}, Wire.wire_nat_round_trip(id, y, she.and_l(LawsBase.wire_fits(id), LawsBase.wire_fits(String.length(text)), h))) : {FS.get_req.id(_) == Wr.Got{FS.QAll{id, text}, rest} : Wr.Dec<FS.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(text, rest)), Wr.Got{text, rest}, Wire.wire_str_round_trip(text, rest, she.and_r(LawsBase.wire_fits(id), LawsBase.wire_fits(String.length(text)), h))) : {FS.get_req.all(id, _) == Wr.Got{FS.QAll{id, text}, rest} : Wr.Dec<FS.Req>}
      {==}

# A decoded list of Nats fits
# ---------------------------

def she.GoP(m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {List.length(&2, Nat, xs) == 1n+m : Nat} & {LawsBase.wire_nats_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def she.and_t(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  LAWireSpell.ws_and_tt(a, b, ha, hb)

def she.go.cons(+m: Nat, +x: Nat, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, v: she.GoP(m, d)) -> she.GoP(1n+m, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = v
      (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, xs), 1n+m, e1), she.and_t(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(xs), fx, e2))
    case Wr.Bad{}:
      Unit{}

def she.go(m: Nat, +s: String, cur: Wr.Dec<Nat>, ec: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) -> she.GoP(m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m:
    case 0n:
      match cur:
        case Wr.Got{+x, +r}:
          ({==}, she.and_t(LawsBase.wire_fits(x), True{}, Wire.wire_nat_decoded_fits(s, x, r, ec), {==}))
        case Wr.Bad{}:
          Unit{}
    case 1n++k:
      match cur:
        case Wr.Got{+x, +r}:
          she.go.cons(k, x, Wire.wire_nat_decoded_fits(s, x, r, ec), Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(r)), she.go(k, r, Wr.get_nat(r), {==}))
        case Wr.Bad{}:
          Unit{}

def she.NF(d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def she.nf.go(+m: Nat, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, v: she.GoP(m, d)) -> she.NF(d):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = v
      %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e1) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
      she.and_t(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(xs), fn, e2)
    case Wr.Bad{}:
      Unit{}

def she.nf.n(n: Nat, +s1: String, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> she.NF(Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s1})):
  match n:
    case 0n:
      {==}
    case 1n++m:
      she.nf.go(m, fn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s1)), she.go(m, s1, Wr.get_nat(s1), {==}))

def she.nf.start(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> she.NF(Wr.get_list.start(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+n, +s1}:
      she.nf.n(n, s1, Wire.wire_nat_decoded_fits(s, n, s1, ed))
    case Wr.Bad{}:
      Unit{}

# a decoded list of Nats fits the wire: its count and every item
def she.nats_fit(+s: String, +xs: List<&2, Nat>, +r: String, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == Wr.Got{xs, r} : Wr.Dec<List<&2, Nat>>}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}:
  %ed : she.NF(_)
  she.nf.start(s, Wr.get_nat(s), {==})

# Exactness
# ---------

def she.RP(s: String, d: Wr.Dec<FS.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ShapeEntry.sp_w_req(q, r) : String} & {ShapeEntry.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def she.x_first(-s: String, +ids: List<&2, Nat>, +s1: String, pre: {s == Wr.put_nat(0n, LawsBase.wire_spell_nats(ids, s1)) : String}, fi: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ids)), LawsBase.wire_nats_fit(ids)) == True{} : Bool}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> she.RP(s, FS.get_req.first(ids, d)):
  match d:
    case Wr.Got{+t, +r}:
      +ee = ed
      (Equal.trans(String, s, Wr.put_nat(0n, LawsBase.wire_spell_nats(ids, s1)), Wr.put_nat(0n, LawsBase.wire_spell_nats(ids, Wr.put_str(t, r))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, LawsBase.wire_spell_nats(ids, z)), s1, Wr.put_str(t, r), Wire.wire_str_exact(s1, t, r, ee))), she.and_t(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ids)), LawsBase.wire_nats_fit(ids)), LawsBase.wire_fits(String.length(t)), fi, Wire.wire_str_decoded_fits(s1, t, r, ee)))
    case Wr.Bad{}:
      Unit{}

def she.x_ids(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s0) == d : Wr.Dec<List<&2, Nat>>}) -> she.RP(s, FS.get_req.ids(d)):
  match d:
    case Wr.Got{+ids, +s1}:
      +ee = ed
      +e0 = {Equal.trans(String, s0, Wr.put_list(~Nat, ~Wr.put_nat, ids, s1), LawsBase.wire_spell_nats(ids, s1), Wire.wire_list_exact(s0, ids, s1, ee), Wire.wire_nats_spells(ids, s1)) : {s0 == LawsBase.wire_spell_nats(ids, s1) : String}}
      she.x_first(s, ids, s1, Equal.trans(String, s, Wr.put_nat(0n, s0), Wr.put_nat(0n, LawsBase.wire_spell_nats(ids, s1)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s0, LawsBase.wire_spell_nats(ids, s1), e0)), she.nats_fit(s0, ids, s1, ee), Wr.get_str(s1), {==})
    case Wr.Bad{}:
      Unit{}

def she.x_all(-s: String, +id: Nat, +s1: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(id, s1)) : String}, fi: {LawsBase.wire_fits(id) == True{} : Bool}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> she.RP(s, FS.get_req.all(id, d)):
  match d:
    case Wr.Got{+t, +r}:
      +ee = ed
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(id, s1)), Wr.put_nat(1n, Wr.put_nat(id, Wr.put_str(t, r))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(id, z)), s1, Wr.put_str(t, r), Wire.wire_str_exact(s1, t, r, ee))), she.and_t(LawsBase.wire_fits(id), LawsBase.wire_fits(String.length(t)), fi, Wire.wire_str_decoded_fits(s1, t, r, ee)))
    case Wr.Bad{}:
      Unit{}

def she.x_id(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> she.RP(s, FS.get_req.id(d)):
  match d:
    case Wr.Got{+id, +s1}:
      +ee = ed
      she.x_all(s, id, s1, Equal.trans(String, s, Wr.put_nat(1n, s0), Wr.put_nat(1n, Wr.put_nat(id, s1)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s0, Wr.put_nat(id, s1), Wire.wire_nat_exact(s0, id, s1, ee))), Wire.wire_nat_decoded_fits(s0, id, s1, ee), Wr.get_str(s1), {==})
    case Wr.Bad{}:
      Unit{}

def she.x_req(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> she.RP(s, FS.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          she.x_ids(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_list(~Nat, ~Wr.get_nat, s0), {==})
        case 1n:
          she.x_id(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the decoder reads from s is the spelling of what it read, then
# its rest, and fits the wire
def she.rp_all(+s: String) -> she.RP(s, FS.get_req(s)):
  she.x_req(s, Wr.get_nat(s), {==})
