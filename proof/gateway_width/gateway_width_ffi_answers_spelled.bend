# eukhe: the proof of LAW gateway_width_ffi_answers_spelled
#
# PROOF: Fl.flat is the spec's gw_flat (gwa.flat) and the entry's table
# the spec's (gwa.table), so the spec's spelling of a table is the entry's
# put_req (gwa.req) and its fit the entry's (gwa.fits);
# gateway_width_ffi_answers answers it with put_lay of the layout, which
# spells it as the spec does (gwa.lay).

import Base
import ../../bend/ffi_gateway_width.bend as FGw
import ../../bend/gateway_width.bend as Gw
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_width.bend as GatewayWidth
import ../../laws/wire.bend as Wire
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ./gateway_width_ffi_answers.bend as PGatewayWidthFfiAnswers

# the flat writer is the spec's
def gwa.one(xs: List<&2, Nat>, +rest: List<&2, Nat>) -> {Fl.one(xs, rest) == GatewayWidth.gw_flat_one(xs, rest) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => {1n+x : Nat} <> z, Fl.one(t, rest), GatewayWidth.gw_flat_one(t, rest), gwa.one(t, rest))

def gwa.flat(xss: List<&2, List<&2, Nat>>) -> {Fl.flat(xss) == GatewayWidth.gw_flat(xss) : List<&2, Nat>}:
  match xss:
    case Nil{}:
      {==}
    case +xs <> +t:
      %gwa.flat(t) : {Fl.one(xs, Fl.flat(t)) == GatewayWidth.gw_flat_one(xs, _) : List<&2, Nat>}
      gwa.one(xs, Fl.flat(t))

# the entry's measured table is the spec's
def gwa.cells(ws: List<&2, Nat>) -> {FGw.cells(ws) == GatewayWidth.gw_cells(ws) : List<&2, List<&2, Nat>>}:
  match ws:
    case Nil{}:
      {==}
    case w <> rest:
      Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => [w] <> z, FGw.cells(rest), GatewayWidth.gw_cells(rest), gwa.cells(rest))

def gwa.table(rows: List<&2, List<&2, Nat>>) -> {FGw.table(rows) == GatewayWidth.gw_table(rows) : List<&2, List<&2, List<&2, Nat>>>}:
  match rows:
    case Nil{}:
      {==}
    case +r <> +rest:
      %gwa.cells(r) : {FGw.cells(r) <> FGw.table(rest) == _ <> GatewayWidth.gw_table(rest) : List<&2, List<&2, List<&2, Nat>>>}
      %gwa.table(rest) : {FGw.cells(r) <> FGw.table(rest) == FGw.cells(r) <> _ : List<&2, List<&2, List<&2, Nat>>>}
      {==}

# the spec's spelling of a table is the entry's
def gwa.req(+rows: List<&2, List<&2, Nat>>, +rest: String) -> {FGw.put_req(rows, rest) == GatewayWidth.gw_spell_req(rows, rest) : String}:
  %gwa.flat(rows) : {FGw.put_req(rows, rest) == LawsBase.wire_spell_nats(_, rest) : String}
  Wire.wire_nats_spells(Fl.flat(rows), rest)

# a table that fits as the spec says fits as the entry's laws ask
def gwa.fits(+rows: List<&2, List<&2, Nat>>, fits: {GatewayWidth.gw_req_fits(rows) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(rows))), LawsBase.wire_nats_fit(Fl.flat(rows))) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, Fl.flat(rows), GatewayWidth.gw_flat(rows), gwa.flat(rows)) : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(rows))), LawsBase.wire_nats_fit(_)) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, Fl.flat(rows), GatewayWidth.gw_flat(rows), gwa.flat(rows)) : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, _)), LawsBase.wire_nats_fit(GatewayWidth.gw_flat(rows))) == True{} : Bool}
  fits

# the entry spells a layout as the spec does
def gwa.lay(l: Gw.Lay) -> {FGw.put_lay(l, "") == GatewayWidth.gw_spell_lay(l) : String}:
  match l:
    case Gw.Lay{+w, +p}:
      %gwa.flat(p) : {FGw.put_lay(Gw.Lay{w, p}, "") == LawsBase.wire_spell_nats(w, LawsBase.wire_spell_nats(_, "")) : String}
      %Wire.wire_nats_spells(Fl.flat(p), "") : {FGw.put_lay(Gw.Lay{w, p}, "") == LawsBase.wire_spell_nats(w, _) : String}
      Wire.wire_nats_spells(w, FGw.put_ns(Fl.flat(p), ""))

# the entry's reply to a table read whole is the spec's answer
def gwa.reply(+rows: List<&2, List<&2, Nat>>) -> {FGw.put_lay(Gw.layout(FGw.table(rows)), "") == GatewayWidth.gw_spell_answer(rows) : String}:
  %gwa.table(rows) : {FGw.put_lay(Gw.layout(FGw.table(rows)), "") == GatewayWidth.gw_spell_lay(Gw.layout(_)) : String}
  gwa.lay(Gw.layout(FGw.table(rows)))

def GatewayWidth.gateway_width_ffi_answers_spelled(rows, fits):
  %gwa.req(rows, "") : {FGw.ffi(_) == GatewayWidth.gw_spell_answer(rows) : String}
  Equal.trans(String, FGw.ffi(FGw.put_req(rows, "")), FGw.put_lay(Gw.layout(FGw.table(rows)), ""), GatewayWidth.gw_spell_answer(rows), GatewayWidth.gateway_width_ffi_answers(rows, gwa.fits(rows, fits)), gwa.reply(rows))
