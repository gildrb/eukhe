# eukhe: the proof of LAW gateway_width_ffi_reads_only_requests
#
# PROOF: the list the decoder reads is spelled and fits (NL.nl.nl); the
# rows Fl.unflat reads from it flatten back to it by the spec (gro.unflat,
# by the fold's state: gro.fold); so the table read is spelled and fits
# (gro.req); the answer is the error form unless the table was read whole,
# nothing left, and then it is the spelled layout (gro.fin with
# gwa.reply).

import Base
import ../../bend/ffi_gateway_width.bend as FGw
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_width.bend as GatewayWidth
import ../wire/base/spell.bend as LAWireSpell
import ../tools/tools_ffi_reads_only_requests/nats.bend as NL
import ./gateway_width_ffi_answers_spelled.bend as PGatewayWidthFfiAnswersSpelled

# Rows read
# ---------

# what a fold of ns says: the lists of its state flatten to ns
def gro.FI(ns: List<&2, Nat>, m: Maybe<&2, Fl.St>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{st}:
      {ns == GatewayWidth.gw_flat(Fl.St.lists(st)) : List<&2, Nat>}

def gro.fold_step(-rest: List<&2, Nat>, m: Maybe<&2, Fl.St>, ih: gro.FI(rest, m), n: Nat) -> gro.FI(n <> rest, Fl.step(n, m)):
  match m:
    case None{}:
      Unit{}
    case Some{st}:
      match st:
        case Fl.Start{}:
          match n:
            case 0n:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => 0n <> z, rest, Nil{}, ih)
            case 1n+x:
              Unit{}
        case Fl.Mid{o, d}:
          match n:
            case 0n:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => 0n <> z, rest, GatewayWidth.gw_flat(o <> d), ih)
            case 1n+x:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => {1n+x : Nat} <> z, rest, GatewayWidth.gw_flat(o <> d), ih)

def gro.fold(ns: List<&2, Nat>) -> gro.FI(ns, Fl.fold(ns)):
  match ns:
    case Nil{}:
      {==}
    case n <> +rest:
      gro.fold_step(rest, Fl.fold(rest), gro.fold(rest), n)

# the rows Fl.unflat reads flatten to its input
def gro.UI(ns: List<&2, Nat>, m: Maybe<&2, List<&2, List<&2, Nat>>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{xss}:
      {ns == GatewayWidth.gw_flat(xss) : List<&2, Nat>}

def gro.unflat_fin(-ns: List<&2, Nat>, m: Maybe<&2, Fl.St>, h: gro.FI(ns, m)) -> gro.UI(ns, Fl.unflat.fin(m)):
  match m:
    case None{}:
      Unit{}
    case Some{st}:
      h

def gro.unflat(+ns: List<&2, Nat>) -> gro.UI(ns, Fl.unflat(ns)):
  gro.unflat_fin(ns, Fl.fold(ns), gro.fold(ns))

# The decoder
# -----------

# what the decoder reads is its spelling, then its rest, and fits
def gro.Req(s: String, d: Wr.Dec<List<&2, List<&2, Nat>>>) -> Type:
  match d:
    case Wr.Got{rows, r}:
      {s == GatewayWidth.gw_spell_req(rows, r) : String} & {GatewayWidth.gw_req_fits(rows) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def gro.spell(-s: String, -ns: List<&2, Nat>, -s1: String, -rows: List<&2, List<&2, Nat>>, pre: {s == LawsBase.wire_spell_nats(ns, s1) : String}, u: {ns == GatewayWidth.gw_flat(rows) : List<&2, Nat>}) -> {s == GatewayWidth.gw_spell_req(rows, s1) : String}:
  %u : {s == LawsBase.wire_spell_nats(_, s1) : String}
  pre

def gro.fits(-ns: List<&2, Nat>, -rows: List<&2, List<&2, Nat>>, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ns)), LawsBase.wire_nats_fit(ns)) == True{} : Bool}, +u: {ns == GatewayWidth.gw_flat(rows) : List<&2, Nat>}) -> {GatewayWidth.gw_req_fits(rows) == True{} : Bool}:
  %u : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, _)), LawsBase.wire_nats_fit(GatewayWidth.gw_flat(rows))) == True{} : Bool}
  %u : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ns)), LawsBase.wire_nats_fit(_)) == True{} : Bool}
  f

# the input and the fit of the list read are the table's
def gro.done(-s: String, -ns: List<&2, Nat>, -s1: String, -rows: List<&2, List<&2, Nat>>, pre: {s == LawsBase.wire_spell_nats(ns, s1) : String}, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ns)), LawsBase.wire_nats_fit(ns)) == True{} : Bool}, +u: {ns == GatewayWidth.gw_flat(rows) : List<&2, Nat>}) -> {s == GatewayWidth.gw_spell_req(rows, s1) : String} & {GatewayWidth.gw_req_fits(rows) == True{} : Bool}:
  (gro.spell(s, ns, s1, rows, pre, u), gro.fits(ns, rows, f, u))

def gro.of(+s: String, +ns: List<&2, Nat>, +s1: String, pre: {s == LawsBase.wire_spell_nats(ns, s1) : String}, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ns)), LawsBase.wire_nats_fit(ns)) == True{} : Bool}, m: Maybe<&2, List<&2, List<&2, Nat>>>, u: gro.UI(ns, m)) -> gro.Req(s, FGw.get_req.of(m, s1)):
  match m:
    case Some{+rows}:
      gro.done(s, ns, s1, rows, pre, f, u)
    case None{}:
      Unit{}

def gro.ns(+s: String, d: Wr.Dec<List<&2, Nat>>, xd: NL.nl.NL(s, d)) -> gro.Req(s, FGw.get_req.ns(d)):
  match d:
    case Wr.Got{+ns, +s1}:
      (e, f) = xd
      gro.of(s, ns, s1, e, f, Fl.unflat(ns), gro.unflat(ns))
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled table that fits, then
# the rest
def gro.req(+s: String) -> gro.Req(s, FGw.get_req(s)):
  gro.ns(s, Wr.get_list(~Nat, ~Wr.get_nat, s), NL.nl.nl(s))

# The entry
# ---------

def gro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, List<&2, List<&2, Nat>>, rows => {(s, (GatewayWidth.gw_req_fits(rows), a)) == (GatewayWidth.gw_spell_req(rows, ""), (True{}, GatewayWidth.gw_spell_answer(rows))) : String & (Bool & String)}>

# a table read whole: the input, the fit and the answer are the spec's
def gro.top_eq(+s: String, +rows: List<&2, List<&2, Nat>>, +a: String, e: {s == GatewayWidth.gw_spell_req(rows, "") : String}, f: {GatewayWidth.gw_req_fits(rows) == True{} : Bool}, ea: {a == GatewayWidth.gw_spell_answer(rows) : String}) -> {(s, (GatewayWidth.gw_req_fits(rows), a)) == (GatewayWidth.gw_spell_req(rows, ""), (True{}, GatewayWidth.gw_spell_answer(rows))) : String & (Bool & String)}:
  %Equal.sym(String, s, GatewayWidth.gw_spell_req(rows, ""), e) : {(_, (GatewayWidth.gw_req_fits(rows), a)) == (GatewayWidth.gw_spell_req(rows, ""), (True{}, GatewayWidth.gw_spell_answer(rows))) : String & (Bool & String)}
  %Equal.sym(Bool, GatewayWidth.gw_req_fits(rows), True{}, f) : {(GatewayWidth.gw_spell_req(rows, ""), (_, a)) == (GatewayWidth.gw_spell_req(rows, ""), (True{}, GatewayWidth.gw_spell_answer(rows))) : String & (Bool & String)}
  %Equal.sym(String, a, GatewayWidth.gw_spell_answer(rows), ea) : {(GatewayWidth.gw_spell_req(rows, ""), (True{}, _)) == (GatewayWidth.gw_spell_req(rows, ""), (True{}, GatewayWidth.gw_spell_answer(rows))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the table, anything left is the
# error form
def gro.fin(+s: String, +rows: List<&2, List<&2, Nat>>, r: String, pre: {s == GatewayWidth.gw_spell_req(rows, r) : String}, f: {GatewayWidth.gw_req_fits(rows) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FGw.reply(Wr.end(r), rows)) == False{} : Bool}) -> gro.G(s, FGw.reply(Wr.end(r), rows)):
  match r:
    case SNil{}:
      (rows, gro.top_eq(s, rows, FGw.reply(True{}, rows), pre, f, PGatewayWidthFfiAnswersSpelled.gwa.reply(rows)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(gro.G(s, FGw.reply(False{}, rows)), ok)

def gro.main(+s: String, d: Wr.Dec<List<&2, List<&2, Nat>>>, inv: gro.Req(s, d), ok: {LawsBase.wire_opens_err(FGw.answer(d)) == False{} : Bool}) -> gro.G(s, FGw.answer(d)):
  match d:
    case Wr.Got{+rows, +r}:
      (e, f) = inv
      gro.fin(s, rows, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(gro.G(s, Wr.err("gateway_width: malformed request")), ok)

def GatewayWidth.gateway_width_ffi_reads_only_requests(s, ok):
  gro.main(s, FGw.get_req(s), gro.req(s), ok)
