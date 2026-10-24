# eukhe: the proof of LAW cvar_layers_ffi_answers
# Per request: each field reads back from what the laws spell (LCl.cl.*_rt,
# LCl.cl.*_full, LWire.pw6.nat), nothing is left, and the reply writers
# write what the laws spell (LCl.cl.*_put, LCl.cl.values_items).

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar_layers.bend as FCL
import ../../bend/wire.bend as Wr
import ../../laws/cvar_layers.bend as Cl
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LCl

def ca.reg(+ds: List<&2, Cv.Decl>, +h: {Cl.decls_fit(ds) == True{} : Bool}) -> {FCL.ffi(Cl.spell_ask(FCL.AskRegistry{ds})) == Cl.spell_answer(FCL.AskRegistry{ds}) : String}:
  %LWire.pw6.nat(0n, Cl.spell_decls(ds, ""), {==}) : {FCL.run(FCL.get_ask.go(_)) == Cl.spell_answer(FCL.AskRegistry{ds}) : String}
  %LCl.cl.decls_full(ds, "", h) : {FCL.run(FCL.get_reg(_)) == Cl.spell_answer(FCL.AskRegistry{ds}) : String}
  LCl.cl.refusal_put(Cv.refusal(ds), "")

def ca.vals(+ds: List<&2, Cv.Decl>, +c: List<&2, Cv.Bind>, +f: List<&2, Cv.Ag>, +h: {Cl.ask_fits(FCL.AskValues{ds, c, f}) == True{} : Bool}) -> {FCL.ffi(Cl.spell_ask(FCL.AskValues{ds, c, f})) == Cl.spell_answer(FCL.AskValues{ds, c, f}) : String}:
  +a = {FCL.AskValues{ds, c, f} : FCL.Ask}
  +y2 = Cl.spell_ags(f, "")
  +y1 = Cl.spell_binds(c, y2)
  +h1 = LCl.cl.and_l(Cl.decls_fit(ds), Bool.and(Cl.binds_fit(c), Cl.ags_fit(f)), h)
  +h23 = LCl.cl.and_r(Cl.decls_fit(ds), Bool.and(Cl.binds_fit(c), Cl.ags_fit(f)), h)
  %LWire.pw6.nat(1n, Cl.spell_decls(ds, y1), {==}) : {FCL.run(FCL.get_ask.go(_)) == Cl.spell_answer(a) : String}
  %LCl.cl.decls_full(ds, y1, h1) : {FCL.run(FCL.get_vals(_)) == Cl.spell_answer(a) : String}
  %LCl.cl.binds_full(c, y2, LCl.cl.and_l(Cl.binds_fit(c), Cl.ags_fit(f), h23)) : {FCL.run(FCL.get_vals.cfg(ds, _)) == Cl.spell_answer(a) : String}
  %LCl.cl.ags_full(f, "", LCl.cl.and_r(Cl.binds_fit(c), Cl.ags_fit(f), h23)) : {FCL.run(FCL.get_vals.fam(ds, c, _)) == Cl.spell_answer(a) : String}
  %LCl.cl.values_items(ds, ds, c, f, "") : {Wr.put_nat(List.length(&2, Cv.Decl, ds), FCL.put_values.items(ds, ds, c, f, "")) == Wr.put_nat(List.length(&2, Cv.Decl, ds), _) : String}
  {==}

def ca.tog(+ds: List<&2, Cv.Decl>, +c: List<&2, Cv.Bind>, +f: List<&2, Cv.Ag>, +l: Cv.Layer, +x: Nat, +h: {Cl.ask_fits(FCL.AskToggle{ds, c, f, l, x}) == True{} : Bool}) -> {FCL.ffi(Cl.spell_ask(FCL.AskToggle{ds, c, f, l, x})) == Cl.spell_answer(FCL.AskToggle{ds, c, f, l, x}) : String}:
  +a = {FCL.AskToggle{ds, c, f, l, x} : FCL.Ask}
  +y4 = Wr.put_nat(x, "")
  +y3 = Cl.spell_layer(l, y4)
  +y2 = Cl.spell_ags(f, y3)
  +y1 = Cl.spell_binds(c, y2)
  +rest = Bool.and(Cl.binds_fit(c), Bool.and(Cl.ags_fit(f), LawsBase.wire_fits(x)))
  +h2 = LCl.cl.and_r(Cl.decls_fit(ds), rest, h)
  +h3 = LCl.cl.and_r(Cl.binds_fit(c), Bool.and(Cl.ags_fit(f), LawsBase.wire_fits(x)), h2)
  %LWire.pw6.nat(2n, Cl.spell_decls(ds, y1), {==}) : {FCL.run(FCL.get_ask.go(_)) == Cl.spell_answer(a) : String}
  %LCl.cl.decls_full(ds, y1, LCl.cl.and_l(Cl.decls_fit(ds), rest, h)) : {FCL.run(FCL.get_tog(_)) == Cl.spell_answer(a) : String}
  %LCl.cl.binds_full(c, y2, LCl.cl.and_l(Cl.binds_fit(c), Bool.and(Cl.ags_fit(f), LawsBase.wire_fits(x)), h2)) : {FCL.run(FCL.get_tog.cfg(ds, _)) == Cl.spell_answer(a) : String}
  %LCl.cl.ags_full(f, y3, LCl.cl.and_l(Cl.ags_fit(f), LawsBase.wire_fits(x), h3)) : {FCL.run(FCL.get_tog.fam(ds, c, _)) == Cl.spell_answer(a) : String}
  %LCl.cl.layer_rt(l, y4) : {FCL.run(FCL.get_tog.layer(ds, c, f, _)) == Cl.spell_answer(a) : String}
  %LWire.pw6.nat(x, "", LCl.cl.and_r(Cl.ags_fit(f), LawsBase.wire_fits(x), h3)) : {FCL.run(FCL.get_tog.id(ds, c, f, l, _)) == Cl.spell_answer(a) : String}
  LCl.cl.tog_put(Cv.tog(ds, c, f, l, x), "")

def ca.chk(+ds: List<&2, Cv.Decl>, +l: Cv.Layer, +b: Cv.Bind, +h: {Cl.ask_fits(FCL.AskCheck{ds, l, b}) == True{} : Bool}) -> {FCL.ffi(Cl.spell_ask(FCL.AskCheck{ds, l, b})) == Cl.spell_answer(FCL.AskCheck{ds, l, b}) : String}:
  +a = {FCL.AskCheck{ds, l, b} : FCL.Ask}
  +y2 = Cl.spell_bind(b, "")
  +y1 = Cl.spell_layer(l, y2)
  %LWire.pw6.nat(3n, Cl.spell_decls(ds, y1), {==}) : {FCL.run(FCL.get_ask.go(_)) == Cl.spell_answer(a) : String}
  %LCl.cl.decls_full(ds, y1, LCl.cl.and_l(Cl.decls_fit(ds), Cl.bind_fits(b), h)) : {FCL.run(FCL.get_chk(_)) == Cl.spell_answer(a) : String}
  %LCl.cl.layer_rt(l, y2) : {FCL.run(FCL.get_chk.layer(ds, _)) == Cl.spell_answer(a) : String}
  %LCl.cl.bind_rt(b, "", LCl.cl.and_r(Cl.decls_fit(ds), Cl.bind_fits(b), h)) : {FCL.run(FCL.get_chk.set(ds, l, _)) == Cl.spell_answer(a) : String}
  LCl.cl.check_put(Cv.check(ds, l, b), "")

def ca.wr(+ds: List<&2, Cv.Decl>, +ss: List<&2, Cv.Bind>, +g: Cv.Flag, +h: {Cl.ask_fits(FCL.AskWritten{ds, ss, g}) == True{} : Bool}) -> {FCL.ffi(Cl.spell_ask(FCL.AskWritten{ds, ss, g})) == Cl.spell_answer(FCL.AskWritten{ds, ss, g}) : String}:
  +a = {FCL.AskWritten{ds, ss, g} : FCL.Ask}
  +y2 = Cl.spell_flag(g, "")
  +y1 = Cl.spell_binds(ss, y2)
  %LWire.pw6.nat(4n, Cl.spell_decls(ds, y1), {==}) : {FCL.run(FCL.get_ask.go(_)) == Cl.spell_answer(a) : String}
  %LCl.cl.decls_full(ds, y1, LCl.cl.and_l(Cl.decls_fit(ds), Cl.binds_fit(ss), h)) : {FCL.run(FCL.get_wr(_)) == Cl.spell_answer(a) : String}
  %LCl.cl.binds_full(ss, y2, LCl.cl.and_r(Cl.decls_fit(ds), Cl.binds_fit(ss), h)) : {FCL.run(FCL.get_wr.sets(ds, _)) == Cl.spell_answer(a) : String}
  %LCl.cl.flag_rt(g, "") : {FCL.run(FCL.get_wr.flag(ds, ss, _)) == Cl.spell_answer(a) : String}
  LCl.cl.binds_put(Cv.written(ss, ds, g), "")

def ca.doc(+ds: List<&2, Cv.Decl>, +m: List<&2, Cv.Bind>, +g: List<&2, Cv.Bind>, +h: {Cl.ask_fits(FCL.AskDocument{ds, m, g}) == True{} : Bool}) -> {FCL.ffi(Cl.spell_ask(FCL.AskDocument{ds, m, g})) == Cl.spell_answer(FCL.AskDocument{ds, m, g}) : String}:
  +a = {FCL.AskDocument{ds, m, g} : FCL.Ask}
  +y2 = Cl.spell_binds(g, "")
  +y1 = Cl.spell_binds(m, y2)
  +h23 = LCl.cl.and_r(Cl.decls_fit(ds), Bool.and(Cl.binds_fit(m), Cl.binds_fit(g)), h)
  %LWire.pw6.nat(5n, Cl.spell_decls(ds, y1), {==}) : {FCL.run(FCL.get_ask.go(_)) == Cl.spell_answer(a) : String}
  %LCl.cl.decls_full(ds, y1, LCl.cl.and_l(Cl.decls_fit(ds), Bool.and(Cl.binds_fit(m), Cl.binds_fit(g)), h)) : {FCL.run(FCL.get_doc(_)) == Cl.spell_answer(a) : String}
  %LCl.cl.binds_full(m, y2, LCl.cl.and_l(Cl.binds_fit(m), Cl.binds_fit(g), h23)) : {FCL.run(FCL.get_doc.merged(ds, _)) == Cl.spell_answer(a) : String}
  %LCl.cl.binds_full(g, "", LCl.cl.and_r(Cl.binds_fit(m), Cl.binds_fit(g), h23)) : {FCL.run(FCL.get_doc.global(ds, m, _)) == Cl.spell_answer(a) : String}
  LCl.cl.binds_put(Cv.document(ds, m, g), "")

def Cl.cvar_layers_ffi_answers(a, fits):
  match a:
    case FCL.AskRegistry{ds}:
      ca.reg(ds, fits)
    case FCL.AskValues{ds, c, f}:
      ca.vals(ds, c, f, fits)
    case FCL.AskToggle{ds, c, f, l, x}:
      ca.tog(ds, c, f, l, x, fits)
    case FCL.AskCheck{ds, l, b}:
      ca.chk(ds, l, b, fits)
    case FCL.AskWritten{ds, ss, g}:
      ca.wr(ds, ss, g, fits)
    case FCL.AskDocument{ds, m, g}:
      ca.doc(ds, m, g, fits)
