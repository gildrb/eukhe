# eukhe: the proof of LAW cvar_layers_ffi_reads_only_requests
#
# PROOF: whatever the entry's decoder reads is a spelled request that fits,
# then its rest (LR.clr.ask); an answer that is no error comes from a
# request read whole, nothing left, and is the entry's answer, which the
# laws' spellers write (LCl.cl.answer).

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar_layers.bend as FCL
import ../../bend/wire.bend as Wr
import ../../laws/cvar_layers.bend as Cl
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LCl
import ./base/read.bend as LR

def clro.G(s: String, ans: String) -> Type:
  &a: FCL.Ask -> {(s, (Cl.ask_fits(a), ans)) == (Cl.spell_ask(a), (True{}, Cl.spell_answer(a))) : String & (Bool & String)}

def clro.eq(+s: String, +a: FCL.Ask, +ans: String, e: {s == Cl.spell_ask(a) : String}, f: {Cl.ask_fits(a) == True{} : Bool}, ea: {ans == Cl.spell_answer(a) : String}) -> {(s, (Cl.ask_fits(a), ans)) == (Cl.spell_ask(a), (True{}, Cl.spell_answer(a))) : String & (Bool & String)}:
  %Equal.sym(String, s, Cl.spell_ask(a), e) : {(_, (Cl.ask_fits(a), ans)) == (Cl.spell_ask(a), (True{}, Cl.spell_answer(a))) : String & (Bool & String)}
  %Equal.sym(Bool, Cl.ask_fits(a), True{}, f) : {(Cl.spell_ask(a), (_, ans)) == (Cl.spell_ask(a), (True{}, Cl.spell_answer(a))) : String & (Bool & String)}
  %Equal.sym(String, ans, Cl.spell_answer(a), ea) : {(Cl.spell_ask(a), (True{}, _)) == (Cl.spell_ask(a), (True{}, Cl.spell_answer(a))) : String & (Bool & String)}
  {==}

def clro.fin(+s: String, +a: FCL.Ask, r: String, pre: {s == LR.clr.ask_onto(a, r) : String}, f: {Cl.ask_fits(a) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FCL.run.end(Wr.end(r), a)) == False{} : Bool}) -> clro.G(s, FCL.run.end(Wr.end(r), a)):
  match r:
    case SNil{}:
      (a, clro.eq(s, a, FCL.answer(a), Equal.trans(String, s, LR.clr.ask_onto(a, ""), Cl.spell_ask(a), pre, LR.clr.ask_onto_nil(a)), f, LCl.cl.answer(a)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(clro.G(s, FCL.run.end(False{}, a)), ok)

def clro.main(+s: String, d: Wr.Dec<FCL.Ask>, inv: LR.clr.Ask(s, d), ok: {LawsBase.wire_opens_err(FCL.run(d)) == False{} : Bool}) -> clro.G(s, FCL.run(d)):
  match d:
    case Wr.Got{+a, +r}:
      (e, f) = inv
      clro.fin(s, a, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(clro.G(s, FCL.fail()), ok)

def Cl.cvar_layers_ffi_reads_only_requests(s, ok):
  clro.main(s, FCL.get_ask(s), LR.clr.ask(s), ok)
