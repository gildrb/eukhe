# eukhe: the proof of LAW run_ffi_reads_only_requests
#
# PROOF: whatever the entry's decoder reads is the spelling of what it
# read, then its rest, and fits the wire (LDk.dk.ask, tag by tag with the
# wire's exactness laws: an unknown tag is Bad); an answer that is no error
# comes from a request read whole, nothing left (ro.fin), and is the
# spelled value of its decision (LSp.sp.answer).

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/run/entry.bend as Run
import ../wire/base/spell.bend as LAWireSpell
import ./run_ffi_answers_spelled/spell.bend as LSp
import ./run_ffi_reads_only_requests/decode.bend as LDk

def ro.G(s: String, x: String) -> Type:
  Sigma<&1, &1, FRn.Ask, a => {(s, (Run.run.ask_fits(a), x)) == (Run.run_spell_ask(a, ""), (True{}, Run.run_spell_answer(a))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def ro.top_eq(+s: String, +a: FRn.Ask, +x: String, e: {s == Run.run_spell_ask(a, "") : String}, f: {Run.run.ask_fits(a) == True{} : Bool}, ex: {x == Run.run_spell_answer(a) : String}) -> {(s, (Run.run.ask_fits(a), x)) == (Run.run_spell_ask(a, ""), (True{}, Run.run_spell_answer(a))) : String & (Bool & String)}:
  %Equal.sym(String, s, Run.run_spell_ask(a, ""), e) : {(_, (Run.run.ask_fits(a), x)) == (Run.run_spell_ask(a, ""), (True{}, Run.run_spell_answer(a))) : String & (Bool & String)}
  %Equal.sym(Bool, Run.run.ask_fits(a), True{}, f) : {(Run.run_spell_ask(a, ""), (_, x)) == (Run.run_spell_ask(a, ""), (True{}, Run.run_spell_answer(a))) : String & (Bool & String)}
  %Equal.sym(String, x, Run.run_spell_answer(a), ex) : {(Run.run_spell_ask(a, ""), (True{}, _)) == (Run.run_spell_ask(a, ""), (True{}, Run.run_spell_answer(a))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def ro.fin(+s: String, +a: FRn.Ask, r: String, pre: {s == Run.run_spell_ask(a, r) : String}, f: {Run.run.ask_fits(a) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FRn.ffi.end(Wr.end(r), a)) == False{} : Bool}) -> ro.G(s, FRn.ffi.end(Wr.end(r), a)):
  match r:
    case SNil{}:
      (a, ro.top_eq(s, a, FRn.ffi.end(True{}, a), pre, f, LSp.sp.answer(a)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(ro.G(s, FRn.ffi.end(False{}, a)), ok)

def ro.main(+s: String, d: Wr.Dec<FRn.Ask>, inv: LDk.dk.Ask(s, d), ok: {LawsBase.wire_opens_err(FRn.ffi.go(d)) == False{} : Bool}) -> ro.G(s, FRn.ffi.go(d)):
  match d:
    case Wr.Got{+a, +r}:
      (e, f) = inv
      ro.fin(s, a, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("run: malformed request")), ok)

def Run.run_ffi_reads_only_requests(s, ok):
  ro.main(s, FRn.get_ask(s), LDk.dk.ask(s), ok)
