# eukhe: the proof of LAW cvar_layers_ffi_exact
# The entry reads every input as the laws' reader does (LCl.cl.ask); a
# whole request is answered by the entry's writers, which write what the
# laws' spellers write for every request (cxe.answer, from LCl.cl.*_put
# and LCl.cl.values_items); anything else gets the one error form.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar_layers.bend as FCL
import ../../bend/wire.bend as Wr
import ../../laws/cvar_layers.bend as Cl
import ./base.bend as LCl

# the entry's writers answer every request as the laws spell the decision
def cxe.answer(a: FCL.Ask) -> {FCL.answer(a) == Cl.spell_answer(a) : String}:
  match a:
    case FCL.AskRegistry{ds}:
      LCl.cl.refusal_put(Cv.refusal(ds), "")
    case FCL.AskValues{+ds, c, f}:
      %LCl.cl.values_items(ds, ds, c, f, "") : {Wr.put_nat(List.length(&2, Cv.Decl, ds), FCL.put_values.items(ds, ds, c, f, "")) == Wr.put_nat(List.length(&2, Cv.Decl, ds), _) : String}
      {==}
    case FCL.AskToggle{ds, c, f, l, x}:
      LCl.cl.tog_put(Cv.tog(ds, c, f, l, x), "")
    case FCL.AskCheck{ds, l, b}:
      LCl.cl.check_put(Cv.check(ds, l, b), "")
    case FCL.AskWritten{ds, ss, g}:
      LCl.cl.binds_put(Cv.written(ss, ds, g), "")
    case FCL.AskDocument{ds, m, g}:
      LCl.cl.binds_put(Cv.document(ds, m, g), "")

def cxe.end(b: Bool, a: FCL.Ask) -> {FCL.run.end(b, a) == Cl.ffi_spec.of(Cl.read_ask.end(b, a)) : String}:
  match b:
    case True{}:
      cxe.answer(a)
    case False{}:
      {==}

def cxe.whole(r: Wr.Dec<FCL.Ask>) -> {FCL.run(r) == Cl.ffi_spec.of(Cl.read_ask.whole(r)) : String}:
  match r:
    case Wr.Got{a, s}:
      cxe.end(Wr.end(s), a)
    case Wr.Bad{}:
      {==}

def Cl.cvar_layers_ffi_exact(s):
  %LCl.cl.ask(Wr.get_nat(s)) : {FCL.run(_) == Cl.ffi_spec(s) : String}
  cxe.whole(Cl.read_ask.go(Wr.get_nat(s)))
