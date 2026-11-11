# eukhe: the proof of LAW cvar_layers_ffi_error_text
#
# PROOF: an answer to a request read whole starts with a spelled Nat
# (wire_nat_not_err), so it is no error; every other input gets the
# entry's one error form.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar_layers.bend as FCL
import ../../bend/wire.bend as Wr
import ../../laws/cvar_layers.bend as Cl
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/base/spell.bend as LAWireSpell

def clet.refusal(f: Cv.Refusal) -> {LawsBase.wire_opens_err(FCL.put_refusal(f, "")) == False{} : Bool}:
  match f:
    case Cv.Accept{}:
      Wire.wire_nat_not_err(0n, "")
    case Cv.Twice{i}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(i, ""))
    case Cv.BadInit{i}:
      Wire.wire_nat_not_err(2n, Wr.put_nat(i, ""))

def clet.tog(t: Cv.Tog) -> {LawsBase.wire_opens_err(FCL.put_tog(t, "")) == False{} : Bool}:
  match t:
    case Cv.TgUndeclared{}:
      Wire.wire_nat_not_err(0n, "")
    case Cv.TgGlobal{}:
      Wire.wire_nat_not_err(1n, "")
    case Cv.TgNotBool{}:
      Wire.wire_nat_not_err(2n, "")
    case Cv.TgFlip{b}:
      Wire.wire_nat_not_err(3n, FCL.put_bind(b, ""))

def clet.check(c: Cv.Check) -> {LawsBase.wire_opens_err(FCL.put_check(c, "")) == False{} : Bool}:
  match c:
    case Cv.CkUndeclared{}:
      Wire.wire_nat_not_err(0n, "")
    case Cv.CkGlobal{}:
      Wire.wire_nat_not_err(1n, "")
    case Cv.CkType{}:
      Wire.wire_nat_not_err(2n, "")
    case Cv.CkFine{}:
      Wire.wire_nat_not_err(3n, "")

# an answer to a request is no error
def clet.answer(a: FCL.Ask) -> {LawsBase.wire_opens_err(FCL.answer(a)) == False{} : Bool}:
  match a:
    case FCL.AskRegistry{ds}:
      clet.refusal(Cv.refusal(ds))
    case FCL.AskValues{+ds, c, f}:
      Wire.wire_nat_not_err(List.length(&2, Cv.Decl, ds), FCL.put_values.items(ds, ds, c, f, ""))
    case FCL.AskToggle{ds, c, f, l, x}:
      clet.tog(Cv.tog(ds, c, f, l, x))
    case FCL.AskCheck{ds, l, b}:
      clet.check(Cv.check(ds, l, b))
    case FCL.AskWritten{ds, ss, g}:
      +w = Cv.written(ss, ds, g)
      Wire.wire_nat_not_err(List.length(&2, Cv.Bind, w), FCL.put_binds.items(w, ""))
    case FCL.AskDocument{ds, m, g}:
      +w = Cv.document(ds, m, g)
      Wire.wire_nat_not_err(List.length(&2, Cv.Bind, w), FCL.put_binds.items(w, ""))

def clet.end(b: Bool, +a: FCL.Ask, bad: {LawsBase.wire_opens_err(FCL.run.end(b, a)) == True{} : Bool}) -> {FCL.run.end(b, a) == SCon{'E', SCon{' ', "cvar_layers: malformed request"}} : String}:
  match b:
    case True{}:
      LAWireSpell.ws_absurd({FCL.answer(a) == SCon{'E', SCon{' ', "cvar_layers: malformed request"}} : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FCL.answer(a)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FCL.answer(a)), True{}, bad), clet.answer(a)))
    case False{}:
      {==}

def clet.run(d: Wr.Dec<FCL.Ask>, bad: {LawsBase.wire_opens_err(FCL.run(d)) == True{} : Bool}) -> {FCL.run(d) == SCon{'E', SCon{' ', "cvar_layers: malformed request"}} : String}:
  match d:
    case Wr.Got{+a, r}:
      clet.end(Wr.end(r), a, bad)
    case Wr.Bad{}:
      {==}

def Cl.cvar_layers_ffi_error_text(s, bad):
  clet.run(FCL.get_ask(s), bad)
