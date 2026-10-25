# eukhe: the proof of LAW cvar_layers_ffi_malformed_exact
# The entry reads every input as the laws' reader does (LCl.cl.ask); where
# that reader finds no whole request, the entry answers its error form.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar_layers.bend as FCL
import ../../bend/wire.bend as Wr
import ../../laws/cvar_layers.bend as Cl
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LCl

def cm.end(b: Bool, -a: FCL.Ask, no: {Cl.read_ask.end(b, a) == None{} : Maybe<&2, FCL.Ask>}) -> {FCL.run.end(b, a) == SCon{'E', SCon{' ', "cvar_layers: malformed request"}} : String}:
  match b:
    case True{}:
      LCl.cl.some_none(FCL.Ask, a, {FCL.answer(a) == SCon{'E', SCon{' ', "cvar_layers: malformed request"}} : String}, no)
    case False{}:
      {==}

def cm.whole(r: Wr.Dec<FCL.Ask>, no: {Cl.read_ask.whole(r) == None{} : Maybe<&2, FCL.Ask>}) -> {FCL.run(r) == SCon{'E', SCon{' ', "cvar_layers: malformed request"}} : String}:
  match r:
    case Wr.Got{a, s}:
      cm.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def Cl.cvar_layers_ffi_malformed_exact(s, no):
  %LCl.cl.ask(Wr.get_nat(s)) : {FCL.run(_) == SCon{'E', SCon{' ', "cvar_layers: malformed request"}} : String}
  cm.whole(Cl.read_ask.go(Wr.get_nat(s)), no)
