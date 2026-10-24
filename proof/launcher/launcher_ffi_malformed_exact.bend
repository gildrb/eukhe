# eukhe: the proof of LAW launcher_ffi_malformed_exact
# The entry reads every input as the laws' reader does; where that reader
# finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_launcher.bend as FLa
import ../../bend/launcher.bend as La
import ../../bend/wire.bend as Wr
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def lme.end(b: Bool, -a: La.Ask, no: {Launcher.read_ask.end(b, a) == None{} : Maybe<&2, La.Ask>}) -> {FLa.run.end(b, a) == SCon{'E', SCon{' ', "launcher: malformed request"}} : String}:
  match b:
    case True{}:
      LLa.la.some_none(La.Ask, a, {FLa.answer(a) == SCon{'E', SCon{' ', "launcher: malformed request"}} : String}, no)
    case False{}:
      {==}

def lme.whole(r: Wr.Dec<La.Ask>, no: {Launcher.read_ask.whole(r) == None{} : Maybe<&2, La.Ask>}) -> {FLa.run(r) == SCon{'E', SCon{' ', "launcher: malformed request"}} : String}:
  match r:
    case Wr.Got{a, s}:
      lme.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def Launcher.launcher_ffi_malformed_exact(s, no):
  %LLa.la.ask(Wr.get_nat(s)) : {FLa.run(_) == SCon{'E', SCon{' ', "launcher: malformed request"}} : String}
  lme.whole(Launcher.read_ask.go(Wr.get_nat(s)), no)
