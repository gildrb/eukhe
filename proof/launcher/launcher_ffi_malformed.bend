# eukhe: the proof of LAW launcher_ffi_malformed
# The entry reads every input as the laws' reader does (LLa.la.ask); where
# that reader finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_launcher.bend as FLa
import ../../bend/launcher.bend as La
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def lfm.end(b: Bool, -a: La.Ask, no: {Launcher.read_ask.end(b, a) == None{} : Maybe<&2, La.Ask>}) -> {LawsBase.wire_opens_err(FLa.run.end(b, a)) == True{} : Bool}:
  match b:
    case True{}:
      LLa.la.some_none(La.Ask, a, {LawsBase.wire_opens_err(FLa.answer(a)) == True{} : Bool}, no)
    case False{}:
      {==}

def lfm.whole(r: Wr.Dec<La.Ask>, no: {Launcher.read_ask.whole(r) == None{} : Maybe<&2, La.Ask>}) -> {LawsBase.wire_opens_err(FLa.run(r)) == True{} : Bool}:
  match r:
    case Wr.Got{a, s}:
      lfm.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def Launcher.launcher_ffi_malformed(s, no):
  %LLa.la.ask(Wr.get_nat(s)) : {LawsBase.wire_opens_err(FLa.run(_)) == True{} : Bool}
  lfm.whole(Launcher.read_ask.go(Wr.get_nat(s)), no)
