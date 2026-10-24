# eukhe: the proof of LAW fsmode_ffi_malformed
# The entry reads every input as the laws' reader does (LAFs.fs.ask); where
# that reader finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_fsmode.bend as FFs
import ../../bend/fsmode.bend as Fs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/fsmode.bend as Fsmode
import ./base.bend as LAFs

def ffm.end(b: Bool, -a: Fs.Ask, no: {Fsmode.read_ask.end(b, a) == None{} : Maybe<&2, Fs.Ask>}) -> {LawsBase.wire_opens_err(FFs.run.end(b, a)) == True{} : Bool}:
  match b:
    case True{}:
      LAFs.fs.some_none(Fs.Ask, a, {LawsBase.wire_opens_err(FFs.answer(a)) == True{} : Bool}, no)
    case False{}:
      {==}

def ffm.whole(r: Wr.Dec<Fs.Ask>, no: {Fsmode.read_ask.whole(r) == None{} : Maybe<&2, Fs.Ask>}) -> {LawsBase.wire_opens_err(FFs.run(r)) == True{} : Bool}:
  match r:
    case Wr.Got{a, s}:
      ffm.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def Fsmode.fsmode_ffi_malformed(s, no):
  %LAFs.fs.ask(Wr.get_nat(s)) : {LawsBase.wire_opens_err(FFs.run(_)) == True{} : Bool}
  ffm.whole(Fsmode.read_ask.go(Wr.get_nat(s)), no)
