# eukhe: the proof of LAW fsmode_ffi_malformed_exact
# The entry reads every input as the laws' reader does; where that reader
# finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_fsmode.bend as FFs
import ../../bend/fsmode.bend as Fs
import ../../bend/wire.bend as Wr
import ../../laws/fsmode.bend as Fsmode
import ./base.bend as LAFs

def fme.end(b: Bool, -a: Fs.Ask, no: {Fsmode.read_ask.end(b, a) == None{} : Maybe<&2, Fs.Ask>}) -> {FFs.run.end(b, a) == SCon{'E', SCon{' ', "fsmode: malformed request"}} : String}:
  match b:
    case True{}:
      LAFs.fs.some_none(Fs.Ask, a, {FFs.answer(a) == SCon{'E', SCon{' ', "fsmode: malformed request"}} : String}, no)
    case False{}:
      {==}

def fme.whole(r: Wr.Dec<Fs.Ask>, no: {Fsmode.read_ask.whole(r) == None{} : Maybe<&2, Fs.Ask>}) -> {FFs.run(r) == SCon{'E', SCon{' ', "fsmode: malformed request"}} : String}:
  match r:
    case Wr.Got{a, s}:
      fme.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def Fsmode.fsmode_ffi_malformed_exact(s, no):
  %LAFs.fs.ask(Wr.get_nat(s)) : {FFs.run(_) == SCon{'E', SCon{' ', "fsmode: malformed request"}} : String}
  fme.whole(Fsmode.read_ask.go(Wr.get_nat(s)), no)
