# eukhe: the proof of LAW kernel_ffi_malformed_exact
# The entry reads every input as the laws' reader does; where that reader
# finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_kernel_local.bend as FKL
import ../../bend/kernel_local.bend as KL
import ../../bend/wire.bend as Wr
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def kme.end(b: Bool, -a: KL.Ask, no: {KernelLocal.read_ask.end(b, a) == None{} : Maybe<&2, KL.Ask>}) -> {FKL.run.end(b, a) == SCon{'E', SCon{' ', "kernel_local: malformed request"}} : String}:
  match b:
    case True{}:
      LKL.kl.some_none(KL.Ask, a, {FKL.answer(a) == SCon{'E', SCon{' ', "kernel_local: malformed request"}} : String}, no)
    case False{}:
      {==}

def kme.whole(r: Wr.Dec<KL.Ask>, no: {KernelLocal.read_ask.whole(r) == None{} : Maybe<&2, KL.Ask>}) -> {FKL.run(r) == SCon{'E', SCon{' ', "kernel_local: malformed request"}} : String}:
  match r:
    case Wr.Got{a, s}:
      kme.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def KernelLocal.kernel_ffi_malformed_exact(s, no):
  %LKL.kl.ask(Wr.get_nat(s)) : {FKL.run(_) == SCon{'E', SCon{' ', "kernel_local: malformed request"}} : String}
  kme.whole(KernelLocal.read_ask.go(Wr.get_nat(s)), no)
