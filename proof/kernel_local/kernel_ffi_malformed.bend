# eukhe: the proof of LAW kernel_ffi_malformed
# The entry reads every input as the laws' reader does (LKL.kl.ask); where
# that reader finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_kernel_local.bend as FKL
import ../../bend/kernel_local.bend as KL
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def km.end(b: Bool, -a: KL.Ask, no: {KernelLocal.read_ask.end(b, a) == None{} : Maybe<&2, KL.Ask>}) -> {LawsBase.wire_opens_err(FKL.run.end(b, a)) == True{} : Bool}:
  match b:
    case True{}:
      LKL.kl.some_none(KL.Ask, a, {LawsBase.wire_opens_err(FKL.answer(a)) == True{} : Bool}, no)
    case False{}:
      {==}

def km.whole(r: Wr.Dec<KL.Ask>, no: {KernelLocal.read_ask.whole(r) == None{} : Maybe<&2, KL.Ask>}) -> {LawsBase.wire_opens_err(FKL.run(r)) == True{} : Bool}:
  match r:
    case Wr.Got{a, s}:
      km.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def KernelLocal.kernel_ffi_malformed(s, no):
  %LKL.kl.ask(Wr.get_nat(s)) : {LawsBase.wire_opens_err(FKL.run(_)) == True{} : Bool}
  km.whole(KernelLocal.read_ask.go(Wr.get_nat(s)), no)
