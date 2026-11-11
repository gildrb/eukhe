# eukhe: the proof of LAW kernel_missing_spares_tools

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

# The session's tools
# -------------------

def pk.missing_spares_tools(n: Nat, f: KL.Found, ok: Bool) -> {KL.answer(KL.Other{n}, KL.start(f, ok)) == KL.Ran{} : KL.Answer}:
  {==}

def KernelLocal.kernel_missing_spares_tools(n, f, ok):
  pk.missing_spares_tools(n, f, ok)
