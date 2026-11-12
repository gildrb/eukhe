# eukhe: the proof of LAW kernel_start_exact
# With all three there both sides are Up; otherwise both are the verdict
# on the steps (ks.ran).

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def ks.ran(ok: Bool) -> {KL.start.ran(ok) == KernelLocal.start_spec.ok(ok) : KL.Kernel}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def KernelLocal.kernel_start_exact(uv, python, env, ok):
  match uv python env:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      ks.ran(ok)
    case True{} False{} True{}:
      ks.ran(ok)
    case True{} False{} False{}:
      ks.ran(ok)
    case False{} True{} True{}:
      ks.ran(ok)
    case False{} True{} False{}:
      ks.ran(ok)
    case False{} False{} True{}:
      ks.ran(ok)
    case False{} False{} False{}:
      ks.ran(ok)
