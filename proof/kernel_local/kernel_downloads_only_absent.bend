# eukhe: the proof of LAW kernel_downloads_only_absent
#
# Each of the eight things a setup can find computes: the plan has a
# fetch exactly when the uv or the CPython is not there.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def KernelLocal.kernel_downloads_only_absent(uv, python, env):
  match uv python env:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}
