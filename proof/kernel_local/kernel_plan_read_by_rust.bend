# eukhe: the proof of LAW kernel_plan_read_by_rust
#
# Eight closed cases (uv x CPython x env there or not): Rust's reader
# computes on each plan.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def KernelLocal.kernel_plan_read_by_rust(uv, python, env):
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
