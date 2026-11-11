# eukhe: the proof of LAW kernel_missing_names_failed_step
# A setup that found all three there contradicts the premise; every other
# one leaves the kernel Missing when its step failed.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

# Logic
# -----

def pk.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# a claim that True is False proves anything
def pk.true_false(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pk.BD(_, Unit, A)
  Unit{}

def pk.missing_names_failed_step(uv: Bool, python: Bool, env: Bool, absent: {Bool.and(uv, Bool.and(python, env)) == False{} : Bool}) -> {KL.answer(KL.Python{}, KL.start(uv, python, env, False{})) == KL.NamesFailed{} : KL.Answer}:
  match uv python env:
    case True{} True{} True{}:
      pk.true_false({KL.answer(KL.Python{}, KL.Up{}) == KL.NamesFailed{} : KL.Answer}, absent)
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

def KernelLocal.kernel_missing_names_failed_step(uv, python, env, absent):
  pk.missing_names_failed_step(uv, python, env, absent)
