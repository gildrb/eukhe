# eukhe: the proof of LAW kernel_ready_starts_on_present
#
# Induction on the actions before the start, from any uv, CPython and env
# there: each passes a ready list on to its rest (a Bool.and that is True
# has both sides True) with what it puts there; the CPython fetch and the
# env's making answer their own half; at the start, Bool.and(python, env)
# is True, so both were there.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def kro.G(a: List<&2, KL.Act>, python: Bool, env: Bool) -> Type:
  {Bool.or(python, KernelLocal.kl_has_fetch_python(a)) == True{} : Bool} & {Bool.or(env, KernelLocal.kl_has_make_env(a)) == True{} : Bool}

# Bool.or(b, True) is True
def kro.or_t(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# at the start: the CPython and the env were there
def kro.start(+python: Bool, +env: Bool, -b: Bool, ok: {Bool.and(Bool.and(python, env), b) == True{} : Bool}) -> kro.G(Nil{}, python, env):
  match python env:
    case True{} True{}:
      ({==}, {==})
    case True{} False{}:
      LKL.kl.absurd(kro.G(Nil{}, True{}, False{}), ok)
    case False{} True{}:
      LKL.kl.absurd(kro.G(Nil{}, False{}, True{}), ok)
    case False{} False{}:
      LKL.kl.absurd(kro.G(Nil{}, False{}, False{}), ok)

# after the CPython fetch: the CPython is there; the env as before it
def kro.fetch_python(+python: Bool, -env: Bool, -t: List<&2, KL.Act>, ih: kro.G(t, True{}, env)) -> {Bool.or(python, True{}) == True{} : Bool} & {Bool.or(env, KernelLocal.kl_has_make_env(t)) == True{} : Bool}:
  (fp, me) = ih
  (kro.or_t(python), me)

# after the env's making: the env is there; the CPython as before it
def kro.make_env(-python: Bool, +env: Bool, -t: List<&2, KL.Act>, ih: kro.G(t, python, True{})) -> {Bool.or(python, KernelLocal.kl_has_fetch_python(t)) == True{} : Bool} & {Bool.or(env, True{}) == True{} : Bool}:
  (fp, me) = ih
  (fp, kro.or_t(env))

def KernelLocal.kernel_ready_starts_on_present(a, uv, python, env, b, ok):
  match a:
    case Nil{}:
      kro.start(python, env, KL.acts.ready(b, uv, python, env), ok)
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          KernelLocal.kernel_ready_starts_on_present(t, True{}, python, env, b, ok)
        case KL.FetchPython{h}:
          kro.fetch_python(python, env, t, KernelLocal.kernel_ready_starts_on_present(t, uv, True{}, env, b, LKL.kl.and_r(uv, KL.acts.ready(List.append(&2, KL.Act, t, KL.Run{} <> b), uv, True{}, env), ok)))
        case KL.MakeEnv{}:
          kro.make_env(python, env, t, KernelLocal.kernel_ready_starts_on_present(t, uv, python, True{}, b, LKL.kl.and_r(Bool.and(uv, python), KL.acts.ready(List.append(&2, KL.Act, t, KL.Run{} <> b), uv, python, True{}), ok)))
        case KL.Run{}:
          KernelLocal.kernel_ready_starts_on_present(t, uv, python, env, b, LKL.kl.and_r(Bool.and(python, env), KL.acts.ready(List.append(&2, KL.Act, t, KL.Run{} <> b), uv, python, env), ok))
