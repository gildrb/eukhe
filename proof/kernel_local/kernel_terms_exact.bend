# eukhe: the proof of LAW kernel_terms_exact
# Each predicate by induction on its list, one case per action.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def kt.fetch(xs: List<&2, KL.Act>) -> {KL.acts.fetching(xs) == KernelLocal.fetching_spec(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          {==}
        case KL.FetchPython{h}:
          {==}
        case KL.MakeEnv{}:
          kt.fetch(t)
        case KL.Run{}:
          kt.fetch(t)

def kt.uv(xs: List<&2, KL.Act>) -> {KL.acts.fetches_uv(xs) == KernelLocal.fetches_uv_spec(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          {==}
        case KL.FetchPython{h}:
          kt.uv(t)
        case KL.MakeEnv{}:
          kt.uv(t)
        case KL.Run{}:
          kt.uv(t)

def kt.python(xs: List<&2, KL.Act>) -> {KL.acts.fetches_python(xs) == KernelLocal.fetches_python_spec(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          kt.python(t)
        case KL.FetchPython{h}:
          {==}
        case KL.MakeEnv{}:
          kt.python(t)
        case KL.Run{}:
          kt.python(t)

def kt.env(xs: List<&2, KL.Act>) -> {KL.acts.makes_env(xs) == KernelLocal.makes_env_spec(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          kt.env(t)
        case KL.FetchPython{h}:
          kt.env(t)
        case KL.MakeEnv{}:
          {==}
        case KL.Run{}:
          kt.env(t)

def kt.ver(xs: List<&2, KL.Act>) -> {KL.acts.verified(xs) == KernelLocal.verified_spec(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          match h:
            case True{}:
              kt.ver(t)
            case False{}:
              {==}
        case KL.FetchPython{h}:
          match h:
            case True{}:
              kt.ver(t)
            case False{}:
              {==}
        case KL.MakeEnv{}:
          kt.ver(t)
        case KL.Run{}:
          kt.ver(t)

def kt.ready(xs: List<&2, KL.Act>, +uv: Bool, +python: Bool, +env: Bool) -> {KL.acts.ready(xs, uv, python, env) == KernelLocal.ready_spec(xs, uv, python, env) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          kt.ready(t, True{}, python, env)
        case KL.FetchPython{h}:
          match uv:
            case True{}:
              kt.ready(t, True{}, True{}, env)
            case False{}:
              {==}
        case KL.MakeEnv{}:
          match uv python:
            case True{} True{}:
              kt.ready(t, True{}, True{}, True{})
            case True{} False{}:
              {==}
            case False{} True{}:
              {==}
            case False{} False{}:
              {==}
        case KL.Run{}:
          match python env:
            case True{} True{}:
              kt.ready(t, uv, True{}, True{})
            case True{} False{}:
              {==}
            case False{} True{}:
              {==}
            case False{} False{}:
              {==}

def kt.ends(xs: List<&2, KL.Act>) -> {KL.acts.ends_started(xs) == KernelLocal.ends_started_spec(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          kt.ends(t)
        case KL.FetchPython{h}:
          kt.ends(t)
        case KL.MakeEnv{}:
          kt.ends(t)
        case KL.Run{}:
          match t:
            case Nil{}:
              {==}
            case y <> u:
              {==}

def kt.own(e: KL.End) -> {KL.own_left(e) == KernelLocal.own_left_spec(e) : Nat}:
  match e:
    case KL.Got{}:
      {==}
    case KL.Busy{}:
      {==}
    case KL.Freed{}:
      {==}
    case KL.Crash{}:
      {==}

def KernelLocal.kernel_terms_exact(xs, uv, python, env, e):
  +ys = xs
  (kt.fetch(ys), kt.uv(ys), kt.python(ys), kt.env(ys), kt.ver(ys), kt.ready(ys, uv, python, env), kt.ends(ys), kt.own(e))
