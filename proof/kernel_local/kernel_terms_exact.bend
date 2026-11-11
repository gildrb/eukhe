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
        case KL.Fetch{h}:
          {==}
        case KL.Offline{}:
          kt.fetch(t)
        case KL.Check{}:
          kt.fetch(t)
        case KL.Run{}:
          kt.fetch(t)

def kt.runs(xs: List<&2, KL.Act>) -> {KL.acts.runs(xs) == KernelLocal.runs_spec(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case KL.Fetch{h}:
          kt.runs(t)
        case KL.Offline{}:
          kt.runs(t)
        case KL.Check{}:
          kt.runs(t)
        case KL.Run{}:
          {==}

def kt.ver(xs: List<&2, KL.Act>, c: Bool) -> {KL.acts.verified(xs, c) == KernelLocal.verified_spec(xs, c) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case KL.Fetch{h}:
          match h:
            case True{}:
              kt.ver(t, False{})
            case False{}:
              {==}
        case KL.Offline{}:
          kt.ver(t, c)
        case KL.Check{}:
          kt.ver(t, True{})
        case KL.Run{}:
          match c:
            case True{}:
              kt.ver(t, True{})
            case False{}:
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

def KernelLocal.kernel_terms_exact(xs, c, e):
  +ys = xs
  (kt.fetch(ys), kt.runs(ys), kt.ver(ys, c), kt.own(e))
