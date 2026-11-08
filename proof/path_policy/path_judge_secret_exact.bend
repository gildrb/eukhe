# eukhe: the proof of LAW path_judge_secret_exact

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA

# a loop never makes or unmakes a secret
def pp.demote_secret_eq(c: Pp.Cls, l: Bool) -> {Pp.Cls.secret(Pp.demote(c, l)) == Pp.Cls.secret(c) : Bool}:
  match c:
    case Pp.Inside{}:
      match l:
        case True{}:
          {==}
        case False{}:
          {==}
    case Pp.Outside{}:
      {==}
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      {==}

def PathPolicy.path_judge_secret_exact(ro, ru, se, at, l):
  Equal.trans(Bool, Pp.Cls.secret(Pp.demote(Pp.class_of(Pp.Pol{ro, ru, se}, at), l)), Pp.Cls.secret(Pp.class_of(Pp.Pol{ro, ru, se}, at)), PathPolicy.pp_under_any(se, at), pp.demote_secret_eq(Pp.class_of(Pp.Pol{ro, ru, se}, at), l), LA.pp.class_of_secret(ro, ru, se, at))
