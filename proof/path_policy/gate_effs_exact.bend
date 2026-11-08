# eukhe: the proof of LAW gate_effs_exact
#
# PROOF: split the access, the search's holds and the class; each side
# computes.

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/gate.bend as PathPolicyGate

def ppg.effs(a: Pp.Acc, c: Pp.Cls) -> {Pp.effs(c, a) == PathPolicyGate.pp_effs(c, a) : List<&2, Nat>}:
  match a:
    case Pp.Rd{}:
      match c:
        case Pp.Inside{}:
          {==}
        case Pp.Outside{}:
          {==}
        case Pp.Protected{}:
          {==}
        case Pp.Secret{}:
          {==}
    case Pp.Ls{}:
      match c:
        case Pp.Inside{}:
          {==}
        case Pp.Outside{}:
          {==}
        case Pp.Protected{}:
          {==}
        case Pp.Secret{}:
          {==}
    case Pp.Sr{h}:
      match h:
        case True{}:
          match c:
            case Pp.Inside{}:
              {==}
            case Pp.Outside{}:
              {==}
            case Pp.Protected{}:
              {==}
            case Pp.Secret{}:
              {==}
        case False{}:
          match c:
            case Pp.Inside{}:
              {==}
            case Pp.Outside{}:
              {==}
            case Pp.Protected{}:
              {==}
            case Pp.Secret{}:
              {==}
    case Pp.Wr{}:
      match c:
        case Pp.Inside{}:
          {==}
        case Pp.Outside{}:
          {==}
        case Pp.Protected{}:
          {==}
        case Pp.Secret{}:
          {==}

def PathPolicyGate.gate_effs_exact(c, a):
  ppg.effs(a, c)
