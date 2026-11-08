# eukhe: the proof of LAW gate_secret_read_exact
#
# PROOF: split the access and the class; each side computes.

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/gate.bend as PathPolicyGate

def ppg.secret_read(a: Pp.Acc, c: Pp.Cls) -> {Pp.secret_read(c, a) == PathPolicyGate.pp_secret_read(c, a) : Bool}:
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
      {==}

def PathPolicyGate.gate_secret_read_exact(c, a):
  ppg.secret_read(a, c)
