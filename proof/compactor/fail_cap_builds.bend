# eukhe: the proof of LAW fail_cap_builds

import Base
import ../../bend/compactor.bend as C
import ../../LAWS.bend as Laws
import ../base.bend as L

# a built line stays built
def pc.run_made(os: List<&2, C.Outcome>) -> {C.Pend.run(os, C.Made{}) == C.Made{} : C.Pend}:
  match os:
    case Nil{}:
      {==}
    case o <> rest:
      match o:
        case C.Built{}:
          pc.run_made(rest)
        case C.Failed{}:
          pc.run_made(rest)
        case C.Disk{}:
          pc.run_made(rest)
        case C.Stopped{}:
          pc.run_made(rest)

def pc.fail_cap_builds(os: List<&2, C.Outcome>, n: Nat, many: {Nat.is_le(1n+n, C.failures(os)) == True{} : Bool}) -> {C.Pend.run(os, C.Owed{n}) == C.Made{} : C.Pend}:
  match os:
    case Nil{}:
      L.pc.absurd_ft({C.Owed{n} == C.Made{} : C.Pend}, many)
    case o <> rest:
      match o:
        case C.Built{}:
          pc.run_made(rest)
        case C.Failed{}:
          match n:
            case 0n:
              pc.run_made(rest)
            case 1n+m:
              pc.fail_cap_builds(rest, m, many)
        case C.Disk{}:
          pc.fail_cap_builds(rest, n, many)
        case C.Stopped{}:
          pc.fail_cap_builds(rest, n, many)

def Laws.fail_cap_builds(n, os, many):
  pc.fail_cap_builds(os, n, many)
