# eukhe: the proof of LAW once_recover_is_spec
#
# PROOF: every case of the life, the world's answer, the mode and the
# policy computes on both sides; a keyed effect's count against its cap
# is LA.ob.keyed.

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ./base.bend as LA

def Once.once_recover_is_spec(l, s, m, p):
  match l:
    case O.Absent{}:
      {==}
    case O.Pending{}:
      match m:
        case O.Resume{}:
          {==}
        case O.Stop{}:
          {==}
    case O.Running{again}:
      match s:
        case O.Dark{}:
          match m:
            case O.Resume{}:
              match p:
                case O.Never{}:
                  {==}
                case O.Safe{}:
                  {==}
                case O.Keyed{cap}:
                  LA.ob.keyed(cap, again)
            case O.Stop{}:
              match p:
                case O.Never{}:
                  {==}
                case O.Safe{}:
                  {==}
                case O.Keyed{cap}:
                  {==}
        case O.Landed{}:
          match m:
            case O.Resume{}:
              match p:
                case O.Never{}:
                  {==}
                case O.Safe{}:
                  {==}
                case O.Keyed{cap}:
                  {==}
            case O.Stop{}:
              match p:
                case O.Never{}:
                  {==}
                case O.Safe{}:
                  {==}
                case O.Keyed{cap}:
                  {==}
        case O.Clean{}:
          match m:
            case O.Resume{}:
              match p:
                case O.Never{}:
                  {==}
                case O.Safe{}:
                  {==}
                case O.Keyed{cap}:
                  {==}
            case O.Stop{}:
              match p:
                case O.Never{}:
                  {==}
                case O.Safe{}:
                  {==}
                case O.Keyed{cap}:
                  {==}
    case O.Ran{}:
      {==}
    case O.Lost{}:
      {==}
    case O.Void{}:
      {==}
