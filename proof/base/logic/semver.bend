# eukhe: lemmas the proofs of two or more areas share: logic/semver

import Base
import ../../../bend/semver.bend as Sv

def rk.ofv(n: Nat) -> Sv.Dig:
  match n:
    case 0n:
      Sv.D0{}
    case 1n+n0:
      match n0:
        case 0n:
          Sv.D1{}
        case 1n+n1:
          match n1:
            case 0n:
              Sv.D2{}
            case 1n+n2:
              match n2:
                case 0n:
                  Sv.D3{}
                case 1n+n3:
                  match n3:
                    case 0n:
                      Sv.D4{}
                    case 1n+n4:
                      match n4:
                        case 0n:
                          Sv.D5{}
                        case 1n+n5:
                          match n5:
                            case 0n:
                              Sv.D6{}
                            case 1n+n6:
                              match n6:
                                case 0n:
                                  Sv.D7{}
                                case 1n+n7:
                                  match n7:
                                    case 0n:
                                      Sv.D8{}
                                    case 1n+n8:
                                      Sv.D9{}
