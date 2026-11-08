# eukhe: the proof of LAW semver_digit_exact
#
# PROOF of LAW semver_digit_exact: Sym.of compares the char with '0' to
# '9', then '.', in turn; whatever each compare answers, the digit test of
# the symbol it picks is the or of the ten digit compares (case analysis
# on the compares, taken as free Bools).

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver

# the symbol Sym.of picks from the answers of its eleven compares
def pdg.sym(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, b8: Bool, b9: Bool, bd: Bool) -> Sv.Sym:
  Sv.Sym.when(b0, Sv.Digit{Sv.D0{}}, Sv.Sym.when(b1, Sv.Digit{Sv.D1{}}, Sv.Sym.when(b2, Sv.Digit{Sv.D2{}}, Sv.Sym.when(b3, Sv.Digit{Sv.D3{}}, Sv.Sym.when(b4, Sv.Digit{Sv.D4{}}, Sv.Sym.when(b5, Sv.Digit{Sv.D5{}}, Sv.Sym.when(b6, Sv.Digit{Sv.D6{}}, Sv.Sym.when(b7, Sv.Digit{Sv.D7{}}, Sv.Sym.when(b8, Sv.Digit{Sv.D8{}}, Sv.Sym.when(b9, Sv.Digit{Sv.D9{}}, Sv.Sym.when(bd, Sv.Dot{}, Sv.Other{})))))))))))

def pdg.chain(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, b8: Bool, b9: Bool, bd: Bool) -> {Semver.digit_spec.of(pdg.sym(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bd)) == Bool.or(b0, Bool.or(b1, Bool.or(b2, Bool.or(b3, Bool.or(b4, Bool.or(b5, Bool.or(b6, Bool.or(b7, Bool.or(b8, b9))))))))) : Bool}:
  match b0:
    case True{}:
      {==}
    case False{}:
      match b1:
        case True{}:
          {==}
        case False{}:
          match b2:
            case True{}:
              {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  match b4:
                    case True{}:
                      {==}
                    case False{}:
                      match b5:
                        case True{}:
                          {==}
                        case False{}:
                          match b6:
                            case True{}:
                              {==}
                            case False{}:
                              match b7:
                                case True{}:
                                  {==}
                                case False{}:
                                  match b8:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      match b9:
                                        case True{}:
                                          {==}
                                        case False{}:
                                          match bd:
                                            case True{}:
                                              {==}
                                            case False{}:
                                              {==}

def Semver.semver_digit_exact(c):
  pdg.chain(Char.is_eq(c, '0'), Char.is_eq(c, '1'), Char.is_eq(c, '2'), Char.is_eq(c, '3'), Char.is_eq(c, '4'), Char.is_eq(c, '5'), Char.is_eq(c, '6'), Char.is_eq(c, '7'), Char.is_eq(c, '8'), Char.is_eq(c, '9'), Char.is_eq(c, '.'))
