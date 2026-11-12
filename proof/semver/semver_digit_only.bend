# eukhe: the proof of LAW semver_digit_only

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ../wire/wire_nat_exact.bend as PWireNatExact

# PROOF of LAW semver_digit_only: Sym.of compares the char with '0' to
# '9', then '.', in turn (taken as free Bools, pdo.sym). It answers the
# digit d only from a compare with d's char that answered True: Char.is_eq
# is equality (pdo.char_eq, from U32.is_eq: wn_eq_sound), and Digit{k} is
# Digit{d} only for k = d. '.' and any other char give no digit.

# the symbol Sym.of picks from the answers of its eleven compares
def pdo.sym(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, b8: Bool, b9: Bool, bd: Bool) -> Sv.Sym:
  Sv.Sym.when(b0, Sv.Digit{Sv.D0{}}, Sv.Sym.when(b1, Sv.Digit{Sv.D1{}}, Sv.Sym.when(b2, Sv.Digit{Sv.D2{}}, Sv.Sym.when(b3, Sv.Digit{Sv.D3{}}, Sv.Sym.when(b4, Sv.Digit{Sv.D4{}}, Sv.Sym.when(b5, Sv.Digit{Sv.D5{}}, Sv.Sym.when(b6, Sv.Digit{Sv.D6{}}, Sv.Sym.when(b7, Sv.Digit{Sv.D7{}}, Sv.Sym.when(b8, Sv.Digit{Sv.D8{}}, Sv.Sym.when(b9, Sv.Digit{Sv.D9{}}, Sv.Sym.when(bd, Sv.Dot{}, Sv.Other{})))))))))))

# the digit of a symbol, D0 for none
def pdo.dig(y: Sv.Sym) -> Sv.Dig:
  match y:
    case Sv.Digit{k}:
      k
    case Sv.Dot{}:
      Sv.D0{}
    case Sv.Other{}:
      Sv.D0{}

def pdo.IfD(y: Sv.Sym, G: Type) -> Type:
  match y:
    case Sv.Digit{k}:
      G
    case Sv.Dot{}:
      Unit
    case Sv.Other{}:
      Unit

# a symbol that is no digit is not Digit{d}
def pdo.dot(-G: Type, -d: Sv.Dig, e: {Sv.Dot{} == Sv.Digit{d} : Sv.Sym}) -> G:
  %e : pdo.IfD(_, G)
  Unit{}

def pdo.other(-G: Type, -d: Sv.Dig, e: {Sv.Other{} == Sv.Digit{d} : Sv.Sym}) -> G:
  %e : pdo.IfD(_, G)
  Unit{}

# Char.is_eq is equality
def pdo.char_eq(c: Char, k: Char, e: {Char.is_eq(c, k) == True{} : Bool}) -> {c == k : Char}:
  match c k:
    case Chr{+x} Chr{+y}:
      Equal.cong(U32, Char, u => Chr{u}, x, y, PWireNatExact.wn_eq_sound(x, y, e))

# a compare with k's char answered True and picked Digit{k}, which is Digit{d}
def pdo.hit(-c: Char, -k: Sv.Dig, -d: Sv.Dig, ec: {c == Sv.Dig.chr(k) : Char}, h: {Sv.Digit{k} == Sv.Digit{d} : Sv.Sym}) -> {c == Sv.Dig.chr(d) : Char}:
  Equal.trans(Char, c, Sv.Dig.chr(k), Sv.Dig.chr(d), ec, Equal.cong(Sv.Dig, Char, Sv.Dig.chr, k, d, Equal.cong(Sv.Sym, Sv.Dig, pdo.dig, Sv.Digit{k}, Sv.Digit{d}, h)))

def pdo.chain(+c: Char, -d: Sv.Dig, b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, b8: Bool, b9: Bool, bd: Bool, e0: {Char.is_eq(c, '0') == b0 : Bool}, e1: {Char.is_eq(c, '1') == b1 : Bool}, e2: {Char.is_eq(c, '2') == b2 : Bool}, e3: {Char.is_eq(c, '3') == b3 : Bool}, e4: {Char.is_eq(c, '4') == b4 : Bool}, e5: {Char.is_eq(c, '5') == b5 : Bool}, e6: {Char.is_eq(c, '6') == b6 : Bool}, e7: {Char.is_eq(c, '7') == b7 : Bool}, e8: {Char.is_eq(c, '8') == b8 : Bool}, e9: {Char.is_eq(c, '9') == b9 : Bool}, h: {pdo.sym(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bd) == Sv.Digit{d} : Sv.Sym}) -> {c == Sv.Dig.chr(d) : Char}:
  match b0:
    case True{}:
      pdo.hit(c, Sv.D0{}, d, pdo.char_eq(c, '0', e0), h)
    case False{}:
      match b1:
        case True{}:
          pdo.hit(c, Sv.D1{}, d, pdo.char_eq(c, '1', e1), h)
        case False{}:
          match b2:
            case True{}:
              pdo.hit(c, Sv.D2{}, d, pdo.char_eq(c, '2', e2), h)
            case False{}:
              match b3:
                case True{}:
                  pdo.hit(c, Sv.D3{}, d, pdo.char_eq(c, '3', e3), h)
                case False{}:
                  match b4:
                    case True{}:
                      pdo.hit(c, Sv.D4{}, d, pdo.char_eq(c, '4', e4), h)
                    case False{}:
                      match b5:
                        case True{}:
                          pdo.hit(c, Sv.D5{}, d, pdo.char_eq(c, '5', e5), h)
                        case False{}:
                          match b6:
                            case True{}:
                              pdo.hit(c, Sv.D6{}, d, pdo.char_eq(c, '6', e6), h)
                            case False{}:
                              match b7:
                                case True{}:
                                  pdo.hit(c, Sv.D7{}, d, pdo.char_eq(c, '7', e7), h)
                                case False{}:
                                  match b8:
                                    case True{}:
                                      pdo.hit(c, Sv.D8{}, d, pdo.char_eq(c, '8', e8), h)
                                    case False{}:
                                      match b9:
                                        case True{}:
                                          pdo.hit(c, Sv.D9{}, d, pdo.char_eq(c, '9', e9), h)
                                        case False{}:
                                          match bd:
                                            case True{}:
                                              pdo.dot({c == Sv.Dig.chr(d) : Char}, d, h)
                                            case False{}:
                                              pdo.other({c == Sv.Dig.chr(d) : Char}, d, h)

def Semver.semver_digit_only(c, d, h):
  pdo.chain(c, d, Char.is_eq(c, '0'), Char.is_eq(c, '1'), Char.is_eq(c, '2'), Char.is_eq(c, '3'), Char.is_eq(c, '4'), Char.is_eq(c, '5'), Char.is_eq(c, '6'), Char.is_eq(c, '7'), Char.is_eq(c, '8'), Char.is_eq(c, '9'), Char.is_eq(c, '.'), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, h)
