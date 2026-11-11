# eukhe: the proof of LAW shell_within_one_out
# One effect within: it is grantable (so below 7: shwu.code) and auto holds
# it (shwu.elem: the place of its first copy splits auto).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell
import ../base/logic/nat.bend as LLogicNat
import ../base/staging.bend as LStg
import ./base.bend as LASh

def shwu.code(c: Nat, h: {Tl.grantable(c) == True{} : Bool}) -> {Nat.is_lt(c, 7n) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+d:
              match d:
                case 0n:
                  {==}
                case 1n+e:
                  match e:
                    case 0n:
                      {==}
                    case 1n+f:
                      match f:
                        case 0n:
                          {==}
                        case 1n+g:
                          match g:
                            case 0n:
                              {==}
                            case 1n+k:
                              LStg.stg.absurdF({Nat.is_lt(7n+k, 7n) == True{} : Bool}, h)

def shwu.Split(c: Nat, auto: List<&2, Nat>) -> Type:
  Sigma<&1, &1, List<&2, Nat>, pre => Sigma<&1, &1, List<&2, Nat>, post => {auto == List.append(&2, Nat, pre, c <> post) : List<&2, Nat>}>>

def shwu.cons(+y: Nat, -c: Nat, -t: List<&2, Nat>, sp: shwu.Split(c, t)) -> shwu.Split(c, y <> t):
  (pre, rest) = sp
  (post, ep) = rest
  (y <> pre, (post, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, t, List.append(&2, Nat, pre, c <> post), ep)))

def shwu.found(b: Bool, +y: Nat, +c: Nat, +t: List<&2, Nat>, eb: {Nat.is_eq(y, c) == b : Bool}, h: {Bool.or(b, Tl.elem(t, c)) == True{} : Bool}, ih: {Tl.elem(t, c) == True{} : Bool} -> shwu.Split(c, t)) -> shwu.Split(c, y <> t):
  match b:
    case True{}:
      +e = LLogicNat.supervisor.ps.eq_of_is_eq(y, c, eb)
      (Nil{}, (t, Equal.cong(Nat, List<&2, Nat>, z => z <> t, y, c, e)))
    case False{}:
      shwu.cons(y, c, t, ih(h))

def shwu.elem(auto: List<&2, Nat>, +c: Nat, h: {Tl.elem(auto, c) == True{} : Bool}) -> shwu.Split(c, auto):
  match auto:
    case Nil{}:
      LStg.stg.absurdF(shwu.Split(c, Nil{}), h)
    case +y <> +t:
      shwu.found(Nat.is_eq(y, c), y, c, t, {==}, h, hh => shwu.elem(t, c, hh))

def shwu.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def shwu.and_r(a: Bool, +b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LStg.stg.absurdF({b == True{} : Bool}, e)

def shwu.fin(-c: Nat, -auto: List<&2, Nat>, lt: {Nat.is_lt(c, 7n) == True{} : Bool}, sp: shwu.Split(c, auto)) -> Sigma<&1, &1, List<&2, Nat>, pre => Sigma<&1, &1, List<&2, Nat>, post => {auto == List.append(&2, Nat, pre, c <> post) : List<&2, Nat>} & {Nat.is_lt(c, 7n) == True{} : Bool}>>:
  (pre, rest) = sp
  (post, ep) = rest
  (pre, (post, (ep, lt)))

def Shell.shell_within_one_out(c, auto, runs):
  +ge = shwu.and_l(Bool.and(Tl.grantable(c), Tl.elem(auto, c)), True{}, runs)
  +hg = shwu.and_l(Tl.grantable(c), Tl.elem(auto, c), ge)
  +he = shwu.and_r(Tl.grantable(c), Tl.elem(auto, c), ge)
  shwu.fin(c, auto, shwu.code(c, hg), shwu.elem(auto, c, he))
