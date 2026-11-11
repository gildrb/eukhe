# eukhe: the proof of LAW shell_within_one_in
# A code below 7 is grantable (shwo.code); auto holds c where it was put
# (shwo.elem); so the one effect is within.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell
import ../base/logic/nat.bend as LLogicNat
import ./base.bend as LASh

def shwo.code(c: Nat, h: {Nat.is_lt(c, 7n) == True{} : Bool}) -> {Tl.grantable(c) == True{} : Bool}:
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
                              match k:
                                case 0n:
                                  h
                                case 1n+m:
                                  h

def shwo.refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      shwo.refl(m)

def shwo.or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def shwo.elem(pre: List<&2, Nat>, +c: Nat, +post: List<&2, Nat>) -> {Tl.elem(List.append(&2, Nat, pre, c <> post), c) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(c, c), True{}, shwo.refl(c)) : {Bool.or(_, Tl.elem(post, c)) == True{} : Bool}
      {==}
    case y <> t:
      %Equal.sym(Bool, Tl.elem(List.append(&2, Nat, t, c <> post), c), True{}, shwo.elem(t, c, post)) : {Bool.or(Nat.is_eq(y, c), _) == True{} : Bool}
      shwo.or_true(Nat.is_eq(y, c))

def Shell.shell_within_one_in(c, pre, post, code):
  %Equal.sym(Bool, Tl.grantable(c), True{}, shwo.code(c, code)) : {Bool.and(Bool.and(_, Tl.elem(List.append(&2, Nat, pre, c <> post), c)), True{}) == True{} : Bool}
  %Equal.sym(Bool, Tl.elem(List.append(&2, Nat, pre, c <> post), c), True{}, shwo.elem(pre, c, post)) : {Bool.and(Bool.and(True{}, _), True{}) == True{} : Bool}
  {==}
