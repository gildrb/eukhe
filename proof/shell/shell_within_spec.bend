# eukhe: the proof of LAW shell_within_spec
# Tl.grantable is the effect codes 0 to 6 (shwi.code) and Tl.elem the
# spec's membership (shwi.has); then effect by effect.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell

def shwi.code(c: Nat) -> {Tl.grantable(c) == Shell.sh_code(c) : Bool}:
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
                            case 1n+h:
                              match h:
                                case 0n:
                                  {==}
                                case 1n+k:
                                  {==}

def shwi.has(xs: List<&2, Nat>, +x: Nat) -> {Tl.elem(xs, x) == Shell.sh_has(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> rest:
      %shwi.has(rest, x) : {Bool.or(Nat.is_eq(y, x), Tl.elem(rest, x)) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def Shell.shell_within_spec(es, auto):
  match es:
    case Nil{}:
      {==}
    case +c <> +rest:
      %Shell.shell_within_spec(rest, auto) : {Tl.within(c <> rest, auto) == Bool.and(Bool.and(Shell.sh_code(c), Shell.sh_has(auto, c)), _) : Bool}
      %shwi.has(auto, c) : {Tl.within(c <> rest, auto) == Bool.and(Bool.and(Shell.sh_code(c), _), Tl.within(rest, auto)) : Bool}
      %shwi.code(c) : {Tl.within(c <> rest, auto) == Bool.and(Bool.and(_, Tl.elem(auto, c)), Tl.within(rest, auto)) : Bool}
      {==}
