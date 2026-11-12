# eukhe: the proof of LAW mode_tight_is_private
# A group or other digit past 0 makes the mode loose (Mode.loose is the or
# of the two digits' set tests), which the premise excludes.

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode
import ./base.bend as LA

def Fsmode.mode_tight_is_private(u, g, o, tight):
  match g:
    case 0n:
      match o:
        case 0n:
          ({==}, {==})
        case 1n+q:
          LA.fsmode.pf.absurdT({0n == 0n : Nat} & {1n+q == 0n : Nat}, tight)
    case 1n+p:
      LA.fsmode.pf.absurdT({1n+p == 0n : Nat} & {o == 0n : Nat}, tight)
