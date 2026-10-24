# eukhe: the proof of LAW fsmode_modes_exact

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

def fme2.loose(u: Nat, g: Nat, o: Nat) -> {Fs.Mode.loose(Fs.Mode{u, g, o}) == Bool.or(Fsmode.set_spec(g), Fsmode.set_spec(o)) : Bool}:
  match g o:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      {==}

def Fsmode.fsmode_modes_exact(u, g, o):
  ({==}, {==}, {==}, fme2.loose(u, g, o))
