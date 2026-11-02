# eukhe: the proof of LAW fsmode_made_exact

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

def Fsmode.fsmode_made_exact(m):
  match m:
    case Fs.Mode{u, g, o}:
      match g o:
        case 0n 0n:
          {==}
        case 0n 1n+q:
          {==}
        case 1n+p 0n:
          {==}
        case 1n+p 1n+q:
          {==}
