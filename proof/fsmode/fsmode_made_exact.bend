# eukhe: the proof of LAW fsmode_made_exact

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

def Fsmode.fsmode_made_exact(m):
  match m:
    case Fs.Mode{u, g, o}:
      {==}
