# eukhe: the proof of LAW private_on_create

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

# What eukhe creates
# ------------------

def private(k: Fs.Made) -> {Fs.Mode.loose(Fs.made_mode(k)) == False{} : Bool}:
  match k:
    case Fs.DirMade{}:
      {==}
    case Fs.FileMade{}:
      {==}

def Fsmode.private_on_create(k):
  private(k)
