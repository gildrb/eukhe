# eukhe: the proof of LAW private_on_create

import Base
import ../../bend/fsmode.bend as Fs
import ../../LAWS.bend as Laws

# What eukhe creates
# ------------------

def private(k: Fs.Made) -> {Fs.Mode.loose(Fs.made_mode(k)) == False{} : Bool}:
  match k:
    case Fs.DirMade{}:
      {==}
    case Fs.FileMade{}:
      {==}

def Laws.private_on_create(k):
  private(k)
