# eukhe: the proof of LAW socket_dir_created

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

def created(mine: Bool, loose: Bool) -> {Fs.socket_dir(Fs.Seen{Fs.Missing{}, mine, loose}) == Fs.Create{Fs.dir_mode()} : Fs.Verdict}:
  {==}

def Fsmode.socket_dir_created(mine, loose):
  created(mine, loose)
