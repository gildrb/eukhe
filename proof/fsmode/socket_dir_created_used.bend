# eukhe: the proof of LAW socket_dir_created_used

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

def created_used() -> {Fs.socket_dir(Fs.made(Fs.dir_mode())) == Fs.Use{} : Fs.Verdict}:
  {==}

def Fsmode.socket_dir_created_used():
  created_used()
