# eukhe: the proof of LAW socket_dir_created_used

import Base
import ../../bend/fsmode.bend as Fs
import ../../LAWS.bend as Laws

def created_used() -> {Fs.socket_dir(Fs.made(Fs.dir_mode())) == Fs.Use{} : Fs.Verdict}:
  {==}

def Laws.socket_dir_created_used():
  created_used()
