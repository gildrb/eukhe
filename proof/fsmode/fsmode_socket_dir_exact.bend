# eukhe: the proof of LAW fsmode_socket_dir_exact

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

def Fsmode.fsmode_socket_dir_exact(d):
  match d:
    case Fs.Seen{k, mine, loose}:
      match k mine loose:
        case Fs.Missing{} _ _:
          {==}
        case Fs.Dir{} True{} True{}:
          {==}
        case Fs.Dir{} True{} False{}:
          {==}
        case Fs.Dir{} False{} True{}:
          {==}
        case Fs.Dir{} False{} False{}:
          {==}
        case Fs.Link{} _ _:
          {==}
        case Fs.Other{} _ _:
          {==}
