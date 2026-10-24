# eukhe: the proof of LAW fsmode_safe_exact

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

def Fsmode.fsmode_safe_exact(d):
  match d:
    case Fs.Seen{k, mine, loose}:
      match k mine loose:
        case Fs.Missing{} True{} True{}:
          {==}
        case Fs.Missing{} True{} False{}:
          {==}
        case Fs.Missing{} False{} True{}:
          {==}
        case Fs.Missing{} False{} False{}:
          {==}
        case Fs.Dir{} True{} True{}:
          {==}
        case Fs.Dir{} True{} False{}:
          {==}
        case Fs.Dir{} False{} True{}:
          {==}
        case Fs.Dir{} False{} False{}:
          {==}
        case Fs.Link{} True{} True{}:
          {==}
        case Fs.Link{} True{} False{}:
          {==}
        case Fs.Link{} False{} True{}:
          {==}
        case Fs.Link{} False{} False{}:
          {==}
        case Fs.Other{} True{} True{}:
          {==}
        case Fs.Other{} True{} False{}:
          {==}
        case Fs.Other{} False{} True{}:
          {==}
        case Fs.Other{} False{} False{}:
          {==}
