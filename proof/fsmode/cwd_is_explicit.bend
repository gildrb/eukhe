# eukhe: the proof of LAW cwd_is_explicit

import Base
import ../../laws/fsmode.bend as Fsmode
import ../base/fsmode.bend as LFsmode

def Fsmode.cwd_is_explicit(c, p, ok):
  LFsmode.explicit(c, p, ok)
