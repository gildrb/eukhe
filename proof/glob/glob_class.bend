# eukhe: the proof of LAW glob_class
#
# PROOF: the code's class test is the spec's (GB.gb.bc: by the class, then the ranges).

import Base
import ../../bend/glob.bend as G
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/match.bend as GB

def Glob.glob_class(k, x):
  GB.gb.bc(k, x)
