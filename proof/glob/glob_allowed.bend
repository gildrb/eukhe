# eukhe: the proof of LAW glob_allowed
#
# PROOF: pattern by pattern (ga.one): the trim, the wildcard test, the bare id and the glob's search are the spec's.

import Base
import ../../bend/glob.bend as G
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/allow.bend as GA

def Glob.glob_allowed(sel, ps):
  GA.ga.allowed(sel, ps)
