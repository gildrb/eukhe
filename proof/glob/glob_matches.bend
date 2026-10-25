# eukhe: the proof of LAW glob_matches
#
# PROOF: the regex is the spec's (gi.items), and each alternative's match the spec's (gb.full).

import Base
import ../../bend/glob.bend as G
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/query.bend as GQ

def Glob.glob_matches(o, g, s):
  GQ.gq.matches(o, g, s)
