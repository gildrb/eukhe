# eukhe: the proof of LAW glob_full
#
# PROOF: the table holds, for each suffix of the items, the spec's answer (GB.gb.rows, by induction on the text then the items); its head is the answer.

import Base
import ../../bend/glob.bend as G
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/match.bend as GB

def Glob.glob_full(bs, its):
  GB.gb.full(bs, its)
