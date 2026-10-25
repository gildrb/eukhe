# eukhe: the proof of LAW glob_items
#
# PROOF: token by token, the code's regex is the spec's (GI.gi.items).

import Base
import ../../bend/glob.bend as G
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/items.bend as GI

def Glob.glob_items(o, g):
  GI.gi.items(o, g)
