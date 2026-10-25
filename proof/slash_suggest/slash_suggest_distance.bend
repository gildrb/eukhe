# eukhe: the proof of LAW slash_suggest_distance
#
# PROOF: the code's row of distances is the spec's distance to each suffix of
# the second name (LA.ssb.row, by induction on the first name, then on
# the second); its head is the distance to the whole name.

import Base
import ../../bend/slash_suggest.bend as Ss
import ../../bend/ffi_slash_suggest.bend as FSs
import ../../bend/skill_load.bend as Sl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/slash_suggest.bend as SlashSuggest
import ./base.bend as LA

def SlashSuggest.slash_suggest_distance(a, b):
  LA.ssb.dist(a, b)
