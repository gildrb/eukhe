# eukhe: the proof of LAW privacy_map_distinct_kept
#
# PROOF: the empty map computes; a scrub keeps the map, or adds a value its
# class does not hold (pmp.kept), one value at a time (pmp.dk)
# (proof/privacy/base/map.bend).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy_map.bend as Sm
import ./base/map.bend as LMp
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_map_distinct_kept(b, vs, ok):
  ({==}, LMp.pmp.dk(vs, b, ok))
