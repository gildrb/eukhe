# eukhe: the proof of LAW privacy_map_scrub_spec
#
# PROOF: induction on the values: with no class holding a value twice,
# the code's find is the place of the value among its class's values
# (pmp.find) and its count their number (pmp.count), so each value's
# token and map are the spec's (pmp.val), and the map after it again
# holds no value twice (pmp.kept) (proof/privacy/base/map.bend).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy_map.bend as Sm
import ./base/map.bend as LMp
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_map_scrub_spec(b, vs, ok):
  LMp.pmp.scrub_vals(vs, b, ok)
