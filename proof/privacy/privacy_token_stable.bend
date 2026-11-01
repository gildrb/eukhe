# eukhe: the proof of LAW privacy_token_stable
#
# PROOF: every value of the text is held in the map after its scrub, at
# the index it got (psc.tok_ok, ptx.find), so it scrubs to that index and
# leaves the map (psc.held, psc.oneway): ptx.stable.

import Base
import ../../bend/privacy/token.bend as Tk
import ./base/text.bend as LPx
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_token_stable(m, xs):
  LPx.ptx.scrub_stable(m, xs)
