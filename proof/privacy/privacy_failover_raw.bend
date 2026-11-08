# eukhe: the proof of LAW privacy_failover_raw
#
# PROOF: the first remote attempt scrubs the raw text; the map after it
# no longer grows on that text and gives the same bytes
# (privacy_token_stable), so every later remote attempt sends the same
# scrub, and every local one the raw text: ptx.failover.

import Base
import ../../bend/privacy/token.bend as Tk
import ./base/text.bend as LPx
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_failover_raw(ts, m, xs):
  LPx.ptx.failover(ts, m, xs)
