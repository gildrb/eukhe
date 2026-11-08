# eukhe: the proof of LAW privacy_send_spec
#
# PROOF: induction on the attempts: a remote one sends the spec's scrub
# (pst.scrub) and leaves a map with no value held twice (pst.kept), a
# local one the raw text (pst.raw): pst.send (proof/privacy/base/stext.bend).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy_map.bend as Sm
import ./base/stext.bend as LSt
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_send_spec(ts, m, xs, ok):
  LSt.pst.send(ts, m, xs, ok)
