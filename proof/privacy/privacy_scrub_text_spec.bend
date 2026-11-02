# eukhe: the proof of LAW privacy_scrub_text_spec
#
# PROOF: induction on the text: the code's values and fill are the spec's
# (pst.vals, pst.fill), so a text scrubbed is the spec's text over the
# stepper's tokens (pst.stepper), and from a map with no value held twice
# those are the spec's (pmp.scrub_vals) (proof/privacy/base/stext.bend).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy_map.bend as Sm
import ./base/stext.bend as LSt
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_scrub_text_spec(m, xs, ok):
  LSt.pst.scrub(m, xs, ok)
