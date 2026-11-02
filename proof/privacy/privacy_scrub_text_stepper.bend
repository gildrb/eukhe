# eukhe: the proof of LAW privacy_scrub_text_stepper
#
# PROOF: induction on the text: the code's values and fill are the spec's
# (pst.vals, pst.fill): pst.stepper (proof/privacy/base/stext.bend).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy_map.bend as Sm
import ./base/stext.bend as LSt
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_scrub_text_stepper(m, xs):
  LSt.pst.stepper(m, xs)
