# eukhe: the proof of LAW privacy_restore_tok_spec
#
# PROOF: the code's value of a class at an index is the spec's value at
# that place: pmp.tok (proof/privacy/base/map.bend).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy_map.bend as Sm
import ./base/map.bend as LMp
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_restore_tok_spec(m, c, i):
  LMp.pmp.tok(m, c, i)
