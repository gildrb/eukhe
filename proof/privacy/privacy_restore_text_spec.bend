# eukhe: the proof of LAW privacy_restore_text_spec
#
# PROOF: induction on the text: the code restores piece by piece
# (ptx.restore_cons), and a piece's token by the spec's value (pmp.tok):
# pst.restore (proof/privacy/base/stext.bend).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy_map.bend as Sm
import ./base/stext.bend as LSt
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_restore_text_spec(m, ys):
  LSt.pst.restore(m, ys)
