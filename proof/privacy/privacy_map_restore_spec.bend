# eukhe: the proof of LAW privacy_map_restore_spec
#
# PROOF: induction on the tokens: the code's value of a class at an index
# is the spec's value at that place (pmp.value: the code's count of the
# older values is their number), and a one-way class restores nothing on
# both sides (pmp.tok) (proof/privacy/base/map.bend).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy_map.bend as Sm
import ./base/map.bend as LMp
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_map_restore_spec(b, rs):
  LMp.pmp.restore_toks(rs, b)
