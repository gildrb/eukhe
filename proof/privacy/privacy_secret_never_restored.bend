# eukhe: the proof of LAW privacy_secret_never_restored
#
# PROOF: a restored token has a class that maps back (psc.rt_none), and
# its value keeps that class: ptx.creds.

import Base
import ../../bend/privacy/token.bend as Tk
import ./base/text.bend as LPx
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_secret_never_restored(m, ys):
  LPx.ptx.creds(m, ys)
