# eukhe: the proof of LAW privacy_scrub_hides
#
# PROOF: each value's token is mapped exactly when its class maps back
# (psc.tok_ok): ptx.shape.

import Base
import ../../bend/privacy/token.bend as Tk
import ./base/text.bend as LPx
import ../../spec/harness/privacy.bend as S
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_scrub_hides(m, xs):
  +r = Tk.scrub_vals(Tk.vals(xs), m)
  %Equal.sym(List<&2, Tk.Seg>, Tk.Out.ys(Tk.scrub.fill(xs, r)), Tk.fill(xs, Tk.Toks.ts(r)), LPx.ptx.out_ys(xs, r)) : {S.erase(_) == S.shape(xs) : List<&2, Tk.Seg>}
  LPx.ptx.shape(xs, m)
