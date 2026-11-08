# eukhe: the proof of LAW privacy_round_trip
#
# PROOF: as privacy_round_trip_exact (ptx.round_trip); a text with no
# credential is its own mask (ptx.mask_raw).

import Base
import ../../bend/privacy/token.bend as Tk
import ./base/text.bend as LPx
import ../../spec/harness/privacy.bend as S
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_round_trip(m, xs, ok):
  +r = Tk.scrub_vals(Tk.vals(xs), m)
  %Equal.sym(Tk.Book, Tk.Out.m(Tk.scrub.fill(xs, r)), Tk.Toks.m(r), LPx.ptx.out_m(xs, r)) : {Tk.restore(_, Tk.Out.ys(Tk.scrub.fill(xs, r))) == S.raw(xs) : List<&2, Tk.Seg>}
  %Equal.sym(List<&2, Tk.Seg>, Tk.Out.ys(Tk.scrub.fill(xs, r)), Tk.fill(xs, Tk.Toks.ts(r)), LPx.ptx.out_ys(xs, r)) : {Tk.restore(Tk.Toks.m(r), _) == S.raw(xs) : List<&2, Tk.Seg>}
  Equal.trans(List<&2, Tk.Seg>, Tk.restore(Tk.Toks.m(r), Tk.fill(xs, Tk.Toks.ts(r))), S.mask(xs), S.raw(xs), LPx.ptx.round_trip(xs, m), LPx.ptx.mask_raw(xs, ok))
