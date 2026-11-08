# eukhe: the proof of LAW privacy_round_trip_exact
#
# PROOF: the scrub is one step for the text's values (ptx.out_m, ptx.out_ys);
# restored piece by piece, each value's token restores to it in the map
# after the step (psc.tok_ok), and later values move no index (ptx.keep):
# ptx.round_trip.

import Base
import ../../bend/privacy/token.bend as Tk
import ./base/text.bend as LPx
import ../../spec/harness/privacy.bend as S
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_round_trip_exact(m, xs):
  +r = Tk.scrub_vals(Tk.vals(xs), m)
  %Equal.sym(Tk.Book, Tk.Out.m(Tk.scrub.fill(xs, r)), Tk.Toks.m(r), LPx.ptx.out_m(xs, r)) : {Tk.restore(_, Tk.Out.ys(Tk.scrub.fill(xs, r))) == S.mask(xs) : List<&2, Tk.Seg>}
  %Equal.sym(List<&2, Tk.Seg>, Tk.Out.ys(Tk.scrub.fill(xs, r)), Tk.fill(xs, Tk.Toks.ts(r)), LPx.ptx.out_ys(xs, r)) : {Tk.restore(Tk.Toks.m(r), _) == S.mask(xs) : List<&2, Tk.Seg>}
  LPx.ptx.round_trip(xs, m)
