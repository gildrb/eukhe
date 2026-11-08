# eukhe: the proof of LAW privacy_tokens_kept
#
# PROOF: a new value goes in front with the next index of its class, past
# every index the map holds (ptk.value_le, ptk.value_new): ptx.keep.

import Base
import ../../bend/privacy/token.bend as Tk
import ./base/text.bend as LPx
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_tokens_kept(m, xs, c, i, v, h):
  +r = Tk.scrub_vals(Tk.vals(xs), m)
  %Equal.sym(Tk.Book, Tk.Out.m(Tk.scrub.fill(xs, r)), Tk.Toks.m(r), LPx.ptx.out_m(xs, r)) : {Tk.restore_tok(_, c, i) == Some{v} : Maybe<&2, String>}
  LPx.ptx.keep(Tk.vals(xs), m, c, i, v, h)
