# eukhe: the proof of LAW privacy_session_numbers_from_one
#
# PROOF: the session's map is the spec's map of its history as one text
# (psn.sess), with no value held twice (pmp.dk), so the code scrubs the
# next text as the spec (pst.scrub); induction on the text: each value of
# a class that maps back takes its place in its class, which is its number
# in the history so far (psn.head over psn.tk), and the map after it is the
# map of the history with it (psn.bsnoc): psn.num
# (proof/privacy/base/session.bend).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy_map.bend as Sm
import ./base/map.bend as LMp
import ./base/session.bend as LSs
import ./base/stext.bend as LSt
import ../../laws/privacy/session.bend as PrivacySession

def PrivacySession.privacy_session_numbers_from_one(xss, xs):
  %Equal.sym(Tk.Book, PrivacySession.session(xss), LSs.psn.B(PrivacySession.history(xss)), LSs.psn.sess(xss)) : {Tk.Out.ys(Tk.scrub(_, xs)) == PrivacySession.numbered(List.append(&2, Tk.Piece, PrivacySession.history(xss), xs), xs) : List<&2, Tk.Seg>}
  %Equal.sym(Tk.Out, Tk.scrub(LSs.psn.B(PrivacySession.history(xss)), xs), Sm.scrub_text(xs, LSs.psn.B(PrivacySession.history(xss))), LSt.pst.scrub(LSs.psn.B(PrivacySession.history(xss)), xs, LMp.pmp.dk(Sm.vals(PrivacySession.history(xss)), Tk.Book.empty(), {==}))) : {Tk.Out.ys(_) == PrivacySession.numbered(List.append(&2, Tk.Piece, PrivacySession.history(xss), xs), xs) : List<&2, Tk.Seg>}
  %LSs.psn.out_ys(xs, Sm.scrub_vals(Sm.vals(xs), LSs.psn.B(PrivacySession.history(xss)))) : {_ == PrivacySession.numbered(List.append(&2, Tk.Piece, PrivacySession.history(xss), xs), xs) : List<&2, Tk.Seg>}
  LSs.psn.num(xs, PrivacySession.history(xss))
