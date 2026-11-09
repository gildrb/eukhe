# eukhe: the proof of LAW privacy_session_restores_own
#
# PROOF: the session's map is the spec's map of its history as one text
# (psn.sess), the code restores as the spec piece by piece (pst.restore),
# and a token the map restores is of a class that maps back with a value
# that has a place in its class, which the history then holds (psn.r1,
# psn.has_of over psn.tk): psn.came (proof/privacy/base/session.bend).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy_map.bend as Sm
import ./base/session.bend as LSs
import ./base/stext.bend as LSt
import ../../laws/privacy/session.bend as PrivacySession

def PrivacySession.privacy_session_restores_own(xss, ys):
  %Equal.sym(Tk.Book, PrivacySession.session(xss), LSs.psn.B(PrivacySession.history(xss)), LSs.psn.sess(xss)) : {PrivacySession.all_came(PrivacySession.history(xss), ys, Tk.restore(_, ys)) == True{} : Bool}
  %Equal.sym(List<&2, Tk.Seg>, Tk.restore(LSs.psn.B(PrivacySession.history(xss)), ys), Sm.restore_text(ys, LSs.psn.B(PrivacySession.history(xss))), LSt.pst.restore(LSs.psn.B(PrivacySession.history(xss)), ys)) : {PrivacySession.all_came(PrivacySession.history(xss), ys, _) == True{} : Bool}
  LSs.psn.came(PrivacySession.history(xss), ys)
