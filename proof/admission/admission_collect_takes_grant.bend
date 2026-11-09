# eukhe: the proof of LAW admission_collect_takes_grant
#
# PROOF: the model reads ticket k as the ticket after pre (pat.got) and
# collects it in place (pat.put).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/at.bend as PAt

def Admission.admission_collect_takes_grant(l, q, pre, c, post):
  +ts = List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Granted{}} <> post)
  +k = List.length(&2, Ad.Tk, pre)
  %PAt.pat.got(pre, Ad.Tk{c, Ad.Granted{}}, post) : {Ad.collect.at(_, l, q, ts, k) == Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Held{}} <> post)} : Ad.St}
  %PAt.pat.put(pre, c, Ad.Granted{}, post, Ad.Held{}) : {Ad.St{l, q, Ad.put(ts, k, Ad.Held{})} == Ad.St{l, q, _} : Ad.St}
  {==}
