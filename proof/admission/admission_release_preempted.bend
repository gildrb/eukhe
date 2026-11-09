# eukhe: the proof of LAW admission_release_preempted
#
# PROOF: the model reads ticket k as the ticket after pre (pat.got) and
# ends it in place (pat.put), with no grant.

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/at.bend as PAt

def Admission.admission_release_preempted(l, q, pre, c, post):
  +ts = List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Preempted{}} <> post)
  +k = List.length(&2, Ad.Tk, pre)
  %PAt.pat.got(pre, Ad.Tk{c, Ad.Preempted{}}, post) : {Ad.release.at(_, l, q, ts, k) == Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post)} : Ad.St}
  %PAt.pat.put(pre, c, Ad.Preempted{}, post, Ad.Ended{}) : {Ad.St{l, q, Ad.put(ts, k, Ad.Ended{})} == Ad.St{l, q, _} : Ad.St}
  {==}
