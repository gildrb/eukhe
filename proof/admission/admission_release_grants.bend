# eukhe: the proof of LAW admission_release_grants
#
# PROOF: the model reads ticket k as the ticket after pre (pat.got), ends
# it in place (pat.put) and grants with its loop, which is the two passes
# (pag.grant).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/at.bend as PAt
import ./base/admission/grant.bend as PG

def Admission.admission_release_grants(l, q, pre, c, post):
  +ts = List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Held{}} <> post)
  +k = List.length(&2, Ad.Tk, pre)
  %PAt.pat.got(pre, Ad.Tk{c, Ad.Held{}}, post) : {Ad.release.at(_, l, q, ts, k) == Ad.St{l, q, Admission.ads_grant(l, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post))} : Ad.St}
  %PAt.pat.put(pre, c, Ad.Held{}, post, Ad.Ended{}) : {Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))} == Ad.St{l, q, Admission.ads_grant(l, _)} : Ad.St}
  %PG.pag.grant(l, Ad.put(ts, k, Ad.Ended{})) : {Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))} == Ad.St{l, q, _} : Ad.St}
  {==}
