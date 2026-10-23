# eukhe: lemmas the proofs of area admission share: admission/step

import Base
import ../../../../bend/admission.bend as Ad
import ./calm.bend as LAAdmissionCalm
import ./collect.bend as LAAdmissionCollect
import ./le.bend as LAAdmissionLe
import ./pick.bend as LAAdmissionPick
import ./release.bend as LAAdmissionRelease
import ./room.bend as LAAdmissionRoom
import ../logic.bend as LALogic

def ad.step_ok(s: Ad.St, o: Ad.Op, +h: {LALogic.ad.okS(s) == True{} : Bool}) -> {LALogic.ad.okS(Ad.step(s, o)) == True{} : Bool}:
  match s:
    case Ad.St{+l, +q, +ts}:
      match o:
        case Ad.Admit{Ad.Ia{}}:
          LAAdmissionRoom.ad.adm_ia_ok(l, q, ts, h)
        case Ad.Admit{Ad.Bg{}}:
          LAAdmissionPick.ad.adm_bg_ok(l, ts, h)
        case Ad.Collect{+k}:
          LAAdmissionCollect.ad.col_ok(Ad.get(ts, k), l, q, ts, k, {==}, h)
        case Ad.Release{+k}:
          LAAdmissionRelease.ad.rel_ok(Ad.get(ts, k), l, q, ts, k, {==}, h)
        case Ad.Leave{+k}:
          LAAdmissionPick.ad.lea_ok(Ad.get(ts, k), l, q, ts, k, {==}, h)
        case Ad.Limit{+l2, q2}:
          LAAdmissionPick.ad.grant_ok(Ad.waits(ts), Ad.pick(l2, ts), l2, ts, {==}, LAAdmissionLe.ad.le_refl(Ad.waits(ts)), LAAdmissionCalm.ad.calm_of(l, ts, h))

def ad.run_ok(os: List<&2, Ad.Op>, +s: Ad.St, h: {LALogic.ad.okS(s) == True{} : Bool}) -> {LALogic.ad.okS(Ad.run(os, s)) == True{} : Bool}:
  match os:
    case Nil{}:
      h
    case +o <> r:
      ad.run_ok(r, Ad.step(s, o), ad.step_ok(s, o, h))
