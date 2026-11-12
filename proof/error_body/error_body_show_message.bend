# eukhe: the proof of LAW error_body_show_message
#
# PROOF: every flag, status, body and prefix the premise allows: the
# message alone computes; with a prefix and a status, the code's
# `<q> (<s>): <m>` is the lead then m by appending's associativity
# (LA.ebs.lead); the shown body is refused by the premise.

import Base
import ../../bend/error_body.bend as Eb
import ../../laws/error_body.bend as ErrorBody
import ../base/staging.bend as LStg
import ./base.bend as LA

def ebsm.lead(p: Maybe<&2, String>, st: Maybe<&2, String>, +m: String) -> {Eb.show.plain(p, st, m) == String.append(ErrorBody.sp_lead(p, st), m) : String}:
  match p st:
    case Some{q} Some{s}:
      LA.ebs.lead(q, s, m)
    case Some{q} None{}:
      {==}
    case None{} None{}:
      {==}
    case None{} Some{s}:
      {==}

def ebsm.go(c: Bool, st: Maybe<&2, String>, b: Maybe<&2, String>, p: Maybe<&2, String>, +m: String, h: {ErrorBody.sp_shows_body(c, st, b) == False{} : Bool}) -> {Eb.show(c, st, b, p, m) == String.append(ErrorBody.sp_lead(p, st), m) : String}:
  match c st b:
    case False{} Some{s} Some{x}:
      LStg.stg.absurd({Eb.show(False{}, Some{s}, Some{x}, p, m) == String.append(ErrorBody.sp_lead(p, Some{s}), m) : String}, h)
    case False{} Some{s} None{}:
      ebsm.lead(p, Some{s}, m)
    case False{} None{} y:
      ebsm.lead(p, None{}, m)
    case True{} y z:
      ebsm.lead(p, y, m)

def ErrorBody.error_body_show_message(c, st, b, p, m, h):
  ebsm.go(c, st, b, p, m, h)
