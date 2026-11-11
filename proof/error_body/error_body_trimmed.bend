# eukhe: the proof of LAW error_body_trimmed
#
# PROOF: the code's start trim drops the white space p (LA.ebr.start) and
# stops at t's first char, no white space (LA.ebr.start_keep); its end
# trim drops q (LA.ebr.end_ws) and keeps t, whose last char is no white
# space (LA.ebr.end_keep); per char the code's white space is ECMA-262's
# (LA.ebc.ws). t is not empty, so the body is t cut to the cap.

import Base
import ../../bend/error_body.bend as Eb
import ../../laws/error_body.bend as ErrorBody
import ../base/staging.bend as LStg
import ./base.bend as LA

def ebtr.go(t: String, +p: String, +q: String, hp: {ErrorBody.sp_all_ws(p) == True{} : Bool}, +hq: {ErrorBody.sp_all_ws(q) == True{} : Bool}, +ht: {ErrorBody.sp_solid(t) == True{} : Bool}) -> {Eb.body(Eb.PText{String.append(p, String.append(t, q))}, Eb.PNone{}, Eb.PNone{}) == Some{Eb.truncate(t, 4000n)} : Maybe<&2, String>}:
  match t:
    case SNil{}:
      LStg.stg.absurdF({Eb.body(Eb.PText{String.append(p, String.append(SNil{}, q))}, Eb.PNone{}, Eb.PNone{}) == Some{Eb.truncate(SNil{}, 4000n)} : Maybe<&2, String>}, ht)
    case SCon{+c, +u}:
      +hn = LA.ebl.and_l(Bool.not(ErrorBody.sp_ws(c)), Bool.not(ErrorBody.sp_ends_ws(u, c)), ht)
      +he = LA.ebl.and_r(Bool.not(ErrorBody.sp_ws(c)), Bool.not(ErrorBody.sp_ends_ws(u, c)), ht)
      %Equal.sym(String, Eb.trim_start(String.append(p, String.append(SCon{c, u}, q))), Eb.trim_start(String.append(SCon{c, u}, q)), LA.ebr.start(p, String.append(SCon{c, u}, q), hp)) : {Eb.body.of(Eb.trim_end(_)) == Some{Eb.truncate(SCon{c, u}, 4000n)} : Maybe<&2, String>}
      %Equal.sym(String, Eb.trim_start(SCon{c, String.append(u, q)}), SCon{c, String.append(u, q)}, LA.ebr.start_keep(c, String.append(u, q), LA.ebl.not_t(ErrorBody.sp_ws(c), hn))) : {Eb.body.of(Eb.trim_end(_)) == Some{Eb.truncate(SCon{c, u}, 4000n)} : Maybe<&2, String>}
      %Equal.sym(String, Eb.trim_end(String.append(SCon{c, u}, q)), SCon{c, u}, LA.ebr.end_keep(u, c, q, LA.ebl.not_t(ErrorBody.sp_ends_ws(u, c), he), hq)) : {Eb.body.of(_) == Some{Eb.truncate(SCon{c, u}, 4000n)} : Maybe<&2, String>}
      {==}

def ErrorBody.error_body_trimmed(p, t, q, hp, hq, ht):
  ebtr.go(t, p, q, hp, hq, ht)
