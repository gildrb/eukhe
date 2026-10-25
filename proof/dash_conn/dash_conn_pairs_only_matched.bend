# eukhe: the proof of LAW dash_conn_pairs_only_matched
#
# PROOF: by cases on the socket and the event. Only a first frame of a
# waiting socket can pair (a later frame's pass runs or refuses:
# dcr.later_not_paired; the rest compute). It pairs only on a pairing
# (dpo.first) whose text is a token (dpo.shown: what it presents is the
# spec's, dash_token_spec), with a token stored (the spec's,
# dash_stored_spec) and Rust's match (dpo.check).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ../dash/dash_token_spec.bend as PDashTokenSpec
import ../dash/dash_stored_spec.bend as PDashStoredSpec
import ./base.bend as LA

def dpo.check(mm: Maybe<&2, List<&2, Nat>>, b: Bool, h: {DashConn.cv_is_paired(DashConn.cv_verdict(Da.first.pass(Da.check(mm, b)))) == True{} : Bool}) -> {Bool.and(b, Maybe.is_some(&2, List<&2, Nat>, mm)) == True{} : Bool}:
  match mm:
    case None{}:
      LA.dcn.absurdF({Bool.and(b, False{}) == True{} : Bool}, h)
    case Some{bs}:
      match b:
        case True{}:
          {==}
        case False{}:
          LA.dcn.absurdF({False{} == True{} : Bool}, h)

def dpo.shown(s: Da.Shown, +f: Da.Disk, +m: Bool, h: {DashConn.cv_is_paired(DashConn.cv_verdict(Da.first.pass(Da.gate.shown(s, f, m)))) == True{} : Bool}) -> {Bool.and(m, Bool.and(DashConn.cv_presents.shown(s), Maybe.is_some(&2, List<&2, Nat>, Da.stored(f)))) == True{} : Bool}:
  match s:
    case Da.Hex{bs}:
      dpo.check(Da.stored(f), m, h)
    case Da.Blank{}:
      LA.dcn.absurdF({Bool.and(m, False{}) == True{} : Bool}, h)
    case Da.Junk{}:
      LA.dcn.absurdF({Bool.and(m, False{}) == True{} : Bool}, h)

def dpo.first(x: Da.First, +f: Da.Disk, +m: Bool, h: {DashConn.cv_is_paired(DashConn.cv_verdict(Da.first.pass(Da.gate(x, f, m)))) == True{} : Bool}) -> {Bool.and(m, Bool.and(DashConn.cv_presents(x), DashConn.cv_holds(f))) == True{} : Bool}:
  match x:
    case Da.NoText{}:
      LA.dcn.absurdF({Bool.and(m, False{}) == True{} : Bool}, h)
    case Da.NotPairing{}:
      LA.dcn.absurdF({Bool.and(m, False{}) == True{} : Bool}, h)
    case Da.Pair{+t}:
      %Dash.dash_token_spec(t) : {Bool.and(m, Bool.and(DashConn.cv_presents.shown(_), Maybe.is_some(&2, List<&2, Nat>, Dash.sp_stored(f)))) == True{} : Bool}
      %Dash.dash_stored_spec(f) : {Bool.and(m, Bool.and(DashConn.cv_presents.shown(Da.shown(t)), Maybe.is_some(&2, List<&2, Nat>, _))) == True{} : Bool}
      dpo.shown(Da.shown(t), f, m, h)

def dpo.pairs(c: Da.Conn, e: Da.CEv, paired: {DashConn.cv_is_paired(DashConn.cv_verdict(Da.cstep(c, e))) == True{} : Bool}) -> {DashConn.cv_pair_ok(c, e) == True{} : Bool}:
  match c:
    case Da.Waiting{}:
      match e:
        case Da.CFirst{x, +f, +m}:
          dpo.first(x, f, m, paired)
        case Da.CFrame{f, m}:
          LA.dcn.absurdF({False{} == True{} : Bool}, paired)
    case Da.Paired{}:
      match e:
        case Da.CFirst{x, f, m}:
          LA.dcn.absurdF({False{} == True{} : Bool}, paired)
        case Da.CFrame{+f, +m}:
          LA.dcn.contra({False{} == True{} : Bool}, DashConn.cv_is_paired(DashConn.cv_verdict(Da.frame.pass(Da.frame(f, m)))), LA.dcr.later_not_paired(Da.frame(f, m)), paired)
    case Da.Closed{}:
      LA.dcn.absurdF({False{} == True{} : Bool}, paired)

def DashConn.dash_conn_pairs_only_matched(c, e, paired):
  dpo.pairs(c, e, paired)
