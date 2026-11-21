# eukhe: the proof of LAW fallback_entry_parses
#
# PROOF: by the failure: its Nats lead to the parse of the candidates and
# the tried models, whose count cuts them back apart (LA.fbb.split_app).

import Base
import ../../bend/fallback.bend as Fb
import ../../bend/ffi_fallback.bend as FFb
import ../../laws/fallback.bend as Fallback
import ./base.bend as LA

def fbp.lists(+w: Fb.Why, +cands: List<&2, Nat>, +tried: List<&2, Nat>) -> {FFb.parse.lists(w, List.length(&2, Nat, cands) <> List.append(&2, Nat, cands, tried)) == Some{Fb.In{w, cands, tried}} : Maybe<&2, Fb.In>}:
  %Equal.sym(Maybe<&2, FFb.Parts>, FFb.split(List.length(&2, Nat, cands), List.append(&2, Nat, cands, tried)), Some{FFb.Parts{cands, tried}}, LA.fbb.split_app(cands, tried)) : {FFb.parse.cut(w, _) == Some{Fb.In{w, cands, tried}} : Maybe<&2, Fb.In>}
  {==}

def Fallback.fallback_entry_parses(x):
  match x:
    case Fb.In{k, +cands, +tried}:
      match k:
        case Fb.Failed{+n, +retries}:
          fbp.lists(Fb.Failed{n, retries}, cands, tried)
        case Fb.Login{}:
          fbp.lists(Fb.Login{}, cands, tried)
        case Fb.Quota{+until}:
          fbp.lists(Fb.Quota{until}, cands, tried)
        case Fb.Unset{}:
          fbp.lists(Fb.Unset{}, cands, tried)
