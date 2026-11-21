# eukhe: the proof of LAW fallback_entry_parses
#
# PROOF: by the failure: its Nats lead to the parse of the candidates, the
# signed-in defaults and the tried models, whose counts cut them back
# apart (LA.fbb.split_app, once per count).

import Base
import ../../bend/fallback.bend as Fb
import ../../bend/ffi_fallback.bend as FFb
import ../../laws/fallback.bend as Fallback
import ./base.bend as LA

def fbp.lists(+w: Fb.Why, +cands: List<&2, Nat>, +defaults: List<&2, Nat>, +tried: List<&2, Nat>) -> {FFb.parse.lists(w, List.length(&2, Nat, cands) <> List.append(&2, Nat, cands, List.length(&2, Nat, defaults) <> List.append(&2, Nat, defaults, tried))) == Some{Fb.In{w, cands, defaults, tried}} : Maybe<&2, Fb.In>}:
  %Equal.sym(Maybe<&2, FFb.Parts>, FFb.split(List.length(&2, Nat, cands), List.append(&2, Nat, cands, List.length(&2, Nat, defaults) <> List.append(&2, Nat, defaults, tried))), Some{FFb.Parts{cands, List.length(&2, Nat, defaults) <> List.append(&2, Nat, defaults, tried)}}, LA.fbb.split_app(cands, List.length(&2, Nat, defaults) <> List.append(&2, Nat, defaults, tried))) : {FFb.parse.cut(w, _) == Some{Fb.In{w, cands, defaults, tried}} : Maybe<&2, Fb.In>}
  %Equal.sym(Maybe<&2, FFb.Parts>, FFb.split(List.length(&2, Nat, defaults), List.append(&2, Nat, defaults, tried)), Some{FFb.Parts{defaults, tried}}, LA.fbb.split_app(defaults, tried)) : {FFb.parse.cut_defaults(w, cands, _) == Some{Fb.In{w, cands, defaults, tried}} : Maybe<&2, Fb.In>}
  {==}

def Fallback.fallback_entry_parses(x):
  match x:
    case Fb.In{k, +cands, +defaults, +tried}:
      match k:
        case Fb.Failed{+n, +retries}:
          fbp.lists(Fb.Failed{n, retries}, cands, defaults, tried)
        case Fb.Login{}:
          fbp.lists(Fb.Login{}, cands, defaults, tried)
        case Fb.Quota{+until}:
          fbp.lists(Fb.Quota{until}, cands, defaults, tried)
        case Fb.Unset{}:
          fbp.lists(Fb.Unset{}, cands, defaults, tried)
