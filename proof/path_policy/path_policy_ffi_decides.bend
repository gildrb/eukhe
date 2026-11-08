# eukhe: the proof of LAW path_policy_ffi_decides
#
# PROOF of LAW path_policy_ffi_decides: the spec's spelling of a request
# is the entry's encoding (pe.put: the flat lists and rules are the
# spec's, wire_nats_spells), and its fits are the entry's (pe.fits); the
# entry answers the model's judgment of it (path_policy_ffi_answers),
# which is the spec's class and secret test (pe.reply: path_class_spec,
# path_holds_spec).

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/path_policy.bend as Pp
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/path_policy/policy.bend as PathPolicy
import ../../laws/path_policy/spec.bend as PathPolicySpec
import ./path_policy_ffi_answers.bend as PPathPolicyFfiAnswers
import ./base/entry.bend as LAPathPolicyEntry

def PathPolicySpec.path_policy_ffi_decides(q, fit):
  match q:
    case FPp.Req{p, r}:
      match p r:
        case Pp.Pol{+ro, +ru, +se} Pp.Res{+at, +l}:
          +hfit = Equal.trans(Bool, LAPathPolicyEntry.pe.F(Fl.flat(ro), Fl.flat(FPp.rules(ru)), Fl.flat(se), at), PathPolicySpec.pp_req_fits(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}), True{}, LAPathPolicyEntry.pe.fits(ro, ru, se, at), fit)
          %LAPathPolicyEntry.pe.put(ro, ru, se, at, l, "") : {FPp.ffi(_) == PathPolicySpec.pp_spell_reply(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) : String}
          %Equal.sym(String, FPp.ffi(FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, "")), FPp.put_judged(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), ""), PathPolicy.path_policy_ffi_answers(ro, ru, se, at, l, hfit)) : {_ == PathPolicySpec.pp_spell_reply(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) : String}
          LAPathPolicyEntry.pe.reply(ro, ru, se, at, l)
