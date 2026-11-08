# eukhe: the proof of LAW path_policy_ffi_answers_spelled
#
# PROOF: the spelled request is the entry's own writing of it
# (LA.pp.req_spell), which the entry answers with its reply to the model's
# judgment (path_policy_ffi_answers, its fit premise from the spec's by
# LA.pp.fits_code), the spec's spelled answer (LA.pp.reply_spec).

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy.bend as PathPolicy
import ./base.bend as LA
import ./path_policy_ffi_answers.bend as PPathPolicyFfiAnswers

def pp.answers_spelled(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool, fits: {PathPolicy.pp_req_fits(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) == True{} : Bool}) -> {FPp.ffi(PathPolicy.pp_spell_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, "")) == PathPolicy.pp_spell_answer(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) : String}:
  %LA.pp.req_spell(ro, ru, se, at, l, "") : {FPp.ffi(_) == PathPolicy.pp_spell_answer(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) : String}
  Equal.trans(String, FPp.ffi(FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, "")), FPp.put_judged(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), ""), PathPolicy.pp_spell_answer(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}), PathPolicy.path_policy_ffi_answers(ro, ru, se, at, l, LA.pp.fits_code(ro, ru, se, at, l, fits)), LA.pp.reply_spec(ro, ru, se, at, l))

def PathPolicy.path_policy_ffi_answers_spelled(q, fits):
  match q:
    case FPp.Req{p, r}:
      match p r:
        case Pp.Pol{+ro, +ru, +se} Pp.Res{+at, +l}:
          pp.answers_spelled(ro, ru, se, at, l, fits)
