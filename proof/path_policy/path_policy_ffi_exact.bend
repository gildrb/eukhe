# eukhe: the proof of LAW path_policy_ffi_exact
#
# PROOF of LAW path_policy_ffi_exact: the decoder reads only spelled
# requests that fit, the rest after them untouched (pe.dec); an answer
# that is not the error form read a request with nothing after it.

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/path_policy.bend as PathPolicy
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LAPathPolicyEntry

def pex.goal(s: String) -> Type:
  Sigma<&1, &1, FPp.Req, q => {s == PathPolicy.pp_spell_req(q, "") : String} & {PathPolicy.pp_req_fits(q) == True{} : Bool}>

def pex.top(-s: String, d: Wr.Dec<FPp.Req>, rp: LAPathPolicyEntry.pe.RP(s, d), ok: {LawsBase.wire_opens_err(FPp.answer(d)) == False{} : Bool}) -> pex.goal(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LAWireSpell.ws_absurd(pex.goal(s), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(pex.goal(s), ok)

def PathPolicy.path_policy_ffi_exact(s, ok):
  pex.top(s, FPp.get_req(s), LAPathPolicyEntry.pe.dec(s), ok)
