# eukhe: the proof of LAW redirect_input_verify_only_same
#
# PROOF: a check that passes compared equal states (ad.str_sound) and
# answered the paste's code and state; a mismatch is no paste.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ../auth_flight/base/logic.bend as LAd

def vo.code(a: Ri.Answer) -> String:
  match a:
    case Ri.Pasted{c, m}:
      c
    case Ri.Failed{f}:
      SNil{}

def vo.state(a: Ri.Answer) -> Maybe<&2, String>:
  match a:
    case Ri.Pasted{c, m}:
      m
    case Ri.Failed{f}:
      None{}

def vo.FP(a: Ri.Answer, G: Type) -> Type:
  match a:
    case Ri.Pasted{c, m}:
      G
    case Ri.Failed{f}:
      Unit

def vo.failed_pasted(-G: Type, -f: Ri.Fail, -c: String, -m: Maybe<&2, String>, e: {Ri.Failed{f} == Ri.Pasted{c, m} : Ri.Answer}) -> G:
  %e : vo.FP(_, G)
  Unit{}

def vo.of(b: Bool, +c: String, +s: String, +e: String, +c2: String, +m: Maybe<&2, String>, eb: {String.eq(s, e) == b : Bool}, ok: {Ri.verify.at(b, c, s) == Ri.Pasted{c2, m} : Ri.Answer}) -> {(s, (c2, m)) == (e, (c, Some{s})) : String & (String & Maybe<&2, String>)}:
  match b:
    case True{}:
      +k = ok
      %LAd.ad.str_sound(s, e, eb) : {(s, (c2, m)) == (_, (c, Some{s})) : String & (String & Maybe<&2, String>)}
      %Equal.cong(Ri.Answer, String, vo.code, Ri.Pasted{c, Some{s}}, Ri.Pasted{c2, m}, k) : {(s, (_, m)) == (s, (c, Some{s})) : String & (String & Maybe<&2, String>)}
      %Equal.cong(Ri.Answer, Maybe<&2, String>, vo.state, Ri.Pasted{c, Some{s}}, Ri.Pasted{c2, m}, k) : {(s, (c, _)) == (s, (c, Some{s})) : String & (String & Maybe<&2, String>)}
      {==}
    case False{}:
      vo.failed_pasted({(s, (c2, m)) == (e, (c, Some{s})) : String & (String & Maybe<&2, String>)}, Ri.FMismatch{}, c2, m, ok)

def RedirectInput.redirect_input_verify_only_same(c, s, e, c2, m, ok):
  vo.of(String.eq(s, e), c, s, e, c2, m, {==}, ok)
