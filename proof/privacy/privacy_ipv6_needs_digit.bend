# eukhe: the proof of LAW privacy_ipv6_needs_digit
#
# PROOF: the IPv6 reader decides as the spec (pdc.decides), and the spec
# takes no address with no decimal digit (pnd.take); an address with no
# digit has no IPv4, so its text starts with a hex letter or `:`, from
# which the IPv4 grammar reads no quad (pnn.text6).

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../spec/harness/privacy.bend as S
import ./base/chars.bend as LIp
import ./base/decide.bend as LDc
import ./base/none.bend as LNn
import ../../laws/privacy/ip.bend as PrivacyIp

# no digit: the spec takes no address
def pnd.take(+a: Ip.Addr, +before: String, +t: String, +nd: {S.digit(a) == False{} : Bool}) -> {S.take6(a, before, t) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, S.digit(a), False{}, nd) : {S.ans(Bool.and(Bool.and(Bool.and(S.counted(a), _), S.free(S.last(before))), S.free(S.first(t))), String.length(S.text6(a, ""))) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Bool.and(S.counted(a), False{}), False{}, LIp.pip.and_false(S.counted(a))) : {S.ans(Bool.and(Bool.and(_, S.free(S.last(before))), S.free(S.first(t))), String.length(S.text6(a, ""))) == None{} : Maybe<&2, Nat>}
  {==}

# no digit: no IPv4 alone
def pnd.isq(a: Ip.Addr, nd: {S.digit(a) == False{} : Bool}) -> {LNn.pnn.isq(a) == False{} : Bool}:
  match a:
    case Ip.Full{gs, q}:
      match gs:
        case Nil{}:
          match q:
            case None{}:
              {==}
            case Some{x}:
              LIp.pip.absurd_ft({LNn.pnn.isq(Ip.Full{Nil{}, Some{x}}) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, nd))
        case g <> rest:
          {==}
    case Ip.Gap{l, r, q}:
      {==}

def PrivacyIp.privacy_ipv6_needs_digit(a, before, t, sh, st, nd):
  +X = S.text6(a, t)
  %Equal.sym(Maybe<&2, Nat>, Ip.v6(before, X), None{}, Equal.trans(Maybe<&2, Nat>, Ip.v6(before, X), S.take6(a, before, t), None{}, LDc.pdc.decides(a, before, t, sh, st), pnd.take(a, before, t, nd))) : {Maybe.or(&2, Nat, _, Ip.v4(before, X)) == None{} : Maybe<&2, Nat>}
  LNn.pnn.v4_at(before, X, LNn.pnn.text6(a, t, sh, st, pnd.isq(a, nd)))
