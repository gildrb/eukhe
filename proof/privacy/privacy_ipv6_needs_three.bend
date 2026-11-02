# eukhe: the proof of LAW privacy_ipv6_needs_three
#
# PROOF: the IPv6 reader decides as the spec (pdc.decides), and the spec
# takes no address that is not counted (pn3.take); the text of a `::`
# address starts with `::` or with a hex group then `:`, from which the
# IPv4 grammar reads no quad (pnn.text6).

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../spec/harness/privacy.bend as S
import ./base/decide.bend as LDc
import ./base/none.bend as LNn
import ../../laws/privacy/ip.bend as PrivacyIp

# not counted: the spec takes no address
def pn3.take(+a: Ip.Addr, +before: String, +t: String, +few: {S.counted(a) == False{} : Bool}) -> {S.take6(a, before, t) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, S.counted(a), False{}, few) : {S.ans(Bool.and(Bool.and(Bool.and(Bool.and(_, S.digit(a)), Bool.not(S.special6(S.value6(a)))), S.free(S.last(before))), S.free(S.first(t))), String.length(S.text6(a, ""))) == None{} : Maybe<&2, Nat>}
  {==}

def PrivacyIp.privacy_ipv6_needs_three(l, r, q, before, t, sh, st, few):
  +a = {Ip.Gap{l, r, q} : Ip.Addr}
  +X = S.text6(a, t)
  %Equal.sym(Maybe<&2, Nat>, Ip.v6(before, X), None{}, Equal.trans(Maybe<&2, Nat>, Ip.v6(before, X), S.take6(a, before, t), None{}, LDc.pdc.decides(a, before, t, sh, st), pn3.take(a, before, t, few))) : {Maybe.or(&2, Nat, _, Ip.v4(before, X)) == None{} : Maybe<&2, Nat>}
  LNn.pnn.v4_at(before, X, LNn.pnn.text6(a, t, sh, st, {==}))
