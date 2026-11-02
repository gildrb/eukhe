# eukhe: the proof of LAW privacy_ipv6_loopback_any_form
#
# PROOF: the IPv6 reader decides as the spec (pdc.decides), and the spec
# takes no address whose value is 31 zero digits then any (plb.take: that
# value is an IPv4 compatible whose first octet is 0); that value is no
# IPv4's eight digits, so the address is no IPv4 alone (pvl.isq), and the
# IPv4 grammar reads no quad from its text (pnn.text6).

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../spec/harness/privacy.bend as S
import ./base/chars.bend as LIp
import ./base/decide.bend as LDc
import ./base/none.bend as LNn
import ./base/value.bend as LVl
import ../../laws/privacy/ip.bend as PrivacyIp

# the value: the spec takes no address
def plb.take(+a: Ip.Addr, -d: Char, +before: String, +t: String, +lo: {S.value6(a) == String.append("0000000000000000000000000000000", SCon{d, SNil{}}) : String}) -> {S.take6(a, before, t) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(String, S.value6(a), String.append("0000000000000000000000000000000", SCon{d, SNil{}}), lo) : {S.ans(Bool.and(Bool.and(Bool.and(Bool.and(S.counted(a), S.digit(a)), Bool.not(S.special6(_))), S.free(S.last(before))), S.free(S.first(t))), String.length(S.text6(a, ""))) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Bool.and(Bool.and(S.counted(a), S.digit(a)), False{}), False{}, LIp.pip.and_false(Bool.and(S.counted(a), S.digit(a)))) : {S.ans(Bool.and(Bool.and(_, S.free(S.last(before))), S.free(S.first(t))), String.length(S.text6(a, ""))) == None{} : Maybe<&2, Nat>}
  {==}

def PrivacyIp.privacy_ipv6_loopback_any_form(a, d, before, t, sh, st, lo):
  +X = S.text6(a, t)
  %Equal.sym(Maybe<&2, Nat>, Ip.v6(before, X), None{}, Equal.trans(Maybe<&2, Nat>, Ip.v6(before, X), S.take6(a, before, t), None{}, LDc.pdc.decides(a, before, t, sh, st), plb.take(a, d, before, t, lo))) : {Maybe.or(&2, Nat, _, Ip.v4(before, X)) == None{} : Maybe<&2, Nat>}
  LNn.pnn.v4_at(before, X, LNn.pnn.text6(a, t, sh, st, LVl.pvl.isq(a, String.append("0000000000000000000000", SCon{d, SNil{}}), lo)))
