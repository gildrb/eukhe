# eukhe: the proof of LAW privacy_ipv6_mapped_reserved
#
# PROOF: for each reserved first octet (00, 7f, ff) and either prefix,
# the spec's test reads the value as one that reaches no one (pmr.sp*:
# computation), so the spec takes no such address (pmr.take) and the IPv6
# reader, deciding as the spec (pdc.decides), takes none; the value starts
# with nine zero digits, so the address is no IPv4 alone (pmr.isq), and
# the IPv4 grammar reads no quad from its text (pnn.text6).

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../spec/harness/privacy.bend as S
import ./base/chars.bend as LIp
import ./base/decide.bend as LDc
import ./base/none.bend as LNn
import ./base/value.bend as LVl
import ../../laws/privacy/ip.bend as PrivacyIp

def pmr.sp00(m: Bool, -rest: String) -> {S.special6(String.append(S.prefix96(m), String.append("00", rest))) == True{} : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def pmr.sp7f(m: Bool, -rest: String) -> {S.special6(String.append(S.prefix96(m), String.append("7f", rest))) == True{} : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def pmr.spff(m: Bool, -rest: String) -> {S.special6(String.append(S.prefix96(m), String.append("ff", rest))) == True{} : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# a value that reaches no one: the spec takes no address
def pmr.take(+a: Ip.Addr, +v: String, +before: String, +t: String, +e: {S.value6(a) == v : String}, +hs: {S.special6(v) == True{} : Bool}) -> {S.take6(a, before, t) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(String, S.value6(a), v, e) : {S.ans(Bool.and(Bool.and(Bool.and(Bool.and(S.counted(a), S.digit(a)), Bool.not(S.special6(_))), S.free(S.last(before))), S.free(S.first(t))), String.length(S.text6(a, ""))) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, S.special6(v), True{}, hs) : {S.ans(Bool.and(Bool.and(Bool.and(Bool.and(S.counted(a), S.digit(a)), Bool.not(_)), S.free(S.last(before))), S.free(S.first(t))), String.length(S.text6(a, ""))) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Bool.and(Bool.and(S.counted(a), S.digit(a)), False{}), False{}, LIp.pip.and_false(Bool.and(S.counted(a), S.digit(a)))) : {S.ans(Bool.and(Bool.and(_, S.free(S.last(before))), S.free(S.first(t))), String.length(S.text6(a, ""))) == None{} : Maybe<&2, Nat>}
  {==}

# a value that starts with either prefix is no IPv4's: no IPv4 alone
def pmr.isq(a: Ip.Addr, m: Bool, -w: String, e: {S.value6(a) == String.append(S.prefix96(m), w) : String}) -> {LNn.pnn.isq(a) == False{} : Bool}:
  match m:
    case True{}:
      LVl.pvl.isq(a, String.append("00000000000ffff", w), e)
    case False{}:
      LVl.pvl.isq(a, String.append("000000000000000", w), e)

# a value that reaches no one, after either prefix: no address of any kind
def pmr.ip(+a: Ip.Addr, +m: Bool, +w: String, +before: String, +t: String, +sh: {S.shaped(a) == True{} : Bool}, +st: {S.stops6(t) == True{} : Bool}, +hs: {S.special6(String.append(S.prefix96(m), w)) == True{} : Bool}, +e: {S.value6(a) == String.append(S.prefix96(m), w) : String}) -> {Ip.ip(before, S.text6(a, t)) == None{} : Maybe<&2, Nat>}:
  +X = S.text6(a, t)
  %Equal.sym(Maybe<&2, Nat>, Ip.v6(before, X), None{}, Equal.trans(Maybe<&2, Nat>, Ip.v6(before, X), S.take6(a, before, t), None{}, LDc.pdc.decides(a, before, t, sh, st), pmr.take(a, String.append(S.prefix96(m), w), before, t, e, hs))) : {Maybe.or(&2, Nat, _, Ip.v4(before, X)) == None{} : Maybe<&2, Nat>}
  LNn.pnn.v4_at(before, X, LNn.pnn.text6(a, t, sh, st, pmr.isq(a, m, w, e)))

def PrivacyIp.privacy_ipv6_mapped_reserved(a, mapped, rest, before, t, sh, st):
  (e => pmr.ip(a, mapped, String.append("00", rest), before, t, sh, st, pmr.sp00(mapped, rest), e), (e => pmr.ip(a, mapped, String.append("7f", rest), before, t, sh, st, pmr.sp7f(mapped, rest), e), e => pmr.ip(a, mapped, String.append("ff", rest), before, t, sh, st, pmr.spff(mapped, rest), e)))
