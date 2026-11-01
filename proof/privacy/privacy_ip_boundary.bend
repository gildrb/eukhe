# eukhe: the proof of LAW privacy_ip_boundary
#
# PROOF: the last char of the text before is c (pip.last2_snoc); a word
# char is free of neither edge (pip.word_not_free, pip.word_not_edge4), so
# neither grammar reads on.

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../bend/privacy/context.bend as Cx
import ../../spec/harness/privacy.bend as S
import ./base/chars.bend as LIp
import ../../laws/privacy/ip.bend as PrivacyIp

def PrivacyIp.privacy_ip_boundary(p, c, rest, w):
  +kf = LIp.pip.word_not_free(S.kind(c), w)
  +ke = LIp.pip.word_not_edge4(S.kind(c), w)
  %Equal.sym(Maybe<&2, Char> & Maybe<&2, Char>, Ip.last2(String.append(p, SCon{c, SNil{}}), None{}, None{}), (LIp.pip.lastm(p, None{}), Some{c}), LIp.pip.last2_snoc(p, None{}, None{}, c)) : {Maybe.or(&2, Nat, Ip.v6.go(Ip.edge6(Ip.last.of(_)), rest), Ip.v4.go(Bool.and(Ip.edge4(_), Bool.not(Cx.vctx(String.append(p, SCon{c, SNil{}})))), rest)) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Ip.Sym.free(Ip.Sym.of(c)), S.k_free(S.kind(c)), LIp.pip.free_of(c)) : {Maybe.or(&2, Nat, Ip.v6.go(_, rest), Ip.v4.go(Bool.and(Bool.and(Ip.Sym.edge4(Ip.Sym.of(c)), Bool.not(Bool.and(Char.is_eq(c, '/'), Ip.alpha(LIp.pip.lastm(p, None{}))))), Bool.not(Cx.vctx(String.append(p, SCon{c, SNil{}})))), rest)) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, S.k_free(S.kind(c)), False{}, kf) : {Maybe.or(&2, Nat, Ip.v6.go(_, rest), Ip.v4.go(Bool.and(Bool.and(Ip.Sym.edge4(Ip.Sym.of(c)), Bool.not(Bool.and(Char.is_eq(c, '/'), Ip.alpha(LIp.pip.lastm(p, None{}))))), Bool.not(Cx.vctx(String.append(p, SCon{c, SNil{}})))), rest)) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Ip.Sym.edge4(Ip.Sym.of(c)), S.k_edge4(S.kind(c)), LIp.pip.edge4_of(c)) : {Ip.v4.go(Bool.and(Bool.and(_, Bool.not(Bool.and(Char.is_eq(c, '/'), Ip.alpha(LIp.pip.lastm(p, None{}))))), Bool.not(Cx.vctx(String.append(p, SCon{c, SNil{}})))), rest) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, S.k_edge4(S.kind(c)), False{}, ke) : {Ip.v4.go(Bool.and(Bool.and(_, Bool.not(Bool.and(Char.is_eq(c, '/'), Ip.alpha(LIp.pip.lastm(p, None{}))))), Bool.not(Cx.vctx(String.append(p, SCon{c, SNil{}})))), rest) == None{} : Maybe<&2, Nat>}
  {==}
