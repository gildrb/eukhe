# eukhe: the proof of LAW privacy_ipv4_version_context
#
# PROOF: the line before, reversed, starts with the suffix reversed
# (pip.rev_app); the context reads only that start (the word, or the
# operator) and holds; with a version's context the IPv4 grammar answers
# none whatever follows (pip.v4_ctx).

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../bend/privacy/context.bend as Cx
import ./base/chars.bend as LIp
import ../../laws/privacy/ip.bend as PrivacyIp

def pvc.ctx0(p: String) -> {Cx.vctx(String.append(p, "version ")) == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(p, "version "), SNil{}), String.reverse.go("version ", String.reverse.go(p, SNil{})), LIp.pip.rev_app(p, "version ", SNil{})) : {Cx.vctx.go(Cx.blanks(Cx.line(Cx.VSym.list(_)))) == True{} : Bool}
  {==}

def pvc.ctx1(p: String) -> {Cx.vctx(String.append(p, "Version: \"")) == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(p, "Version: \""), SNil{}), String.reverse.go("Version: \"", String.reverse.go(p, SNil{})), LIp.pip.rev_app(p, "Version: \"", SNil{})) : {Cx.vctx.go(Cx.blanks(Cx.line(Cx.VSym.list(_)))) == True{} : Bool}
  {==}

def pvc.ctx2(p: String) -> {Cx.vctx(String.append(p, "==")) == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(p, "=="), SNil{}), String.reverse.go("==", String.reverse.go(p, SNil{})), LIp.pip.rev_app(p, "==", SNil{})) : {Cx.vctx.go(Cx.blanks(Cx.line(Cx.VSym.list(_)))) == True{} : Bool}
  {==}

def pvc.ctx3(p: String) -> {Cx.vctx(String.append(p, ">=")) == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(p, ">="), SNil{}), String.reverse.go(">=", String.reverse.go(p, SNil{})), LIp.pip.rev_app(p, ">=", SNil{})) : {Cx.vctx.go(Cx.blanks(Cx.line(Cx.VSym.list(_)))) == True{} : Bool}
  {==}

def pvc.ctx4(p: String) -> {Cx.vctx(String.append(p, "<=")) == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(p, "<="), SNil{}), String.reverse.go("<=", String.reverse.go(p, SNil{})), LIp.pip.rev_app(p, "<=", SNil{})) : {Cx.vctx.go(Cx.blanks(Cx.line(Cx.VSym.list(_)))) == True{} : Bool}
  {==}

def pvc.ctx5(p: String) -> {Cx.vctx(String.append(p, "~=")) == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(p, "~="), SNil{}), String.reverse.go("~=", String.reverse.go(p, SNil{})), LIp.pip.rev_app(p, "~=", SNil{})) : {Cx.vctx.go(Cx.blanks(Cx.line(Cx.VSym.list(_)))) == True{} : Bool}
  {==}

def pvc.ctx6(p: String) -> {Cx.vctx(String.append(p, "!=")) == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(p, "!="), SNil{}), String.reverse.go("!=", String.reverse.go(p, SNil{})), LIp.pip.rev_app(p, "!=", SNil{})) : {Cx.vctx.go(Cx.blanks(Cx.line(Cx.VSym.list(_)))) == True{} : Bool}
  {==}

def pvc.ctx7(p: String) -> {Cx.vctx(String.append(p, "^")) == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(p, "^"), SNil{}), String.reverse.go("^", String.reverse.go(p, SNil{})), LIp.pip.rev_app(p, "^", SNil{})) : {Cx.vctx.go(Cx.blanks(Cx.line(Cx.VSym.list(_)))) == True{} : Bool}
  {==}

def pvc.ctx8(p: String) -> {Cx.vctx(String.append(p, "~")) == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(p, "~"), SNil{}), String.reverse.go("~", String.reverse.go(p, SNil{})), LIp.pip.rev_app(p, "~", SNil{})) : {Cx.vctx.go(Cx.blanks(Cx.line(Cx.VSym.list(_)))) == True{} : Bool}
  {==}

def PrivacyIp.privacy_ipv4_version_context(p, s):
  (LIp.pip.v4_ctx(String.append(p, "version "), s, pvc.ctx0(p)), (LIp.pip.v4_ctx(String.append(p, "Version: \""), s, pvc.ctx1(p)), (LIp.pip.v4_ctx(String.append(p, "=="), s, pvc.ctx2(p)), (LIp.pip.v4_ctx(String.append(p, ">="), s, pvc.ctx3(p)), (LIp.pip.v4_ctx(String.append(p, "<="), s, pvc.ctx4(p)), (LIp.pip.v4_ctx(String.append(p, "~="), s, pvc.ctx5(p)), (LIp.pip.v4_ctx(String.append(p, "!="), s, pvc.ctx6(p)), (LIp.pip.v4_ctx(String.append(p, "^"), s, pvc.ctx7(p)), LIp.pip.v4_ctx(String.append(p, "~"), s, pvc.ctx8(p))))))))))
