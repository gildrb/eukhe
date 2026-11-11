# eukhe: the proof of LAW package_source_local_prefixed
#
# PROOF: trimmed, the value is the prefix then the rest of x
# (LA.psb.trim_pre: the prefix starts and ends with a char that is not
# White_Space), so it starts with the prefix.

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/gateway_answer.bend as Ga
import ../../laws/package_source/model.bend as PackageSource
import ../base/staging.bend as LStg
import ./base.bend as LA

def psl.pre(+w: String, b: {PackageSource.ps_blank(w) == True{} : Bool}, +p: String, +x: String, ep: {Ps.lspace(String.append(p, x)) == String.append(p, x) : String}, +d: Char, +r: String, er: {String.reverse(p) == SCon{d, r} : String}, ed: {Ga.space(d) == False{} : Bool}, eb: {LA.psb.lbody(String.append(p, String.reverse(Ps.lspace(String.reverse(x))))) == False{} : Bool}) -> {Ps.local(String.append(w, String.append(p, x))) == False{} : Bool}:
  %LA.psb.local(String.append(w, String.append(p, x))) : {_ == False{} : Bool}
  %Equal.sym(String, Ps.trim(String.append(w, String.append(p, x))), String.append(p, String.reverse(Ps.lspace(String.reverse(x)))), LA.psb.trim_pre(w, b, p, x, ep, d, r, er, ed)) : {LA.psb.lbody(_) == False{} : Bool}
  eb

def PackageSource.package_source_local_prefixed(w, b, x):
  (psl.pre(w, b, "npm:", x, {==}, ':', "mpn", {==}, {==}, {==}), psl.pre(w, b, "git:", x, {==}, ':', "tig", {==}, {==}, {==}), psl.pre(w, b, "github:", x, {==}, ':', "buhtig", {==}, {==}, {==}), psl.pre(w, b, "http:", x, {==}, ':', "ptth", {==}, {==}, {==}), psl.pre(w, b, "https:", x, {==}, ':', "sptth", {==}, {==}, {==}), psl.pre(w, b, "ssh:", x, {==}, ':', "hss", {==}, {==}, {==}))
