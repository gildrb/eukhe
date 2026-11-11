# eukhe: the proof of LAW package_source_local_plain
#
# PROOF: trimmed, the value is c then the rest (LA.psb.trim_pre: c is not
# White_Space); c is none of the prefixes' first letters, so the value
# starts with no prefix.

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/gateway_answer.bend as Ga
import ../../laws/package_source/model.bend as PackageSource
import ../base/staging.bend as LStg
import ./base.bend as LA

def psp.sw(+c: Char, z: String, y: Char, p: String, e: {Char.is_eq(c, y) == False{} : Bool}) -> {String.starts_with(SCon{c, z}, SCon{y, p}) == False{} : Bool}:
  %Equal.sym(Bool, Char.is_eq(c, y), False{}, e) : {String.starts_with.go.if(p, z, _) == False{} : Bool}
  {==}

def psp.b6(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool) -> Bool:
  Bool.not(Bool.or(a, Bool.or(b, Bool.or(c, Bool.or(d, Bool.or(e, f))))))

def psp.body(+c: Char, +z: String, +cn: {Bool.or(Char.is_eq(c, 'n'), Bool.or(Char.is_eq(c, 'g'), Bool.or(Char.is_eq(c, 'h'), Char.is_eq(c, 's')))) == False{} : Bool}) -> {LA.psb.lbody(SCon{c, z}) == True{} : Bool}:
  +n = Char.is_eq(c, 'n')
  +g = Char.is_eq(c, 'g')
  +h = Char.is_eq(c, 'h')
  +s = Char.is_eq(c, 's')
  +r1 = LA.psb.or_fr(n, Bool.or(g, Bool.or(h, s)), cn)
  +r2 = LA.psb.or_fr(g, Bool.or(h, s), r1)
  +en = LA.psb.or_fl(n, Bool.or(g, Bool.or(h, s)), cn)
  +eg = LA.psb.or_fl(g, Bool.or(h, s), r1)
  +eh = LA.psb.or_fl(h, s, r2)
  +es = LA.psb.or_fr(h, s, r2)
  +t = {SCon{c, z} : String}
  %Equal.sym(Bool, String.starts_with(t, "npm:"), False{}, psp.sw(c, z, 'n', "pm:", en)) : {psp.b6(_, String.starts_with(t, "git:"), String.starts_with(t, "github:"), String.starts_with(t, "http:"), String.starts_with(t, "https:"), String.starts_with(t, "ssh:")) == True{} : Bool}
  %Equal.sym(Bool, String.starts_with(t, "git:"), False{}, psp.sw(c, z, 'g', "it:", eg)) : {psp.b6(False{}, _, String.starts_with(t, "github:"), String.starts_with(t, "http:"), String.starts_with(t, "https:"), String.starts_with(t, "ssh:")) == True{} : Bool}
  %Equal.sym(Bool, String.starts_with(t, "github:"), False{}, psp.sw(c, z, 'g', "ithub:", eg)) : {psp.b6(False{}, False{}, _, String.starts_with(t, "http:"), String.starts_with(t, "https:"), String.starts_with(t, "ssh:")) == True{} : Bool}
  %Equal.sym(Bool, String.starts_with(t, "http:"), False{}, psp.sw(c, z, 'h', "ttp:", eh)) : {psp.b6(False{}, False{}, False{}, _, String.starts_with(t, "https:"), String.starts_with(t, "ssh:")) == True{} : Bool}
  %Equal.sym(Bool, String.starts_with(t, "https:"), False{}, psp.sw(c, z, 'h', "ttps:", eh)) : {psp.b6(False{}, False{}, False{}, False{}, _, String.starts_with(t, "ssh:")) == True{} : Bool}
  %Equal.sym(Bool, String.starts_with(t, "ssh:"), False{}, psp.sw(c, z, 's', "sh:", es)) : {psp.b6(False{}, False{}, False{}, False{}, False{}, _) == True{} : Bool}
  {==}

def psp.lsp(+c: Char, +x: String, ed: {Ga.space(c) == False{} : Bool}) -> {Ps.lspace(SCon{c, x}) == SCon{c, x} : String}:
  %Equal.sym(Bool, Ga.space(c), False{}, ed) : {Ps.lspace.at(_, c, x, Ps.lspace(x)) == SCon{c, x} : String}
  {==}

def PackageSource.package_source_local_plain(w, b, c, cw, cn, x):
  +ed = LA.psb.sp_f(c, cw)
  +z = String.reverse(Ps.lspace(String.reverse(x)))
  %LA.psb.local(String.append(w, SCon{c, x})) : {_ == True{} : Bool}
  %Equal.sym(String, Ps.trim(String.append(w, String.append(SCon{c, SNil{}}, x))), String.append(SCon{c, SNil{}}, z), LA.psb.trim_pre(w, b, SCon{c, SNil{}}, x, psp.lsp(c, x, ed), c, SNil{}, {==}, ed)) : {LA.psb.lbody(_) == True{} : Bool}
  psp.body(c, z, cn)
