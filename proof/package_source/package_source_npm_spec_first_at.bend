# eukhe: the proof of LAW package_source_npm_spec_first_at
#
# PROOF: the spec after its first char splits at its first `@`, the one
# after t (pna.cut: t holds none); the version after it is not empty.

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/gateway_answer.bend as Ga
import ../../laws/package_source/model.bend as PackageSource
import ../base/staging.bend as LStg
import ./base.bend as LA

def pna.at_f(+c: Char, t: String, +e: {PackageSource.ps_no_at(SCon{c, t}) == True{} : Bool}) -> {Char.is_eq(c, '@') == False{} : Bool}:
  LA.psb.not_t(Char.is_eq(c, '@'), LStg.stg.and_l(Bool.not(Char.is_eq(c, '@')), PackageSource.ps_no_at(t), e))

# t without `@`, then `@` and r: cut at that `@`
def pna.cut(t: String, +r: String, +e: {PackageSource.ps_no_at(t) == True{} : Bool}) -> {Ps.cut(String.append(t, SCon{'@', r}), '@') == Some{Ps.Cut{t, r}} : Maybe<&2, Ps.Cut>}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +rest = String.append(u, SCon{'@', r})
      %Equal.sym(Bool, Char.is_eq(c, '@'), False{}, pna.at_f(c, u, e)) : {Ps.cut.at(_, c, rest, Ps.cut(rest, '@')) == Some{Ps.Cut{SCon{c, u}, r}} : Maybe<&2, Ps.Cut>}
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(rest, '@'), Some{Ps.Cut{u, r}}, pna.cut(u, r, LStg.stg.and_r(Bool.not(Char.is_eq(c, '@')), PackageSource.ps_no_at(u), e))) : {Ps.cut.at(False{}, c, rest, _) == Some{Ps.Cut{SCon{c, u}, r}} : Maybe<&2, Ps.Cut>}
      {==}

# t without `@`: no cut
def pna.none(t: String, +e: {PackageSource.ps_no_at(t) == True{} : Bool}) -> {Ps.cut(t, '@') == None{} : Maybe<&2, Ps.Cut>}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      %Equal.sym(Bool, Char.is_eq(c, '@'), False{}, pna.at_f(c, u, e)) : {Ps.cut.at(_, c, u, Ps.cut(u, '@')) == None{} : Maybe<&2, Ps.Cut>}
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(u, '@'), None{}, pna.none(u, LStg.stg.and_r(Bool.not(Char.is_eq(c, '@')), PackageSource.ps_no_at(u), e))) : {Ps.cut.at(False{}, c, u, _) == None{} : Maybe<&2, Ps.Cut>}
      {==}

def PackageSource.package_source_npm_spec_first_at(c, t, na, x, v):
  +rest = String.append(t, SCon{'@', SCon{x, v}})
  %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(rest, '@'), Some{Ps.Cut{t, SCon{x, v}}}, pna.cut(t, SCon{x, v}, na)) : {Ps.npm_spec.at(_, c, rest) == Ps.NpmSpec{SCon{c, t}, Some{SCon{x, v}}} : Ps.NpmSpec}
  {==}
