# eukhe: the proof of LAW package_source_npm_spec_whole
#
# PROOF: after the first char, t holds no `@` (no cut: PNa.pna.none), or
# its first `@` is the last char (an empty version: PNa.pna.cut).

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/gateway_answer.bend as Ga
import ../../laws/package_source/model.bend as PackageSource
import ../base/staging.bend as LStg
import ./base.bend as LA
import ./package_source_npm_spec_first_at.bend as PNa

def pnw.one(+c: Char, +t: String, na: {PackageSource.ps_no_at(t) == True{} : Bool}) -> {Ps.npm_spec(SCon{c, t}) == Ps.NpmSpec{SCon{c, t}, None{}} : Ps.NpmSpec}:
  %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(t, '@'), None{}, PNa.pna.none(t, na)) : {Ps.npm_spec.at(_, c, t) == Ps.NpmSpec{SCon{c, t}, None{}} : Ps.NpmSpec}
  {==}

def pnw.two(+c: Char, +t: String, na: {PackageSource.ps_no_at(t) == True{} : Bool}) -> {Ps.npm_spec(String.append(SCon{c, t}, "@")) == Ps.NpmSpec{String.append(SCon{c, t}, "@"), None{}} : Ps.NpmSpec}:
  +rest = String.append(t, SCon{'@', SNil{}})
  %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(rest, '@'), Some{Ps.Cut{t, SNil{}}}, PNa.pna.cut(t, SNil{}, na)) : {Ps.npm_spec.at(_, c, rest) == Ps.NpmSpec{SCon{c, rest}, None{}} : Ps.NpmSpec}
  {==}

def PackageSource.package_source_npm_spec_whole(c, t, na):
  ({==}, pnw.one(c, t, na), pnw.two(c, t, na))
