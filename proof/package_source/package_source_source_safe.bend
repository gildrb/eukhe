# eukhe: the proof of LAW package_source_source_safe
#
# PROOF: an `npm:` source is accepted only when the code finds no argument
# defect in its spec and no relative-path defect in its package name
# (LA.psb.arg, LA.psb.rel); a git source is a safe git answer
# (LA.psb.git); a local path is safe as given.

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/gateway_answer.bend as Ga
import ../../laws/package_source/model.bend as PackageSource
import ../base/staging.bend as LStg
import ./base.bend as LA

def pss.src_ok(p: Ps.Parsed) -> Bool:
  match p:
    case Ps.Parsed{x}:
      PackageSource.ps_src_ok(x)
    case Ps.Refused{f}:
      True{}

def pss.npm.ok(m: Maybe<&2, Ps.Defect>, +name: String, pin: Bool, +spec: String, ea: {True{} == PackageSource.ps_arg_ok(spec) : Bool}, en: {LA.psb.none_d(m) == PackageSource.ps_rel_ok(name) : Bool}) -> {pss.src_ok(Ps.npm.ok(m, name, pin, spec)) == True{} : Bool}:
  match m:
    case None{}:
      %ea : {Bool.and(_, PackageSource.ps_rel_ok(name)) == True{} : Bool}
      %en : {Bool.and(True{}, _) == True{} : Bool}
      {==}
    case Some{d}:
      {==}

def pss.npm.name(ns: Ps.NpmSpec, +spec: String, ea: {True{} == PackageSource.ps_arg_ok(spec) : Bool}) -> {pss.src_ok(Ps.npm.name(ns, spec)) == True{} : Bool}:
  match ns:
    case Ps.NpmSpec{+name, v}:
      pss.npm.ok(Ps.rel(name), name, Ps.is_some(v), spec, ea, LA.psb.rel(name))

def pss.npm.at(m: Maybe<&2, Ps.Defect>, +spec: String, e: {LA.psb.none_d(m) == PackageSource.ps_arg_ok(spec) : Bool}) -> {pss.src_ok(Ps.npm.at(m, spec)) == True{} : Bool}:
  match m:
    case None{}:
      pss.npm.name(Ps.npm_spec(spec), spec, e)
    case Some{d}:
      {==}

def pss.git(a: Ps.GitAns, s: String, e: {LA.psb.ans_ok(a) == True{} : Bool}) -> {pss.src_ok(Ps.source.git(a, s)) == True{} : Bool}:
  match a:
    case Ps.NoGit{}:
      {==}
    case Ps.IsGit{g}:
      e
    case Ps.BadGit{f}:
      {==}

def pss.local(b: Bool, +s: String) -> {pss.src_ok(Ps.source.local(b, s)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pss.git(Ps.git(s), s, LA.psb.git(s))

def pss.at(b: Bool, +s: String) -> {pss.src_ok(Ps.source.at(b, s)) == True{} : Bool}:
  match b:
    case True{}:
      +spec = Ps.trim(String.drop(s, 4n))
      pss.npm.at(Ps.arg(spec), spec, LA.psb.arg(spec))
    case False{}:
      pss.local(Ps.local(s), s)

def PackageSource.package_source_source_safe(s, x, got):
  %got : {pss.src_ok(_) == True{} : Bool}
  pss.at(String.starts_with(s, "npm:"), s)
