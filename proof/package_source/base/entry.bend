# eukhe: lemmas of the entry proofs of area package_source: the reply
# encoders are the spec spellers, a spelled request reads back (pse.*_rt),
# and a decoded one is spelled (rix.*: a predicate per decoder answer,
# carried stage by stage with the wire exactness lemmas dcw.nat, dcw.str)

import Base
import ../../../bend/package_source.bend as Ps
import ../../../bend/ffi_package_source.bend as FPs
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/package_source/model.bend as PackageSource
import ../../../laws/package_source/entry.bend as PackageSourceEntry
import ../../base/wire_dec.bend as LE
import ../../base/staging.bend as LStg

# Encoders
# --------

def pse.ms(m: Maybe<&2, String>, rest: String) -> {FPs.put_ms(m, rest) == PackageSourceEntry.ps_w_ms(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def pse.part(p: Ps.Part, rest: String) -> {FPs.put_part(p, rest) == PackageSourceEntry.ps_w_part(p, rest) : String}:
  match p:
    case Ps.PHost{}:
      {==}
    case Ps.PPath{}:
      {==}
    case Ps.PRef{}:
      {==}
    case Ps.PClone{}:
      {==}
    case Ps.PSpec{}:
      {==}
    case Ps.PName{}:
      {==}

def pse.defect(d: Ps.Defect, rest: String) -> {FPs.put_defect(d, rest) == PackageSourceEntry.ps_w_defect(d, rest) : String}:
  match d:
    case Ps.DEmpty{}:
      {==}
    case Ps.DEmptySeg{}:
      {==}
    case Ps.DDot{}:
      {==}
    case Ps.DDrive{}:
      {==}
    case Ps.DBackslash{}:
      {==}
    case Ps.DControl{}:
      {==}
    case Ps.DDash{}:
      {==}
    case Ps.DSlash{}:
      {==}

def pse.flaw(f: Ps.Flaw, +rest: String) -> {FPs.put_flaw(f, rest) == PackageSourceEntry.ps_w_flaw(f, rest) : String}:
  match f:
    case Ps.Flaw{+p, +d}:
      %Equal.sym(String, FPs.put_defect(d, rest), PackageSourceEntry.ps_w_defect(d, rest), pse.defect(d, rest)) : {FPs.put_part(p, _) == PackageSourceEntry.ps_w_flaw(Ps.Flaw{p, d}, rest) : String}
      pse.part(p, PackageSourceEntry.ps_w_defect(d, rest))

def pse.git(g: Ps.GitSrc, +rest: String) -> {FPs.put_git(g, rest) == PackageSourceEntry.ps_w_git(g, rest) : String}:
  match g:
    case Ps.GitSrc{+repo, +h, +p, +r, +n}:
      %Equal.sym(String, FPs.put_ms(r, Wr.put_bool(n, rest)), PackageSourceEntry.ps_w_ms(r, Wr.put_bool(n, rest)), pse.ms(r, Wr.put_bool(n, rest))) : {Wr.put_str(repo, Wr.put_str(h, Wr.put_str(p, _))) == PackageSourceEntry.ps_w_git(Ps.GitSrc{repo, h, p, r, n}, rest) : String}
      {==}

def pse.src(x: Ps.Src) -> {FPs.put_src(x) == PackageSourceEntry.ps_w_src(x) : String}:
  match x:
    case Ps.SrcNpm{m}:
      match m:
        case Ps.NpmSrc{spec, name, n}:
          {==}
    case Ps.SrcGit{+g}:
      %Equal.sym(String, FPs.put_git(g, ""), PackageSourceEntry.ps_w_git(g, ""), pse.git(g, "")) : {Wr.put_nat(1n, _) == PackageSourceEntry.ps_w_src(Ps.SrcGit{g}) : String}
      {==}
    case Ps.SrcLocal{p}:
      {==}

def pse.parsed(a: Ps.Parsed) -> {FPs.put_parsed(a) == PackageSourceEntry.ps_w_parsed(a) : String}:
  match a:
    case Ps.Parsed{+x}:
      %Equal.sym(String, FPs.put_src(x), PackageSourceEntry.ps_w_src(x), pse.src(x)) : {Wr.put_nat(0n, _) == PackageSourceEntry.ps_w_parsed(Ps.Parsed{x}) : String}
      {==}
    case Ps.Refused{+f}:
      %Equal.sym(String, FPs.put_flaw(f, ""), PackageSourceEntry.ps_w_flaw(f, ""), pse.flaw(f, "")) : {Wr.put_nat(1n, _) == PackageSourceEntry.ps_w_parsed(Ps.Refused{f}) : String}
      {==}

def pse.gitans(a: Ps.GitAns) -> {FPs.put_gitans(a) == PackageSourceEntry.ps_w_gitans(a) : String}:
  match a:
    case Ps.NoGit{}:
      {==}
    case Ps.IsGit{+g}:
      %Equal.sym(String, FPs.put_git(g, ""), PackageSourceEntry.ps_w_git(g, ""), pse.git(g, "")) : {Wr.put_nat(1n, _) == PackageSourceEntry.ps_w_gitans(Ps.IsGit{g}) : String}
      {==}
    case Ps.BadGit{+f}:
      %Equal.sym(String, FPs.put_flaw(f, ""), PackageSourceEntry.ps_w_flaw(f, ""), pse.flaw(f, "")) : {Wr.put_nat(2n, _) == PackageSourceEntry.ps_w_gitans(Ps.BadGit{f}) : String}
      {==}

def pse.spec(n: Ps.NpmSpec) -> {FPs.put_spec(n) == PackageSourceEntry.ps_w_spec(n) : String}:
  match n:
    case Ps.NpmSpec{+name, +v}:
      %Equal.sym(String, FPs.put_ms(v, ""), PackageSourceEntry.ps_w_ms(v, ""), pse.ms(v, "")) : {Wr.put_str(name, _) == PackageSourceEntry.ps_w_spec(Ps.NpmSpec{name, v}) : String}
      {==}

# Round trips
# -----------

def pse.part_rt(p: Ps.Part, rest: String) -> {FPs.get_part(PackageSourceEntry.ps_w_part(p, rest)) == Wr.Got{p, rest} : Wr.Dec<Ps.Part>}:
  match p:
    case Ps.PHost{}:
      {==}
    case Ps.PPath{}:
      {==}
    case Ps.PRef{}:
      {==}
    case Ps.PClone{}:
      {==}
    case Ps.PSpec{}:
      {==}
    case Ps.PName{}:
      {==}

def pse.defect_rt(d: Ps.Defect, rest: String) -> {FPs.get_defect(PackageSourceEntry.ps_w_defect(d, rest)) == Wr.Got{d, rest} : Wr.Dec<Ps.Defect>}:
  match d:
    case Ps.DEmpty{}:
      {==}
    case Ps.DEmptySeg{}:
      {==}
    case Ps.DDot{}:
      {==}
    case Ps.DDrive{}:
      {==}
    case Ps.DBackslash{}:
      {==}
    case Ps.DControl{}:
      {==}
    case Ps.DDash{}:
      {==}
    case Ps.DSlash{}:
      {==}

def pse.flaw_rt(f: Ps.Flaw, +rest: String) -> {FPs.get_flaw(PackageSourceEntry.ps_w_flaw(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Ps.Flaw>}:
  match f:
    case Ps.Flaw{+p, +d}:
      %Equal.sym(Wr.Dec<Ps.Part>, FPs.get_part(PackageSourceEntry.ps_w_part(p, PackageSourceEntry.ps_w_defect(d, rest))), Wr.Got{p, PackageSourceEntry.ps_w_defect(d, rest)}, pse.part_rt(p, PackageSourceEntry.ps_w_defect(d, rest))) : {FPs.get_flaw.part(_) == Wr.Got{Ps.Flaw{p, d}, rest} : Wr.Dec<Ps.Flaw>}
      %Equal.sym(Wr.Dec<Ps.Defect>, FPs.get_defect(PackageSourceEntry.ps_w_defect(d, rest)), Wr.Got{d, rest}, pse.defect_rt(d, rest)) : {FPs.get_flaw.defect(p, _) == Wr.Got{Ps.Flaw{p, d}, rest} : Wr.Dec<Ps.Flaw>}
      {==}

def pse.req_rt(q: FPs.Req, +rest: String, h: {PackageSourceEntry.ps_fit_req(q) == True{} : Bool}) -> {FPs.get_req(PackageSourceEntry.ps_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FPs.Req>}:
  match q:
    case FPs.QSource{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FPs.get_source(_) == Wr.Got{FPs.QSource{x}, rest} : Wr.Dec<FPs.Req>}
      {==}
    case FPs.QGit{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FPs.get_git(_) == Wr.Got{FPs.QGit{x}, rest} : Wr.Dec<FPs.Req>}
      {==}
    case FPs.QLocal{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FPs.get_local(_) == Wr.Got{FPs.QLocal{x}, rest} : Wr.Dec<FPs.Req>}
      {==}
    case FPs.QNpm{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FPs.get_npm(_) == Wr.Got{FPs.QNpm{x}, rest} : Wr.Dec<FPs.Req>}
      {==}
    case FPs.QPart{+p}:
      %Equal.sym(Wr.Dec<Ps.Part>, FPs.get_part(PackageSourceEntry.ps_w_part(p, rest)), Wr.Got{p, rest}, pse.part_rt(p, rest)) : {FPs.get_qpart(_) == Wr.Got{FPs.QPart{p}, rest} : Wr.Dec<FPs.Req>}
      {==}
    case FPs.QDefect{+d}:
      %Equal.sym(Wr.Dec<Ps.Defect>, FPs.get_defect(PackageSourceEntry.ps_w_defect(d, rest)), Wr.Got{d, rest}, pse.defect_rt(d, rest)) : {FPs.get_qdefect(_) == Wr.Got{FPs.QDefect{d}, rest} : Wr.Dec<FPs.Req>}
      {==}
    case FPs.QError{+x, +f}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, PackageSourceEntry.ps_w_flaw(f, rest))), Wr.Got{x, PackageSourceEntry.ps_w_flaw(f, rest)}, Wire.wire_str_round_trip(x, PackageSourceEntry.ps_w_flaw(f, rest), h)) : {FPs.get_error(_) == Wr.Got{FPs.QError{x, f}, rest} : Wr.Dec<FPs.Req>}
      %Equal.sym(Wr.Dec<Ps.Flaw>, FPs.get_flaw(PackageSourceEntry.ps_w_flaw(f, rest)), Wr.Got{f, rest}, pse.flaw_rt(f, rest)) : {FPs.get_error.flaw(x, _) == Wr.Got{FPs.QError{x, f}, rest} : Wr.Dec<FPs.Req>}
      {==}

# Replies never open with 'E'
# ---------------------------

def pse.bool_ok(b: Bool) -> {LawsBase.wire_opens_err(Wr.put_bool(b, "")) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pse.parsed_ok(a: Ps.Parsed) -> {LawsBase.wire_opens_err(FPs.put_parsed(a)) == False{} : Bool}:
  match a:
    case Ps.Parsed{x}:
      {==}
    case Ps.Refused{f}:
      {==}

def pse.gitans_ok(a: Ps.GitAns) -> {LawsBase.wire_opens_err(FPs.put_gitans(a)) == False{} : Bool}:
  match a:
    case Ps.NoGit{}:
      {==}
    case Ps.IsGit{g}:
      {==}
    case Ps.BadGit{f}:
      {==}

def pse.spec_ok(n: Ps.NpmSpec) -> {LawsBase.wire_opens_err(FPs.put_spec(n)) == False{} : Bool}:
  match n:
    case Ps.NpmSpec{name, v}:
      LE.dcw.sfin_ok(Wr.put_str.go(name, SNil{}, 0n), FPs.put_ms(v, ""))

def pse.reply_ok(q: FPs.Req) -> {LawsBase.wire_opens_err(FPs.answer(q)) == False{} : Bool}:
  match q:
    case FPs.QSource{x}:
      pse.parsed_ok(Ps.source(x))
    case FPs.QGit{x}:
      pse.gitans_ok(Ps.git(x))
    case FPs.QLocal{x}:
      pse.bool_ok(Ps.local(x))
    case FPs.QNpm{x}:
      pse.spec_ok(Ps.npm_spec(x))
    case FPs.QPart{p}:
      LE.dcw.sfin_ok(Wr.put_str.go(Ps.part_text(p), SNil{}, 0n), "")
    case FPs.QDefect{d}:
      LE.dcw.sfin_ok(Wr.put_str.go(Ps.defect_text(d), SNil{}, 0n), "")
    case FPs.QError{x, f}:
      LE.dcw.sfin_ok(Wr.put_str.go(Ps.error_text(x, f), SNil{}, 0n), "")

# Decoded requests are spelled
# ----------------------------

def rix.PP(s: String, d: Wr.Dec<Ps.Part>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == PackageSourceEntry.ps_w_part(p, r) : String}
    case Wr.Bad{}:
      Unit

def rix.part_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rix.PP(s, FPs.get_part.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          np
        case 1n:
          np
        case 2n:
          np
        case 3n:
          np
        case 4n:
          np
        case 5n:
          np
        case 6n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a part decoded is spelled
def rix.part(+s: String) -> rix.PP(s, FPs.get_part(s)):
  rix.part_at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rix.DP(s: String, d: Wr.Dec<Ps.Defect>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == PackageSourceEntry.ps_w_defect(x, r) : String}
    case Wr.Bad{}:
      Unit

def rix.defect_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rix.DP(s, FPs.get_defect.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          np
        case 1n:
          np
        case 2n:
          np
        case 3n:
          np
        case 4n:
          np
        case 5n:
          np
        case 6n:
          np
        case 7n:
          np
        case 8n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a defect decoded is spelled
def rix.defect(+s: String) -> rix.DP(s, FPs.get_defect(s)):
  rix.defect_at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rix.FP(s: String, d: Wr.Dec<Ps.Flaw>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == PackageSourceEntry.ps_w_flaw(f, r) : String}
    case Wr.Bad{}:
      Unit

def rix.flaw_d(-s: String, +p: Ps.Part, -s1: String, pre: {s == PackageSourceEntry.ps_w_part(p, s1) : String}, d: Wr.Dec<Ps.Defect>, dp: rix.DP(s1, d)) -> rix.FP(s, FPs.get_flaw.defect(p, d)):
  match d:
    case Wr.Got{+x, +r}:
      Equal.trans(String, s, PackageSourceEntry.ps_w_part(p, s1), PackageSourceEntry.ps_w_part(p, PackageSourceEntry.ps_w_defect(x, r)), pre, Equal.cong(String, String, z => PackageSourceEntry.ps_w_part(p, z), s1, PackageSourceEntry.ps_w_defect(x, r), dp))
    case Wr.Bad{}:
      Unit{}

def rix.flaw_p(-s: String, d: Wr.Dec<Ps.Part>, pp: rix.PP(s, d)) -> rix.FP(s, FPs.get_flaw.part(d)):
  match d:
    case Wr.Got{+p, +s1}:
      rix.flaw_d(s, p, s1, pp, FPs.get_defect(s1), rix.defect(s1))
    case Wr.Bad{}:
      Unit{}

# a flaw decoded is spelled
def rix.flaw(+s: String) -> rix.FP(s, FPs.get_flaw(s)):
  rix.flaw_p(s, FPs.get_part(s), rix.part(s))

def rix.RP(s: String, d: Wr.Dec<FPs.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == PackageSourceEntry.ps_w_req(q, r) : String} & {PackageSourceEntry.ps_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rix.source(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.RP(s, FPs.get_source(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = sp
      (LE.dcw.after(s, 0n, s1, Wr.put_str(x, r), pre, e), fx)
    case Wr.Bad{}:
      Unit{}

def rix.git(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.RP(s, FPs.get_git(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = sp
      (LE.dcw.after(s, 1n, s1, Wr.put_str(x, r), pre, e), fx)
    case Wr.Bad{}:
      Unit{}

def rix.local(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.RP(s, FPs.get_local(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = sp
      (LE.dcw.after(s, 2n, s1, Wr.put_str(x, r), pre, e), fx)
    case Wr.Bad{}:
      Unit{}

def rix.npm(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.RP(s, FPs.get_npm(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = sp
      (LE.dcw.after(s, 3n, s1, Wr.put_str(x, r), pre, e), fx)
    case Wr.Bad{}:
      Unit{}

def rix.qpart(-s: String, -s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<Ps.Part>, pp: rix.PP(s1, d)) -> rix.RP(s, FPs.get_qpart(d)):
  match d:
    case Wr.Got{+p, +r}:
      (LE.dcw.after(s, 4n, s1, PackageSourceEntry.ps_w_part(p, r), pre, pp), {==})
    case Wr.Bad{}:
      Unit{}

def rix.qdefect(-s: String, -s1: String, pre: {s == Wr.put_nat(5n, s1) : String}, d: Wr.Dec<Ps.Defect>, dp: rix.DP(s1, d)) -> rix.RP(s, FPs.get_qdefect(d)):
  match d:
    case Wr.Got{+x, +r}:
      (LE.dcw.after(s, 5n, s1, PackageSourceEntry.ps_w_defect(x, r), pre, dp), {==})
    case Wr.Bad{}:
      Unit{}

def rix.qerror_f(-s: String, +x: String, -s2: String, pre: {s == Wr.put_nat(6n, Wr.put_str(x, s2)) : String}, fx: {PackageSourceEntry.ps_fit_str(x) == True{} : Bool}, d: Wr.Dec<Ps.Flaw>, fp: rix.FP(s2, d)) -> rix.RP(s, FPs.get_error.flaw(x, d)):
  match d:
    case Wr.Got{+f, +r}:
      (Equal.trans(String, s, Wr.put_nat(6n, Wr.put_str(x, s2)), Wr.put_nat(6n, Wr.put_str(x, PackageSourceEntry.ps_w_flaw(f, r))), pre, Equal.cong(String, String, z => Wr.put_nat(6n, Wr.put_str(x, z)), s2, PackageSourceEntry.ps_w_flaw(f, r), fp)), fx)
    case Wr.Bad{}:
      Unit{}

def rix.qerror(-s: String, -s1: String, pre: {s == Wr.put_nat(6n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.RP(s, FPs.get_error(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e1, fx) = sp
      rix.qerror_f(s, x, r, LE.dcw.after(s, 6n, s1, Wr.put_str(x, r), pre, e1), fx, FPs.get_flaw(r), rix.flaw(r))
    case Wr.Bad{}:
      Unit{}

def rix.req_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rix.RP(s, FPs.get_req.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          rix.source(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 1n:
          rix.git(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 2n:
          rix.local(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 3n:
          rix.npm(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 4n:
          rix.qpart(s, s1, np, FPs.get_part(s1), rix.part(s1))
        case 5n:
          rix.qdefect(s, s1, np, FPs.get_defect(s1), rix.defect(s1))
        case 6n:
          rix.qerror(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 7n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rix.T(s: String) -> Type:
  Sigma<&1, &1, FPs.Req, q => {s == PackageSourceEntry.ps_w_req(q, "") : String} & {PackageSourceEntry.ps_fit_req(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def rix.top(-s: String, d: Wr.Dec<FPs.Req>, rp: rix.RP(s, d), ok: {LawsBase.wire_opens_err(FPs.ffi.got(d)) == False{} : Bool}) -> rix.T(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(rix.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(rix.T(s), ok)
