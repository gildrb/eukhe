# eukhe: the proof of LAW error_body_entry_exact
#
# PROOF: each decoder stage of bend/ffi_error_body.bend answers Got{x,
# rest} only for an input that is the spec's spelling of what it read so
# far before rest, every number and length within the wire (ebx.*: per
# field kind a predicate on its decoder's answer: wire_nat_exact,
# wire_nat_decoded_fits, wire_bool_exact, the string lemmas of LE.dcw.str,
# and ebx.mstr, ebx.probe built from them; each stage carries `pre`, the
# input spelled up to its field). The entry answers a value only for a
# request read whole with nothing left: that input is the spelled request
# (ebx.top).

import Base
import ../../bend/error_body.bend as Eb
import ../../bend/ffi_error_body.bend as FEb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/error_body.bend as ErrorBody
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LE

def ebx.RP(s: String, d: Wr.Dec<FEb.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ErrorBody.sp_w_req(q, r) : String} & {ErrorBody.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# Maybe<String>
def ebx.MSP(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == ErrorBody.sp_w_mstr(m, r) : String} & {ErrorBody.sp_fit_mstr(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ebx.mstr.of(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> ebx.MSP(s, FEb.get_mstr.of(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = sp
      (LE.dcw.after(s, 1n, s1, Wr.put_str(x, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def ebx.mstr.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ebx.MSP(s, FEb.get_mstr.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, ed), {==})
        case 1n:
          ebx.mstr.of(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_str(s1), LE.dcw.str(s1))
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ebx.mstr(+s: String) -> ebx.MSP(s, FEb.get_mstr(s)):
  ebx.mstr.at(s, Wr.get_nat(s), {==})

# a probe
def ebx.PP(s: String, d: Wr.Dec<Eb.Probe>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == ErrorBody.sp_w_probe(p, r) : String} & {ErrorBody.sp_fit_probe(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ebx.probe.text(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> ebx.PP(s, FEb.get_probe.text(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = sp
      (LE.dcw.after(s, 1n, s1, Wr.put_str(x, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def ebx.probe.obj(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> ebx.PP(s, FEb.get_probe.obj(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = sp
      (LE.dcw.after(s, 2n, s1, Wr.put_str(x, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def ebx.probe.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ebx.PP(s, FEb.get_probe.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, ed), {==})
        case 1n:
          ebx.probe.text(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_str(s1), LE.dcw.str(s1))
        case 2n:
          ebx.probe.obj(s, s1, Wire.wire_nat_exact(s, 2n, s1, ed), Wr.get_str(s1), LE.dcw.str(s1))
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ebx.probe(+s: String) -> ebx.PP(s, FEb.get_probe(s)):
  ebx.probe.at(s, Wr.get_nat(s), {==})

# the body's question
def ebx.body.r(-s: String, +b: Eb.Probe, +e: Eb.Probe, +s2: String, pre: {s == Wr.put_nat(0n, ErrorBody.sp_w_probe(b, ErrorBody.sp_w_probe(e, s2))) : String}, fb: {ErrorBody.sp_fit_probe(b) == True{} : Bool}, fe: {ErrorBody.sp_fit_probe(e) == True{} : Bool}, dd: Wr.Dec<Eb.Probe>, pp: ebx.PP(s2, dd)) -> ebx.RP(s, FEb.get_body.r(b, e, dd)):
  match dd:
    case Wr.Got{+r, +rr}:
      (eq, fr) = pp
      (Equal.trans(String, s, Wr.put_nat(0n, ErrorBody.sp_w_probe(b, ErrorBody.sp_w_probe(e, s2))), Wr.put_nat(0n, ErrorBody.sp_w_probe(b, ErrorBody.sp_w_probe(e, ErrorBody.sp_w_probe(r, rr)))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, ErrorBody.sp_w_probe(b, ErrorBody.sp_w_probe(e, z))), s2, ErrorBody.sp_w_probe(r, rr), eq)), LBool.cb_and_intro(ErrorBody.sp_fit_probe(b), Bool.and(ErrorBody.sp_fit_probe(e), ErrorBody.sp_fit_probe(r)), fb, LBool.cb_and_intro(ErrorBody.sp_fit_probe(e), ErrorBody.sp_fit_probe(r), fe, fr)))
    case Wr.Bad{}:
      Unit{}

def ebx.body.e(-s: String, +b: Eb.Probe, +s1: String, pre: {s == Wr.put_nat(0n, ErrorBody.sp_w_probe(b, s1)) : String}, fb: {ErrorBody.sp_fit_probe(b) == True{} : Bool}, dd: Wr.Dec<Eb.Probe>, pp: ebx.PP(s1, dd)) -> ebx.RP(s, FEb.get_body.e(b, dd)):
  match dd:
    case Wr.Got{+e, +rr}:
      (eq, fe) = pp
      ebx.body.r(s, b, e, rr, Equal.trans(String, s, Wr.put_nat(0n, ErrorBody.sp_w_probe(b, s1)), Wr.put_nat(0n, ErrorBody.sp_w_probe(b, ErrorBody.sp_w_probe(e, rr))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, ErrorBody.sp_w_probe(b, z)), s1, ErrorBody.sp_w_probe(e, rr), eq)), fb, fe, FEb.get_probe(rr), ebx.probe(rr))
    case Wr.Bad{}:
      Unit{}

def ebx.body.b(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, dd: Wr.Dec<Eb.Probe>, pp: ebx.PP(s0, dd)) -> ebx.RP(s, FEb.get_body(dd)):
  match dd:
    case Wr.Got{+b, +rr}:
      (eq, fb) = pp
      ebx.body.e(s, b, rr, Equal.trans(String, s, Wr.put_nat(0n, s0), Wr.put_nat(0n, ErrorBody.sp_w_probe(b, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s0, ErrorBody.sp_w_probe(b, rr), eq)), fb, FEb.get_probe(rr), ebx.probe(rr))
    case Wr.Bad{}:
      Unit{}

# the display question
def ebx.show.m(-s: String, +c: Bool, +st: Maybe<&2, String>, +b: Maybe<&2, String>, +p: Maybe<&2, String>, +s4: String, pre: {s == Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, ErrorBody.sp_w_mstr(b, ErrorBody.sp_w_mstr(p, s4))))) : String}, fst: {ErrorBody.sp_fit_mstr(st) == True{} : Bool}, fb: {ErrorBody.sp_fit_mstr(b) == True{} : Bool}, fp: {ErrorBody.sp_fit_mstr(p) == True{} : Bool}, dd: Wr.Dec<String>, pp: LE.dcw.SP(s4, dd)) -> ebx.RP(s, FEb.get_show.m(c, st, b, p, dd)):
  match dd:
    case Wr.Got{+m, +rr}:
      (eq, fm) = pp
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, ErrorBody.sp_w_mstr(b, ErrorBody.sp_w_mstr(p, s4))))), Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, ErrorBody.sp_w_mstr(b, ErrorBody.sp_w_mstr(p, Wr.put_str(m, rr)))))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, ErrorBody.sp_w_mstr(b, ErrorBody.sp_w_mstr(p, z))))), s4, Wr.put_str(m, rr), eq)), LBool.cb_and_intro(ErrorBody.sp_fit_mstr(st), Bool.and(ErrorBody.sp_fit_mstr(b), Bool.and(ErrorBody.sp_fit_mstr(p), LawsBase.wire_fits(String.length(m)))), fst, LBool.cb_and_intro(ErrorBody.sp_fit_mstr(b), Bool.and(ErrorBody.sp_fit_mstr(p), LawsBase.wire_fits(String.length(m))), fb, LBool.cb_and_intro(ErrorBody.sp_fit_mstr(p), LawsBase.wire_fits(String.length(m)), fp, fm))))
    case Wr.Bad{}:
      Unit{}

def ebx.show.p(-s: String, +c: Bool, +st: Maybe<&2, String>, +b: Maybe<&2, String>, +s3: String, pre: {s == Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, ErrorBody.sp_w_mstr(b, s3)))) : String}, fst: {ErrorBody.sp_fit_mstr(st) == True{} : Bool}, fb: {ErrorBody.sp_fit_mstr(b) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, String>>, pp: ebx.MSP(s3, dd)) -> ebx.RP(s, FEb.get_show.p(c, st, b, dd)):
  match dd:
    case Wr.Got{+p, +rr}:
      (eq, fp) = pp
      ebx.show.m(s, c, st, b, p, rr, Equal.trans(String, s, Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, ErrorBody.sp_w_mstr(b, s3)))), Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, ErrorBody.sp_w_mstr(b, ErrorBody.sp_w_mstr(p, rr))))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, ErrorBody.sp_w_mstr(b, z)))), s3, ErrorBody.sp_w_mstr(p, rr), eq)), fst, fb, fp, Wr.get_str(rr), LE.dcw.str(rr))
    case Wr.Bad{}:
      Unit{}

def ebx.show.b(-s: String, +c: Bool, +st: Maybe<&2, String>, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, s2))) : String}, fst: {ErrorBody.sp_fit_mstr(st) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, String>>, pp: ebx.MSP(s2, dd)) -> ebx.RP(s, FEb.get_show.b(c, st, dd)):
  match dd:
    case Wr.Got{+b, +rr}:
      (eq, fb) = pp
      ebx.show.p(s, c, st, b, rr, Equal.trans(String, s, Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, s2))), Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, ErrorBody.sp_w_mstr(b, rr)))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, z))), s2, ErrorBody.sp_w_mstr(b, rr), eq)), fst, fb, FEb.get_mstr(rr), ebx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def ebx.show.st(-s: String, +c: Bool, +s1: String, pre: {s == Wr.put_nat(1n, Wr.put_bool(c, s1)) : String}, dd: Wr.Dec<Maybe<&2, String>>, pp: ebx.MSP(s1, dd)) -> ebx.RP(s, FEb.get_show.st(c, dd)):
  match dd:
    case Wr.Got{+st, +rr}:
      (eq, fst) = pp
      ebx.show.b(s, c, st, rr, Equal.trans(String, s, Wr.put_nat(1n, Wr.put_bool(c, s1)), Wr.put_nat(1n, Wr.put_bool(c, ErrorBody.sp_w_mstr(st, rr))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_bool(c, z)), s1, ErrorBody.sp_w_mstr(st, rr), eq)), fst, FEb.get_mstr(rr), ebx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def ebx.show.c(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, dd: Wr.Dec<Bool>, ed: {Wr.get_bool(s0) == dd : Wr.Dec<Bool>}) -> ebx.RP(s, FEb.get_show(dd)):
  match dd:
    case Wr.Got{+c, +rr}:
      +ee = ed
      ebx.show.st(s, c, rr, Equal.trans(String, s, Wr.put_nat(1n, s0), Wr.put_nat(1n, Wr.put_bool(c, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s0, Wr.put_bool(c, rr), Wire.wire_bool_exact(s0, c, rr, ee))), FEb.get_mstr(rr), ebx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

# the cut question
def ebx.cut.max(-s: String, +t: String, +s1: String, pre: {s == Wr.put_nat(2n, Wr.put_str(t, s1)) : String}, ft: {LawsBase.wire_fits(String.length(t)) == True{} : Bool}, dd: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == dd : Wr.Dec<Nat>}) -> ebx.RP(s, FEb.get_cut.max(t, dd)):
  match dd:
    case Wr.Got{+n, +rr}:
      +ee = ed
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(t, s1)), Wr.put_nat(2n, Wr.put_str(t, Wr.put_nat(n, rr))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(t, z)), s1, Wr.put_nat(n, rr), Wire.wire_nat_exact(s1, n, rr, ee))), LBool.cb_and_intro(LawsBase.wire_fits(String.length(t)), LawsBase.wire_fits(n), ft, Wire.wire_nat_decoded_fits(s1, n, rr, ee)))
    case Wr.Bad{}:
      Unit{}

def ebx.cut.t(-s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, dd: Wr.Dec<String>, pp: LE.dcw.SP(s0, dd)) -> ebx.RP(s, FEb.get_cut(dd)):
  match dd:
    case Wr.Got{+t, +rr}:
      (eq, ft) = pp
      ebx.cut.max(s, t, rr, Equal.trans(String, s, Wr.put_nat(2n, s0), Wr.put_nat(2n, Wr.put_str(t, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s0, Wr.put_str(t, rr), eq)), ft, Wr.get_nat(rr), {==})
    case Wr.Bad{}:
      Unit{}

def ebx.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ebx.RP(s, FEb.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          ebx.body.b(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FEb.get_probe(s0), ebx.probe(s0))
        case 1n:
          ebx.show.c(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_bool(s0), {==})
        case 2n:
          ebx.cut.t(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_str(s0), LE.dcw.str(s0))
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def ebx.top(-s: String, d: Wr.Dec<FEb.Req>, rp: ebx.RP(s, d), ok: {LawsBase.wire_opens_err(FEb.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FEb.Req, r => {s == ErrorBody.sp_w_req(r, "") : String} & {ErrorBody.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FEb.Req, r2 => {s == ErrorBody.sp_w_req(r2, "") : String} & {ErrorBody.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FEb.Req, r2 => {s == ErrorBody.sp_w_req(r2, "") : String} & {ErrorBody.sp_fit_req(r2) == True{} : Bool}>, ok)

def ErrorBody.error_body_entry_exact(s, ok):
  ebx.top(s, FEb.get_req(s), ebx.tag(s, Wr.get_nat(s), {==}), ok)
