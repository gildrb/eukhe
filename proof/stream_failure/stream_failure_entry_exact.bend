# eukhe: the proof of LAW stream_failure_entry_exact
#
# PROOF: each decoder stage of bend/ffi_stream_failure.bend answers Got{x,
# rest} only for an input that is the spec's spelling of what it read so
# far before rest, every number and length within the wire (sfx.*: per
# field kind a predicate on its decoder's answer: wire_nat_exact and
# wire_nat_decoded_fits, the string lemmas of LE.dcw.str, and sfx.mstr,
# sfx.mnat, sfx.cause, sfx.block built from them; each stage carries `pre`,
# the input spelled up to its field). The entry answers a value only for a
# request read whole with nothing left: that input is the spelled request
# (sfx.top).

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/stream_failure.bend as Sf
import ../../bend/ffi_stream_failure.bend as FSf
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as OverflowLaws
import ../../laws/stream_failure.bend as StreamFailure
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LE

def sfx.RP(s: String, d: Wr.Dec<FSf.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == StreamFailure.sp_w_req(q, r) : String} & {StreamFailure.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# Maybe<String>
def sfx.MSP(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == StreamFailure.sp_w_mstr(m, r) : String} & {StreamFailure.sp_fit_mstr(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sfx.mstr.of(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> sfx.MSP(s, FSf.get_mstr.of(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = sp
      (LE.dcw.after(s, 1n, s1, Wr.put_str(x, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def sfx.mstr.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sfx.MSP(s, FSf.get_mstr.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, ed), {==})
        case 1n:
          sfx.mstr.of(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_str(s1), LE.dcw.str(s1))
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def sfx.mstr(+s: String) -> sfx.MSP(s, FSf.get_mstr(s)):
  sfx.mstr.at(s, Wr.get_nat(s), {==})

# Maybe<Nat>
def sfx.MNP(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == StreamFailure.sp_w_mnat(m, r) : String} & {StreamFailure.sp_fit_mnat(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sfx.mnat.of(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> sfx.MNP(s, FSf.get_mnat.of(d)):
  match d:
    case Wr.Got{+x, +r}:
      +e = ed
      (LE.dcw.after(s, 1n, s1, Wr.put_nat(x, r), pre, Wire.wire_nat_exact(s1, x, r, e)), Wire.wire_nat_decoded_fits(s1, x, r, e))
    case Wr.Bad{}:
      Unit{}

def sfx.mnat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sfx.MNP(s, FSf.get_mnat.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, ed), {==})
        case 1n:
          sfx.mnat.of(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_nat(s1), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def sfx.mnat(+s: String) -> sfx.MNP(s, FSf.get_mnat(s)):
  sfx.mnat.at(s, Wr.get_nat(s), {==})

# a cause
def sfx.CP(s: String, d: Wr.Dec<Sf.Cause>) -> Type:
  match d:
    case Wr.Got{k, r}:
      {s == StreamFailure.sp_w_cause(k, r) : String}
    case Wr.Bad{}:
      Unit

def sfx.cause.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sfx.CP(s, FSf.get_cause.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s1, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s1, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s1, ed)
        case 3n:
          Wire.wire_nat_exact(s, 3n, s1, ed)
        case 4n:
          Wire.wire_nat_exact(s, 4n, s1, ed)
        case 5n:
          Wire.wire_nat_exact(s, 5n, s1, ed)
        case 6n:
          Wire.wire_nat_exact(s, 6n, s1, ed)
        case 7n:
          Wire.wire_nat_exact(s, 7n, s1, ed)
        case 8n:
          Wire.wire_nat_exact(s, 8n, s1, ed)
        case 9n:
          Wire.wire_nat_exact(s, 9n, s1, ed)
        case 10n:
          Wire.wire_nat_exact(s, 10n, s1, ed)
        case 11n:
          Wire.wire_nat_exact(s, 11n, s1, ed)
        case 12n:
          Wire.wire_nat_exact(s, 12n, s1, ed)
        case 13n:
          Wire.wire_nat_exact(s, 13n, s1, ed)
        case 14n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def sfx.cause(+s: String) -> sfx.CP(s, FSf.get_cause(s)):
  sfx.cause.at(s, Wr.get_nat(s), {==})

# a block
def sfx.BP(s: String, d: Wr.Dec<Sf.Block>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == StreamFailure.sp_w_block(b, r) : String}
    case Wr.Bad{}:
      Unit

def sfx.block.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sfx.BP(s, FSf.get_block.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s1, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s1, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s1, ed)
        case 3n:
          Wire.wire_nat_exact(s, 3n, s1, ed)
        case 4n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def sfx.block(+s: String) -> sfx.BP(s, FSf.get_block(s)):
  sfx.block.at(s, Wr.get_nat(s), {==})

def sfx.classify.st(-s: String, +t: Maybe<&2, String>, +s1: String, pre: {s == Wr.put_nat(0n, StreamFailure.sp_w_mstr(t, s1)) : String}, ft: {StreamFailure.sp_fit_mstr(t) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, Nat>>, pp: sfx.MNP(s1, dd)) -> sfx.RP(s, FSf.get_classify.st(t, dd)):
  match dd:
    case Wr.Got{+st, +rr}:
      (e, fst) = pp
      (Equal.trans(String, s, Wr.put_nat(0n, StreamFailure.sp_w_mstr(t, s1)), Wr.put_nat(0n, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, rr))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, StreamFailure.sp_w_mstr(t, z)), s1, StreamFailure.sp_w_mnat(st, rr), e)), LBool.cb_and_intro(StreamFailure.sp_fit_mstr(t), StreamFailure.sp_fit_mnat(st), ft, fst))
    case Wr.Bad{}:
      Unit{}


def sfx.classify.t(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s0, dd)) -> sfx.RP(s, FSf.get_classify.t(dd)):
  match dd:
    case Wr.Got{+t, +rr}:
      (e, ft) = pp
      sfx.classify.st(s, t, rr, Equal.trans(String, s, Wr.put_nat(0n, s0), Wr.put_nat(0n, StreamFailure.sp_w_mstr(t, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s0, StreamFailure.sp_w_mstr(t, rr), e)), ft, FSf.get_mnat(rr), sfx.mnat(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.message.r(-s: String, +k: Sf.Cause, +t: Maybe<&2, String>, +st: Maybe<&2, Nat>, +d: Maybe<&2, String>, +s4: String, pre: {s == Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(d, s4))))) : String}, ft: {StreamFailure.sp_fit_mstr(t) == True{} : Bool}, fst: {StreamFailure.sp_fit_mnat(st) == True{} : Bool}, fd: {StreamFailure.sp_fit_mstr(d) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s4, dd)) -> sfx.RP(s, FSf.get_message.r(k, t, st, d, dd)):
  match dd:
    case Wr.Got{+r, +rr}:
      (e, fr) = pp
      (Equal.trans(String, s, Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(d, s4))))), Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(r, rr)))))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(d, z))))), s4, StreamFailure.sp_w_mstr(r, rr), e)), LBool.cb_and_intro(StreamFailure.sp_fit_mstr(t), Bool.and(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(d), StreamFailure.sp_fit_mstr(r))), ft, LBool.cb_and_intro(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(d), StreamFailure.sp_fit_mstr(r)), fst, LBool.cb_and_intro(StreamFailure.sp_fit_mstr(d), StreamFailure.sp_fit_mstr(r), fd, fr))))
    case Wr.Bad{}:
      Unit{}


def sfx.message.d(-s: String, +k: Sf.Cause, +t: Maybe<&2, String>, +st: Maybe<&2, Nat>, +s3: String, pre: {s == Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, s3)))) : String}, ft: {StreamFailure.sp_fit_mstr(t) == True{} : Bool}, fst: {StreamFailure.sp_fit_mnat(st) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s3, dd)) -> sfx.RP(s, FSf.get_message.d(k, t, st, dd)):
  match dd:
    case Wr.Got{+d, +rr}:
      (e, fd) = pp
      sfx.message.r(s, k, t, st, d, rr, Equal.trans(String, s, Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, s3)))), Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(d, rr))))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, z)))), s3, StreamFailure.sp_w_mstr(d, rr), e)), ft, fst, fd, FSf.get_mstr(rr), sfx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.message.st(-s: String, +k: Sf.Cause, +t: Maybe<&2, String>, +s2: String, pre: {s == Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, s2))) : String}, ft: {StreamFailure.sp_fit_mstr(t) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, Nat>>, pp: sfx.MNP(s2, dd)) -> sfx.RP(s, FSf.get_message.st(k, t, dd)):
  match dd:
    case Wr.Got{+st, +rr}:
      (e, fst) = pp
      sfx.message.d(s, k, t, st, rr, Equal.trans(String, s, Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, s2))), Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, rr)))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, z))), s2, StreamFailure.sp_w_mnat(st, rr), e)), ft, fst, FSf.get_mstr(rr), sfx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.message.t(-s: String, +k: Sf.Cause, +s1: String, pre: {s == Wr.put_nat(1n, StreamFailure.sp_w_cause(k, s1)) : String}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s1, dd)) -> sfx.RP(s, FSf.get_message.t(k, dd)):
  match dd:
    case Wr.Got{+t, +rr}:
      (e, ft) = pp
      sfx.message.st(s, k, t, rr, Equal.trans(String, s, Wr.put_nat(1n, StreamFailure.sp_w_cause(k, s1)), Wr.put_nat(1n, StreamFailure.sp_w_cause(k, StreamFailure.sp_w_mstr(t, rr))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, StreamFailure.sp_w_cause(k, z)), s1, StreamFailure.sp_w_mstr(t, rr), e)), ft, FSf.get_mnat(rr), sfx.mnat(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.message.k(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, dd: Wr.Dec<Sf.Cause>, pp: sfx.CP(s0, dd)) -> sfx.RP(s, FSf.get_message.k(dd)):
  match dd:
    case Wr.Got{+k, +rr}:
      e = pp
      sfx.message.t(s, k, rr, Equal.trans(String, s, Wr.put_nat(1n, s0), Wr.put_nat(1n, StreamFailure.sp_w_cause(k, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s0, StreamFailure.sp_w_cause(k, rr), e)), FSf.get_mstr(rr), sfx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.http.r(-s: String, +m: String, +st: Maybe<&2, Nat>, +bt: Maybe<&2, String>, +d: Maybe<&2, String>, +code: Maybe<&2, String>, +sdk: Maybe<&2, String>, +s6: String, pre: {s == Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, StreamFailure.sp_w_mstr(sdk, s6))))))) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, fst: {StreamFailure.sp_fit_mnat(st) == True{} : Bool}, fbt: {StreamFailure.sp_fit_mstr(bt) == True{} : Bool}, fd: {StreamFailure.sp_fit_mstr(d) == True{} : Bool}, fcode: {StreamFailure.sp_fit_mstr(code) == True{} : Bool}, fsdk: {StreamFailure.sp_fit_mstr(sdk) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s6, dd)) -> sfx.RP(s, FSf.get_http.r(m, st, bt, d, code, sdk, dd)):
  match dd:
    case Wr.Got{+r, +rr}:
      (e, fr) = pp
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, StreamFailure.sp_w_mstr(sdk, s6))))))), Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, StreamFailure.sp_w_mstr(sdk, StreamFailure.sp_w_mstr(r, rr)))))))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, StreamFailure.sp_w_mstr(sdk, z))))))), s6, StreamFailure.sp_w_mstr(r, rr), e)), LBool.cb_and_intro(LawsBase.wire_fits(String.length(m)), Bool.and(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(bt), Bool.and(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r)))))), fm, LBool.cb_and_intro(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(bt), Bool.and(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r))))), fst, LBool.cb_and_intro(StreamFailure.sp_fit_mstr(bt), Bool.and(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r)))), fbt, LBool.cb_and_intro(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r))), fd, LBool.cb_and_intro(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r)), fcode, LBool.cb_and_intro(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r), fsdk, fr)))))))
    case Wr.Bad{}:
      Unit{}


def sfx.http.sdk(-s: String, +m: String, +st: Maybe<&2, Nat>, +bt: Maybe<&2, String>, +d: Maybe<&2, String>, +code: Maybe<&2, String>, +s5: String, pre: {s == Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, s5)))))) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, fst: {StreamFailure.sp_fit_mnat(st) == True{} : Bool}, fbt: {StreamFailure.sp_fit_mstr(bt) == True{} : Bool}, fd: {StreamFailure.sp_fit_mstr(d) == True{} : Bool}, fcode: {StreamFailure.sp_fit_mstr(code) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s5, dd)) -> sfx.RP(s, FSf.get_http.sdk(m, st, bt, d, code, dd)):
  match dd:
    case Wr.Got{+sdk, +rr}:
      (e, fsdk) = pp
      sfx.http.r(s, m, st, bt, d, code, sdk, rr, Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, s5)))))), Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, StreamFailure.sp_w_mstr(sdk, rr))))))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, z)))))), s5, StreamFailure.sp_w_mstr(sdk, rr), e)), fm, fst, fbt, fd, fcode, fsdk, FSf.get_mstr(rr), sfx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.http.code(-s: String, +m: String, +st: Maybe<&2, Nat>, +bt: Maybe<&2, String>, +d: Maybe<&2, String>, +s4: String, pre: {s == Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, s4))))) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, fst: {StreamFailure.sp_fit_mnat(st) == True{} : Bool}, fbt: {StreamFailure.sp_fit_mstr(bt) == True{} : Bool}, fd: {StreamFailure.sp_fit_mstr(d) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s4, dd)) -> sfx.RP(s, FSf.get_http.code(m, st, bt, d, dd)):
  match dd:
    case Wr.Got{+code, +rr}:
      (e, fcode) = pp
      sfx.http.sdk(s, m, st, bt, d, code, rr, Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, s4))))), Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, rr)))))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, z))))), s4, StreamFailure.sp_w_mstr(code, rr), e)), fm, fst, fbt, fd, fcode, FSf.get_mstr(rr), sfx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.http.d(-s: String, +m: String, +st: Maybe<&2, Nat>, +bt: Maybe<&2, String>, +s3: String, pre: {s == Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, s3)))) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, fst: {StreamFailure.sp_fit_mnat(st) == True{} : Bool}, fbt: {StreamFailure.sp_fit_mstr(bt) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s3, dd)) -> sfx.RP(s, FSf.get_http.d(m, st, bt, dd)):
  match dd:
    case Wr.Got{+d, +rr}:
      (e, fd) = pp
      sfx.http.code(s, m, st, bt, d, rr, Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, s3)))), Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, rr))))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, z)))), s3, StreamFailure.sp_w_mstr(d, rr), e)), fm, fst, fbt, fd, FSf.get_mstr(rr), sfx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.http.bt(-s: String, +m: String, +st: Maybe<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, s2))) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, fst: {StreamFailure.sp_fit_mnat(st) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s2, dd)) -> sfx.RP(s, FSf.get_http.bt(m, st, dd)):
  match dd:
    case Wr.Got{+bt, +rr}:
      (e, fbt) = pp
      sfx.http.d(s, m, st, bt, rr, Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, s2))), Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, rr)))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, z))), s2, StreamFailure.sp_w_mstr(bt, rr), e)), fm, fst, fbt, FSf.get_mstr(rr), sfx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.http.st(-s: String, +m: String, +s1: String, pre: {s == Wr.put_nat(2n, Wr.put_str(m, s1)) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, Nat>>, pp: sfx.MNP(s1, dd)) -> sfx.RP(s, FSf.get_http.st(m, dd)):
  match dd:
    case Wr.Got{+st, +rr}:
      (e, fst) = pp
      sfx.http.bt(s, m, st, rr, Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(m, s1)), Wr.put_nat(2n, Wr.put_str(m, StreamFailure.sp_w_mnat(st, rr))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(m, z)), s1, StreamFailure.sp_w_mnat(st, rr), e)), fm, fst, FSf.get_mstr(rr), sfx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.http.m(-s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, dd: Wr.Dec<String>, pp: LE.dcw.SP(s0, dd)) -> sfx.RP(s, FSf.get_http.m(dd)):
  match dd:
    case Wr.Got{+m, +rr}:
      (e, fm) = pp
      sfx.http.st(s, m, rr, Equal.trans(String, s, Wr.put_nat(2n, s0), Wr.put_nat(2n, Wr.put_str(m, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s0, Wr.put_str(m, rr), e)), fm, FSf.get_mnat(rr), sfx.mnat(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.fromstop.r(-s: String, +raw: Maybe<&2, String>, +s1: String, pre: {s == Wr.put_nat(3n, StreamFailure.sp_w_mstr(raw, s1)) : String}, fraw: {StreamFailure.sp_fit_mstr(raw) == True{} : Bool}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s1, dd)) -> sfx.RP(s, FSf.get_fromstop.r(raw, dd)):
  match dd:
    case Wr.Got{+r, +rr}:
      (e, fr) = pp
      (Equal.trans(String, s, Wr.put_nat(3n, StreamFailure.sp_w_mstr(raw, s1)), Wr.put_nat(3n, StreamFailure.sp_w_mstr(raw, StreamFailure.sp_w_mstr(r, rr))), pre, Equal.cong(String, String, z => Wr.put_nat(3n, StreamFailure.sp_w_mstr(raw, z)), s1, StreamFailure.sp_w_mstr(r, rr), e)), LBool.cb_and_intro(StreamFailure.sp_fit_mstr(raw), StreamFailure.sp_fit_mstr(r), fraw, fr))
    case Wr.Bad{}:
      Unit{}


def sfx.fromstop.raw(-s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, dd: Wr.Dec<Maybe<&2, String>>, pp: sfx.MSP(s0, dd)) -> sfx.RP(s, FSf.get_fromstop.raw(dd)):
  match dd:
    case Wr.Got{+raw, +rr}:
      (e, fraw) = pp
      sfx.fromstop.r(s, raw, rr, Equal.trans(String, s, Wr.put_nat(3n, s0), Wr.put_nat(3n, StreamFailure.sp_w_mstr(raw, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(3n, z), s0, StreamFailure.sp_w_mstr(raw, rr), e)), fraw, FSf.get_mstr(rr), sfx.mstr(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.drop.b(-s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, dd: Wr.Dec<Sf.Block>, pp: sfx.BP(s0, dd)) -> sfx.RP(s, FSf.get_drop.b(dd)):
  match dd:
    case Wr.Got{+b, +rr}:
      e = pp
      (Equal.trans(String, s, Wr.put_nat(4n, s0), Wr.put_nat(4n, StreamFailure.sp_w_block(b, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(4n, z), s0, StreamFailure.sp_w_block(b, rr), e)), {==})
    case Wr.Bad{}:
      Unit{}


def sfx.stalled.ms(-s: String, +s0: String, pre: {s == Wr.put_nat(5n, s0) : String}, dd: Wr.Dec<String>, pp: LE.dcw.SP(s0, dd)) -> sfx.RP(s, FSf.get_stalled.ms(dd)):
  match dd:
    case Wr.Got{+ms, +rr}:
      (e, fms) = pp
      (Equal.trans(String, s, Wr.put_nat(5n, s0), Wr.put_nat(5n, Wr.put_str(ms, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(5n, z), s0, Wr.put_str(ms, rr), e)), fms)
    case Wr.Bad{}:
      Unit{}


def sfx.shown.line(-s: String, +s0: String, pre: {s == Wr.put_nat(6n, s0) : String}, dd: Wr.Dec<String>, pp: LE.dcw.SP(s0, dd)) -> sfx.RP(s, FSf.get_shown.line(dd)):
  match dd:
    case Wr.Got{+line, +rr}:
      (e, fline) = pp
      (Equal.trans(String, s, Wr.put_nat(6n, s0), Wr.put_nat(6n, Wr.put_str(line, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(6n, z), s0, Wr.put_str(line, rr), e)), fline)
    case Wr.Bad{}:
      Unit{}


def sfx.repeating.q(-s: String, +limit: Nat, +period: Nat, +s2: String, pre: {s == Wr.put_nat(7n, Wr.put_nat(limit, Wr.put_nat(period, s2))) : String}, flimit: {LawsBase.wire_fits(limit) == True{} : Bool}, fperiod: {LawsBase.wire_fits(period) == True{} : Bool}, dd: Wr.Dec<String>, pp: LE.dcw.SP(s2, dd)) -> sfx.RP(s, FSf.get_repeating.q(limit, period, dd)):
  match dd:
    case Wr.Got{+q, +rr}:
      (e, fq) = pp
      (Equal.trans(String, s, Wr.put_nat(7n, Wr.put_nat(limit, Wr.put_nat(period, s2))), Wr.put_nat(7n, Wr.put_nat(limit, Wr.put_nat(period, Wr.put_str(q, rr)))), pre, Equal.cong(String, String, z => Wr.put_nat(7n, Wr.put_nat(limit, Wr.put_nat(period, z))), s2, Wr.put_str(q, rr), e)), LBool.cb_and_intro(LawsBase.wire_fits(limit), Bool.and(LawsBase.wire_fits(period), LawsBase.wire_fits(String.length(q))), flimit, LBool.cb_and_intro(LawsBase.wire_fits(period), LawsBase.wire_fits(String.length(q)), fperiod, fq)))
    case Wr.Bad{}:
      Unit{}


def sfx.repeating.period(-s: String, +limit: Nat, +s1: String, pre: {s == Wr.put_nat(7n, Wr.put_nat(limit, s1)) : String}, flimit: {LawsBase.wire_fits(limit) == True{} : Bool}, dd: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == dd : Wr.Dec<Nat>}) -> sfx.RP(s, FSf.get_repeating.period(limit, dd)):
  match dd:
    case Wr.Got{+period, +rr}:
      +ee = ed
      +e = Wire.wire_nat_exact(s1, period, rr, ee)
      +fperiod = Wire.wire_nat_decoded_fits(s1, period, rr, ee)
      sfx.repeating.q(s, limit, period, rr, Equal.trans(String, s, Wr.put_nat(7n, Wr.put_nat(limit, s1)), Wr.put_nat(7n, Wr.put_nat(limit, Wr.put_nat(period, rr))), pre, Equal.cong(String, String, z => Wr.put_nat(7n, Wr.put_nat(limit, z)), s1, Wr.put_nat(period, rr), e)), flimit, fperiod, Wr.get_str(rr), LE.dcw.str(rr))
    case Wr.Bad{}:
      Unit{}

def sfx.repeating.limit(-s: String, +s0: String, pre: {s == Wr.put_nat(7n, s0) : String}, dd: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == dd : Wr.Dec<Nat>}) -> sfx.RP(s, FSf.get_repeating.limit(dd)):
  match dd:
    case Wr.Got{+limit, +rr}:
      +ee = ed
      +e = Wire.wire_nat_exact(s0, limit, rr, ee)
      +flimit = Wire.wire_nat_decoded_fits(s0, limit, rr, ee)
      sfx.repeating.period(s, limit, rr, Equal.trans(String, s, Wr.put_nat(7n, s0), Wr.put_nat(7n, Wr.put_nat(limit, rr)), pre, Equal.cong(String, String, z => Wr.put_nat(7n, z), s0, Wr.put_nat(limit, rr), e)), flimit, Wr.get_nat(rr), {==})
    case Wr.Bad{}:
      Unit{}

def sfx.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sfx.RP(s, FSf.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          sfx.classify.t(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FSf.get_mstr(s0), sfx.mstr(s0))
        case 1n:
          sfx.message.k(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FSf.get_cause(s0), sfx.cause(s0))
        case 2n:
          sfx.http.m(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_str(s0), LE.dcw.str(s0))
        case 3n:
          sfx.fromstop.raw(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), FSf.get_mstr(s0), sfx.mstr(s0))
        case 4n:
          sfx.drop.b(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), FSf.get_block(s0), sfx.block(s0))
        case 5n:
          sfx.stalled.ms(s, s0, Wire.wire_nat_exact(s, 5n, s0, ed), Wr.get_str(s0), LE.dcw.str(s0))
        case 6n:
          sfx.shown.line(s, s0, Wire.wire_nat_exact(s, 6n, s0, ed), Wr.get_str(s0), LE.dcw.str(s0))
        case 7n:
          sfx.repeating.limit(s, s0, Wire.wire_nat_exact(s, 7n, s0, ed), Wr.get_nat(s0), {==})
        case 8n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def sfx.top(-s: String, d: Wr.Dec<FSf.Req>, rp: sfx.RP(s, d), ok: {LawsBase.wire_opens_err(FSf.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FSf.Req, r => {s == StreamFailure.sp_w_req(r, "") : String} & {StreamFailure.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FSf.Req, r2 => {s == StreamFailure.sp_w_req(r2, "") : String} & {StreamFailure.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FSf.Req, r2 => {s == StreamFailure.sp_w_req(r2, "") : String} & {StreamFailure.sp_fit_req(r2) == True{} : Bool}>, ok)

def StreamFailure.stream_failure_entry_exact(s, ok):
  sfx.top(s, FSf.get_req(s), sfx.tag(s, Wr.get_nat(s), {==}), ok)
