# eukhe: lemmas of the refine_plan entry proofs: a decoded value is
# spelled and fits (rpx.*: a predicate per decoder answer, carried stage
# by stage with the wire exactness laws): the primitives and the edits

import Base
import ../../../bend/refine_plan.bend as Rp
import ../../../bend/ffi_refine_plan.bend as FRp
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/refine_plan/entry.bend as E
import ../../base/wire_dec.bend as LE
import ../../base/staging.bend as LStg
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool

# Primitives
# ----------

def rpx.bool.P(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Wr.put_bool(x, r) : String}
    case Wr.Bad{}:
      Unit

def rpx.bool.at(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> rpx.bool.P(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

# a Bool decoded is spelled
def rpx.bool(+s: String) -> rpx.bool.P(s, Wr.get_bool(s)):
  rpx.bool.at(s, Wr.get_bool(s), {==})

def rpx.nat.P(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Wr.put_nat(x, r) : String} & {LawsBase.wire_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rpx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rpx.nat.P(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e = ed
      (Wire.wire_nat_exact(s, n, r, e), Wire.wire_nat_decoded_fits(s, n, r, e))
    case Wr.Bad{}:
      Unit{}

# a Nat decoded is spelled, and fits
def rpx.nat(+s: String) -> rpx.nat.P(s, Wr.get_nat(s)):
  rpx.nat.at(s, Wr.get_nat(s), {==})

# Edits
# -----

def rpx.verb.P(s: String, d: Wr.Dec<Rp.Verb>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_verb(x, r) : String}
    case Wr.Bad{}:
      Unit

def rpx.verb.at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rpx.verb.P(s, FRp.get_verb.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          np
        case 1n:
          np
        case 2n:
          np
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rpx.verb(+s: String) -> rpx.verb.P(s, FRp.get_verb(s)):
  rpx.verb.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rpx.comp.P(s: String, d: Wr.Dec<Rp.Comp>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_comp(x, r) : String}
    case Wr.Bad{}:
      Unit

def rpx.comp.at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rpx.comp.P(s, FRp.get_comp.start(d)):
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
        case 5n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rpx.comp(+s: String) -> rpx.comp.P(s, FRp.get_comp(s)):
  rpx.comp.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rpx.val.P(s: String, d: Wr.Dec<Rp.Val>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_val(x, r) : String}
    case Wr.Bad{}:
      Unit

def rpx.val.at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rpx.val.P(s, FRp.get_val.start(d)):
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
        case 4n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rpx.val(+s: String) -> rpx.val.P(s, FRp.get_val(s)):
  rpx.val.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rpx.ms.P(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_ms(x, r) : String} & {E.rp_fit_ms(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rpx.ms.some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, dp: LE.dcw.SP(s1, d)) -> rpx.ms.P(s, FRp.get_ms.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = dp
      (LE.dcw.after(s, 1n, s1, Wr.put_str(x, r), pre, e), fx)
    case Wr.Bad{}:
      Unit{}

def rpx.ms.at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rpx.ms.P(s, FRp.get_ms.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (np, {==})
        case 1n:
          rpx.ms.some(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rpx.ms(+s: String) -> rpx.ms.P(s, FRp.get_ms(s)):
  rpx.ms.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rpx.pyref.P(s: String, d: Wr.Dec<Rp.Pyref>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_pyref(x, r) : String} & {E.rp_fit_pyref(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rpx.pyref.f5(-s: String, +v1: Maybe<&2, String>, +v2: Maybe<&2, String>, +v3: Maybe<&2, String>, +v4: Maybe<&2, String>, -s5: String, pre: {s == E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, s5)))) : String}, +h1: {E.rp_fit_ms(v1) == True{} : Bool}, +h2: {E.rp_fit_ms(v2) == True{} : Bool}, +h3: {E.rp_fit_ms(v3) == True{} : Bool}, +h4: {E.rp_fit_ms(v4) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, dp: rpx.ms.P(s5, d)) -> rpx.pyref.P(s, FRp.get_pyref.f5(v1, v2, v3, v4, d)):
  match d:
    case Wr.Got{+v5, +r}:
      (e1, +h5) = dp
      +pre2 = Equal.trans(String, s, E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, s5)))), E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, E.rp_w_ms(v5, r))))), pre, Equal.cong(String, String, z => E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, z)))), s5, E.rp_w_ms(v5, r), e1))
      (pre2, LBool.cb_and_intro(E.rp_fit_ms(v1), Bool.and(E.rp_fit_ms(v2), Bool.and(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_ms(v5)))), h1, LBool.cb_and_intro(E.rp_fit_ms(v2), Bool.and(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_ms(v5))), h2, LBool.cb_and_intro(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_ms(v5)), h3, LBool.cb_and_intro(E.rp_fit_ms(v4), E.rp_fit_ms(v5), h4, h5)))))
    case Wr.Bad{}:
      Unit{}

def rpx.pyref.f4(-s: String, +v1: Maybe<&2, String>, +v2: Maybe<&2, String>, +v3: Maybe<&2, String>, -s4: String, pre: {s == E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, s4))) : String}, +h1: {E.rp_fit_ms(v1) == True{} : Bool}, +h2: {E.rp_fit_ms(v2) == True{} : Bool}, +h3: {E.rp_fit_ms(v3) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, dp: rpx.ms.P(s4, d)) -> rpx.pyref.P(s, FRp.get_pyref.f4(v1, v2, v3, d)):
  match d:
    case Wr.Got{+v4, +r}:
      (e1, +h4) = dp
      +pre2 = Equal.trans(String, s, E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, s4))), E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, r)))), pre, Equal.cong(String, String, z => E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, z))), s4, E.rp_w_ms(v4, r), e1))
      rpx.pyref.f5(s, v1, v2, v3, v4, r, pre2, h1, h2, h3, h4, FRp.get_ms(r), rpx.ms(r))
    case Wr.Bad{}:
      Unit{}

def rpx.pyref.f3(-s: String, +v1: Maybe<&2, String>, +v2: Maybe<&2, String>, -s3: String, pre: {s == E.rp_w_ms(v1, E.rp_w_ms(v2, s3)) : String}, +h1: {E.rp_fit_ms(v1) == True{} : Bool}, +h2: {E.rp_fit_ms(v2) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, dp: rpx.ms.P(s3, d)) -> rpx.pyref.P(s, FRp.get_pyref.f3(v1, v2, d)):
  match d:
    case Wr.Got{+v3, +r}:
      (e1, +h3) = dp
      +pre2 = Equal.trans(String, s, E.rp_w_ms(v1, E.rp_w_ms(v2, s3)), E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, r))), pre, Equal.cong(String, String, z => E.rp_w_ms(v1, E.rp_w_ms(v2, z)), s3, E.rp_w_ms(v3, r), e1))
      rpx.pyref.f4(s, v1, v2, v3, r, pre2, h1, h2, h3, FRp.get_ms(r), rpx.ms(r))
    case Wr.Bad{}:
      Unit{}

def rpx.pyref.f2(-s: String, +v1: Maybe<&2, String>, -s2: String, pre: {s == E.rp_w_ms(v1, s2) : String}, +h1: {E.rp_fit_ms(v1) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, dp: rpx.ms.P(s2, d)) -> rpx.pyref.P(s, FRp.get_pyref.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      (e1, +h2) = dp
      +pre2 = Equal.trans(String, s, E.rp_w_ms(v1, s2), E.rp_w_ms(v1, E.rp_w_ms(v2, r)), pre, Equal.cong(String, String, z => E.rp_w_ms(v1, z), s2, E.rp_w_ms(v2, r), e1))
      rpx.pyref.f3(s, v1, v2, r, pre2, h1, h2, FRp.get_ms(r), rpx.ms(r))
    case Wr.Bad{}:
      Unit{}

def rpx.pyref.f1(-s: String, -s1: String, pre: {s == s1 : String}, d: Wr.Dec<Maybe<&2, String>>, dp: rpx.ms.P(s1, d)) -> rpx.pyref.P(s, FRp.get_pyref.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      (e1, +h1) = dp
      +pre2 = Equal.trans(String, s, s1, E.rp_w_ms(v1, r), pre, Equal.cong(String, String, z => z, s1, E.rp_w_ms(v1, r), e1))
      rpx.pyref.f2(s, v1, r, pre2, h1, FRp.get_ms(r), rpx.ms(r))
    case Wr.Bad{}:
      Unit{}

def rpx.pyref(+s: String) -> rpx.pyref.P(s, FRp.get_pyref(s)):
  rpx.pyref.f1(s, s, {==}, FRp.get_ms(s), rpx.ms(s))

def rpx.args.P(s: String, d: Wr.Dec<Rp.Args>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_args(x, r) : String}
    case Wr.Bad{}:
      Unit

def rpx.args.f2(-s: String, +v1: Rp.Val, -s2: String, pre: {s == E.rp_w_val(v1, s2) : String}, d: Wr.Dec<Rp.Val>, dp: rpx.val.P(s2, d)) -> rpx.args.P(s, FRp.get_args.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      +pre2 = Equal.trans(String, s, E.rp_w_val(v1, s2), E.rp_w_val(v1, E.rp_w_val(v2, r)), pre, Equal.cong(String, String, z => E.rp_w_val(v1, z), s2, E.rp_w_val(v2, r), dp))
      pre2
    case Wr.Bad{}:
      Unit{}

def rpx.args.f1(-s: String, -s1: String, pre: {s == s1 : String}, d: Wr.Dec<Rp.Val>, dp: rpx.val.P(s1, d)) -> rpx.args.P(s, FRp.get_args.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      +pre2 = Equal.trans(String, s, s1, E.rp_w_val(v1, r), pre, Equal.cong(String, String, z => z, s1, E.rp_w_val(v1, r), dp))
      rpx.args.f2(s, v1, r, pre2, FRp.get_val(r), rpx.val(r))
    case Wr.Bad{}:
      Unit{}

def rpx.args(+s: String) -> rpx.args.P(s, FRp.get_args(s)):
  rpx.args.f1(s, s, {==}, FRp.get_val(s), rpx.val(s))

def rpx.mverb.P(s: String, d: Wr.Dec<Maybe<&2, Rp.Verb>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_mverb(x, r) : String}
    case Wr.Bad{}:
      Unit

def rpx.mverb.some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Rp.Verb>, dp: rpx.verb.P(s1, d)) -> rpx.mverb.P(s, FRp.get_mverb.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      LE.dcw.after(s, 1n, s1, E.rp_w_verb(x, r), pre, dp)
    case Wr.Bad{}:
      Unit{}

def rpx.mverb.at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rpx.mverb.P(s, FRp.get_mverb.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          np
        case 1n:
          rpx.mverb.some(s, s1, np, FRp.get_verb(s1), rpx.verb(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rpx.mverb(+s: String) -> rpx.mverb.P(s, FRp.get_mverb(s)):
  rpx.mverb.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rpx.mcomp.P(s: String, d: Wr.Dec<Maybe<&2, Rp.Comp>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_mcomp(x, r) : String}
    case Wr.Bad{}:
      Unit

def rpx.mcomp.some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Rp.Comp>, dp: rpx.comp.P(s1, d)) -> rpx.mcomp.P(s, FRp.get_mcomp.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      LE.dcw.after(s, 1n, s1, E.rp_w_comp(x, r), pre, dp)
    case Wr.Bad{}:
      Unit{}

def rpx.mcomp.at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rpx.mcomp.P(s, FRp.get_mcomp.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          np
        case 1n:
          rpx.mcomp.some(s, s1, np, FRp.get_comp(s1), rpx.comp(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rpx.mcomp(+s: String) -> rpx.mcomp.P(s, FRp.get_mcomp(s)):
  rpx.mcomp.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rpx.mpyref.P(s: String, d: Wr.Dec<Maybe<&2, Rp.Pyref>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_mpyref(x, r) : String} & {E.rp_fit_mpyref(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rpx.mpyref.some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Rp.Pyref>, dp: rpx.pyref.P(s1, d)) -> rpx.mpyref.P(s, FRp.get_mpyref.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = dp
      (LE.dcw.after(s, 1n, s1, E.rp_w_pyref(x, r), pre, e), fx)
    case Wr.Bad{}:
      Unit{}

def rpx.mpyref.at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rpx.mpyref.P(s, FRp.get_mpyref.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (np, {==})
        case 1n:
          rpx.mpyref.some(s, s1, np, FRp.get_pyref(s1), rpx.pyref(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rpx.mpyref(+s: String) -> rpx.mpyref.P(s, FRp.get_mpyref(s)):
  rpx.mpyref.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rpx.margs.P(s: String, d: Wr.Dec<Maybe<&2, Rp.Args>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_margs(x, r) : String}
    case Wr.Bad{}:
      Unit

def rpx.margs.some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Rp.Args>, dp: rpx.args.P(s1, d)) -> rpx.margs.P(s, FRp.get_margs.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      LE.dcw.after(s, 1n, s1, E.rp_w_args(x, r), pre, dp)
    case Wr.Bad{}:
      Unit{}

def rpx.margs.at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rpx.margs.P(s, FRp.get_margs.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          np
        case 1n:
          rpx.margs.some(s, s1, np, FRp.get_args(s1), rpx.args(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rpx.margs(+s: String) -> rpx.margs.P(s, FRp.get_margs(s)):
  rpx.margs.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rpx.ed.P(s: String, d: Wr.Dec<Rp.Ed>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_ed(x, r) : String} & {E.rp_fit_ed(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rpx.ed.f10(-s: String, +v1: Maybe<&2, Rp.Verb>, +v2: Maybe<&2, Rp.Comp>, +v3: Maybe<&2, String>, +v4: Maybe<&2, String>, +v5: Bool, +v6: Maybe<&2, Rp.Pyref>, +v7: Maybe<&2, Rp.Args>, +v8: Bool, +v9: Bool, -s10: String, pre: {s == E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, s10))))))))) : String}, +h3: {E.rp_fit_ms(v3) == True{} : Bool}, +h4: {E.rp_fit_ms(v4) == True{} : Bool}, +h6: {E.rp_fit_mpyref(v6) == True{} : Bool}, d: Wr.Dec<Bool>, dp: rpx.bool.P(s10, d)) -> rpx.ed.P(s, FRp.get_ed.f10(v1, v2, v3, v4, v5, v6, v7, v8, v9, d)):
  match d:
    case Wr.Got{+v10, +r}:
      +pre2 = Equal.trans(String, s, E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, s10))))))))), E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, r)))))))))), pre, Equal.cong(String, String, z => E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, z))))))))), s10, Wr.put_bool(v10, r), dp))
      (pre2, LBool.cb_and_intro(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_mpyref(v6)), h3, LBool.cb_and_intro(E.rp_fit_ms(v4), E.rp_fit_mpyref(v6), h4, h6)))
    case Wr.Bad{}:
      Unit{}

def rpx.ed.f9(-s: String, +v1: Maybe<&2, Rp.Verb>, +v2: Maybe<&2, Rp.Comp>, +v3: Maybe<&2, String>, +v4: Maybe<&2, String>, +v5: Bool, +v6: Maybe<&2, Rp.Pyref>, +v7: Maybe<&2, Rp.Args>, +v8: Bool, -s9: String, pre: {s == E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, s9)))))))) : String}, +h3: {E.rp_fit_ms(v3) == True{} : Bool}, +h4: {E.rp_fit_ms(v4) == True{} : Bool}, +h6: {E.rp_fit_mpyref(v6) == True{} : Bool}, d: Wr.Dec<Bool>, dp: rpx.bool.P(s9, d)) -> rpx.ed.P(s, FRp.get_ed.f9(v1, v2, v3, v4, v5, v6, v7, v8, d)):
  match d:
    case Wr.Got{+v9, +r}:
      +pre2 = Equal.trans(String, s, E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, s9)))))))), E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, r))))))))), pre, Equal.cong(String, String, z => E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, z)))))))), s9, Wr.put_bool(v9, r), dp))
      rpx.ed.f10(s, v1, v2, v3, v4, v5, v6, v7, v8, v9, r, pre2, h3, h4, h6, Wr.get_bool(r), rpx.bool(r))
    case Wr.Bad{}:
      Unit{}

def rpx.ed.f8(-s: String, +v1: Maybe<&2, Rp.Verb>, +v2: Maybe<&2, Rp.Comp>, +v3: Maybe<&2, String>, +v4: Maybe<&2, String>, +v5: Bool, +v6: Maybe<&2, Rp.Pyref>, +v7: Maybe<&2, Rp.Args>, -s8: String, pre: {s == E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, s8))))))) : String}, +h3: {E.rp_fit_ms(v3) == True{} : Bool}, +h4: {E.rp_fit_ms(v4) == True{} : Bool}, +h6: {E.rp_fit_mpyref(v6) == True{} : Bool}, d: Wr.Dec<Bool>, dp: rpx.bool.P(s8, d)) -> rpx.ed.P(s, FRp.get_ed.f8(v1, v2, v3, v4, v5, v6, v7, d)):
  match d:
    case Wr.Got{+v8, +r}:
      +pre2 = Equal.trans(String, s, E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, s8))))))), E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, r)))))))), pre, Equal.cong(String, String, z => E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, z))))))), s8, Wr.put_bool(v8, r), dp))
      rpx.ed.f9(s, v1, v2, v3, v4, v5, v6, v7, v8, r, pre2, h3, h4, h6, Wr.get_bool(r), rpx.bool(r))
    case Wr.Bad{}:
      Unit{}

def rpx.ed.f7(-s: String, +v1: Maybe<&2, Rp.Verb>, +v2: Maybe<&2, Rp.Comp>, +v3: Maybe<&2, String>, +v4: Maybe<&2, String>, +v5: Bool, +v6: Maybe<&2, Rp.Pyref>, -s7: String, pre: {s == E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, s7)))))) : String}, +h3: {E.rp_fit_ms(v3) == True{} : Bool}, +h4: {E.rp_fit_ms(v4) == True{} : Bool}, +h6: {E.rp_fit_mpyref(v6) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Rp.Args>>, dp: rpx.margs.P(s7, d)) -> rpx.ed.P(s, FRp.get_ed.f7(v1, v2, v3, v4, v5, v6, d)):
  match d:
    case Wr.Got{+v7, +r}:
      +pre2 = Equal.trans(String, s, E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, s7)))))), E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, r))))))), pre, Equal.cong(String, String, z => E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, z)))))), s7, E.rp_w_margs(v7, r), dp))
      rpx.ed.f8(s, v1, v2, v3, v4, v5, v6, v7, r, pre2, h3, h4, h6, Wr.get_bool(r), rpx.bool(r))
    case Wr.Bad{}:
      Unit{}

def rpx.ed.f6(-s: String, +v1: Maybe<&2, Rp.Verb>, +v2: Maybe<&2, Rp.Comp>, +v3: Maybe<&2, String>, +v4: Maybe<&2, String>, +v5: Bool, -s6: String, pre: {s == E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, s6))))) : String}, +h3: {E.rp_fit_ms(v3) == True{} : Bool}, +h4: {E.rp_fit_ms(v4) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Rp.Pyref>>, dp: rpx.mpyref.P(s6, d)) -> rpx.ed.P(s, FRp.get_ed.f6(v1, v2, v3, v4, v5, d)):
  match d:
    case Wr.Got{+v6, +r}:
      (e1, +h6) = dp
      +pre2 = Equal.trans(String, s, E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, s6))))), E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, r)))))), pre, Equal.cong(String, String, z => E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, z))))), s6, E.rp_w_mpyref(v6, r), e1))
      rpx.ed.f7(s, v1, v2, v3, v4, v5, v6, r, pre2, h3, h4, h6, FRp.get_margs(r), rpx.margs(r))
    case Wr.Bad{}:
      Unit{}

def rpx.ed.f5(-s: String, +v1: Maybe<&2, Rp.Verb>, +v2: Maybe<&2, Rp.Comp>, +v3: Maybe<&2, String>, +v4: Maybe<&2, String>, -s5: String, pre: {s == E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, s5)))) : String}, +h3: {E.rp_fit_ms(v3) == True{} : Bool}, +h4: {E.rp_fit_ms(v4) == True{} : Bool}, d: Wr.Dec<Bool>, dp: rpx.bool.P(s5, d)) -> rpx.ed.P(s, FRp.get_ed.f5(v1, v2, v3, v4, d)):
  match d:
    case Wr.Got{+v5, +r}:
      +pre2 = Equal.trans(String, s, E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, s5)))), E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, r))))), pre, Equal.cong(String, String, z => E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, z)))), s5, Wr.put_bool(v5, r), dp))
      rpx.ed.f6(s, v1, v2, v3, v4, v5, r, pre2, h3, h4, FRp.get_mpyref(r), rpx.mpyref(r))
    case Wr.Bad{}:
      Unit{}

def rpx.ed.f4(-s: String, +v1: Maybe<&2, Rp.Verb>, +v2: Maybe<&2, Rp.Comp>, +v3: Maybe<&2, String>, -s4: String, pre: {s == E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, s4))) : String}, +h3: {E.rp_fit_ms(v3) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, dp: rpx.ms.P(s4, d)) -> rpx.ed.P(s, FRp.get_ed.f4(v1, v2, v3, d)):
  match d:
    case Wr.Got{+v4, +r}:
      (e1, +h4) = dp
      +pre2 = Equal.trans(String, s, E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, s4))), E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, r)))), pre, Equal.cong(String, String, z => E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, z))), s4, E.rp_w_ms(v4, r), e1))
      rpx.ed.f5(s, v1, v2, v3, v4, r, pre2, h3, h4, Wr.get_bool(r), rpx.bool(r))
    case Wr.Bad{}:
      Unit{}

def rpx.ed.f3(-s: String, +v1: Maybe<&2, Rp.Verb>, +v2: Maybe<&2, Rp.Comp>, -s3: String, pre: {s == E.rp_w_mverb(v1, E.rp_w_mcomp(v2, s3)) : String}, d: Wr.Dec<Maybe<&2, String>>, dp: rpx.ms.P(s3, d)) -> rpx.ed.P(s, FRp.get_ed.f3(v1, v2, d)):
  match d:
    case Wr.Got{+v3, +r}:
      (e1, +h3) = dp
      +pre2 = Equal.trans(String, s, E.rp_w_mverb(v1, E.rp_w_mcomp(v2, s3)), E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, r))), pre, Equal.cong(String, String, z => E.rp_w_mverb(v1, E.rp_w_mcomp(v2, z)), s3, E.rp_w_ms(v3, r), e1))
      rpx.ed.f4(s, v1, v2, v3, r, pre2, h3, FRp.get_ms(r), rpx.ms(r))
    case Wr.Bad{}:
      Unit{}

def rpx.ed.f2(-s: String, +v1: Maybe<&2, Rp.Verb>, -s2: String, pre: {s == E.rp_w_mverb(v1, s2) : String}, d: Wr.Dec<Maybe<&2, Rp.Comp>>, dp: rpx.mcomp.P(s2, d)) -> rpx.ed.P(s, FRp.get_ed.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      +pre2 = Equal.trans(String, s, E.rp_w_mverb(v1, s2), E.rp_w_mverb(v1, E.rp_w_mcomp(v2, r)), pre, Equal.cong(String, String, z => E.rp_w_mverb(v1, z), s2, E.rp_w_mcomp(v2, r), dp))
      rpx.ed.f3(s, v1, v2, r, pre2, FRp.get_ms(r), rpx.ms(r))
    case Wr.Bad{}:
      Unit{}

def rpx.ed.f1(-s: String, -s1: String, pre: {s == s1 : String}, d: Wr.Dec<Maybe<&2, Rp.Verb>>, dp: rpx.mverb.P(s1, d)) -> rpx.ed.P(s, FRp.get_ed.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      +pre2 = Equal.trans(String, s, s1, E.rp_w_mverb(v1, r), pre, Equal.cong(String, String, z => z, s1, E.rp_w_mverb(v1, r), dp))
      rpx.ed.f2(s, v1, r, pre2, FRp.get_mcomp(r), rpx.mcomp(r))
    case Wr.Bad{}:
      Unit{}

def rpx.ed(+s: String) -> rpx.ed.P(s, FRp.get_ed(s)):
  rpx.ed.f1(s, s, {==}, FRp.get_mverb(s), rpx.mverb(s))

def rpx.eds.P(s: String, d: Wr.Dec<List<&2, Rp.Ed>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_eds(x, r) : String} & {E.rp_fit_eds(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rpx.eds.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Rp.Ed>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == E.rp_w_eds.items(xs, r) : String} & ({List.length(&2, Rp.Ed, xs) == 1n+m : Nat} & {E.rp_fit_eds.items(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def rpx.eds.step(-s: String, +x: Rp.Ed, +s3: String, -k: Nat, ex: {s == E.rp_w_ed(x, s3) : String}, +hx: {E.rp_fit_ed(x) == True{} : Bool}, d: Wr.Dec<List<&2, Rp.Ed>>, ih: rpx.eds.PL(s3, k, d)) -> rpx.eds.PL(s, 1n+k, Wr.get_list.cons(Rp.Ed, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, E.rp_w_ed(x, s3), E.rp_w_ed(x, E.rp_w_eds.items(ys, r)), ex, Equal.cong(String, String, z => E.rp_w_ed(x, z), s3, E.rp_w_eds.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Rp.Ed, ys), 1n+k, e2), LBool.cb_and_intro(E.rp_fit_ed(x), E.rp_fit_eds.items(ys), hx, e3)))
    case Wr.Bad{}:
      Unit{}

def rpx.eds.loop(m: Nat, cur: Wr.Dec<Rp.Ed>, +s: String, pc: rpx.ed.P(s, cur)) -> rpx.eds.PL(s, m, Wr.get_list.go(~Rp.Ed, ~FRp.get_ed, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, +hx) = pc
      (e, ({==}, LBool.cb_and_intro(E.rp_fit_ed(x), True{}, hx, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, +hx) = pc
      rpx.eds.step(s, x, s3, k, e, hx, Wr.get_list.go(~Rp.Ed, ~FRp.get_ed, k, FRp.get_ed(s3)), rpx.eds.loop(k, FRp.get_ed(s3), s3, rpx.ed(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def rpx.eds.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Rp.Ed>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == E.rp_w_eds.items(xs, r) : String}, e2: {List.length(&2, Rp.Ed, xs) == 1n+m : Nat}) -> {s == E.rp_w_eds(xs, r) : String}:
  %Equal.sym(Nat, List.length(&2, Rp.Ed, xs), 1n+m, e2) : {s == Wr.put_nat(_, E.rp_w_eds.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def rpx.eds.conv_n(-m: Nat, -xs: List<&2, Rp.Ed>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Rp.Ed, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Rp.Ed, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Rp.Ed, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def rpx.eds.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Rp.Ed>>, pl: rpx.eds.PL(s2, m, d)) -> rpx.eds.P(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (rpx.eds.conv_s(s, s2, m, xs, r, en, e1, e2), LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, Rp.Ed, xs)), E.rp_fit_eds.items(xs), rpx.eds.conv_n(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def rpx.eds.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> rpx.eds.P(s, Wr.get_list.start(~Rp.Ed, ~FRp.get_ed, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, LBool.cb_and_intro(LawsBase.wire_fits(0n), True{}, fn, {==}))
    case 1n++m:
      rpx.eds.conv(s, s2, m, en, fn, Wr.get_list.go(~Rp.Ed, ~FRp.get_ed, m, FRp.get_ed(s2)), rpx.eds.loop(m, FRp.get_ed(s2), s2, rpx.ed(s2)))

def rpx.eds.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rpx.eds.P(s, Wr.get_list.start(~Rp.Ed, ~FRp.get_ed, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      rpx.eds.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

def rpx.eds(+s: String) -> rpx.eds.P(s, FRp.get_eds(s)):
  rpx.eds.top(s, Wr.get_nat(s), {==})

