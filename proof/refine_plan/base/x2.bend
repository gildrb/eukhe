# eukhe: lemmas of the refine_plan entry proofs: a decoded value is
# spelled and fits: the options, rows, window, walk and requests

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
import ./x1.bend as LX1

def rpx.opts.P(s: String, d: Wr.Dec<Rp.Opts>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_opts(x, r) : String}
    case Wr.Bad{}:
      Unit

def rpx.opts.f2(-s: String, +v1: Bool, -s2: String, pre: {s == Wr.put_bool(v1, s2) : String}, d: Wr.Dec<Bool>, dp: LX1.rpx.bool.P(s2, d)) -> rpx.opts.P(s, FRp.get_opts.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      +pre2 = Equal.trans(String, s, Wr.put_bool(v1, s2), Wr.put_bool(v1, Wr.put_bool(v2, r)), pre, Equal.cong(String, String, z => Wr.put_bool(v1, z), s2, Wr.put_bool(v2, r), dp))
      pre2
    case Wr.Bad{}:
      Unit{}

def rpx.opts.f1(-s: String, -s1: String, pre: {s == s1 : String}, d: Wr.Dec<Bool>, dp: LX1.rpx.bool.P(s1, d)) -> rpx.opts.P(s, FRp.get_opts.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      +pre2 = Equal.trans(String, s, s1, Wr.put_bool(v1, r), pre, Equal.cong(String, String, z => z, s1, Wr.put_bool(v1, r), dp))
      rpx.opts.f2(s, v1, r, pre2, Wr.get_bool(r), LX1.rpx.bool(r))
    case Wr.Bad{}:
      Unit{}

def rpx.opts(+s: String) -> rpx.opts.P(s, FRp.get_opts(s)):
  rpx.opts.f1(s, s, {==}, Wr.get_bool(s), LX1.rpx.bool(s))

def rpx.was.P(s: String, d: Wr.Dec<Rp.Was>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_was(x, r) : String}
    case Wr.Bad{}:
      Unit

def rpx.was.f3(-s: String, +v1: Bool, +v2: Bool, -s3: String, pre: {s == Wr.put_bool(v1, Wr.put_bool(v2, s3)) : String}, d: Wr.Dec<Bool>, dp: LX1.rpx.bool.P(s3, d)) -> rpx.was.P(s, FRp.get_was.f3(v1, v2, d)):
  match d:
    case Wr.Got{+v3, +r}:
      +pre2 = Equal.trans(String, s, Wr.put_bool(v1, Wr.put_bool(v2, s3)), Wr.put_bool(v1, Wr.put_bool(v2, Wr.put_bool(v3, r))), pre, Equal.cong(String, String, z => Wr.put_bool(v1, Wr.put_bool(v2, z)), s3, Wr.put_bool(v3, r), dp))
      pre2
    case Wr.Bad{}:
      Unit{}

def rpx.was.f2(-s: String, +v1: Bool, -s2: String, pre: {s == Wr.put_bool(v1, s2) : String}, d: Wr.Dec<Bool>, dp: LX1.rpx.bool.P(s2, d)) -> rpx.was.P(s, FRp.get_was.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      +pre2 = Equal.trans(String, s, Wr.put_bool(v1, s2), Wr.put_bool(v1, Wr.put_bool(v2, r)), pre, Equal.cong(String, String, z => Wr.put_bool(v1, z), s2, Wr.put_bool(v2, r), dp))
      rpx.was.f3(s, v1, v2, r, pre2, Wr.get_bool(r), LX1.rpx.bool(r))
    case Wr.Bad{}:
      Unit{}

def rpx.was.f1(-s: String, -s1: String, pre: {s == s1 : String}, d: Wr.Dec<Bool>, dp: LX1.rpx.bool.P(s1, d)) -> rpx.was.P(s, FRp.get_was.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      +pre2 = Equal.trans(String, s, s1, Wr.put_bool(v1, r), pre, Equal.cong(String, String, z => z, s1, Wr.put_bool(v1, r), dp))
      rpx.was.f2(s, v1, r, pre2, Wr.get_bool(r), LX1.rpx.bool(r))
    case Wr.Bad{}:
      Unit{}

def rpx.was(+s: String) -> rpx.was.P(s, FRp.get_was(s)):
  rpx.was.f1(s, s, {==}, Wr.get_bool(s), LX1.rpx.bool(s))

def rpx.wl.P(s: String, d: Wr.Dec<List<&2, Rp.Was>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_wl(x, r) : String} & {E.rp_fit_wl(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rpx.wl.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Rp.Was>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == E.rp_w_wl.items(xs, r) : String} & {List.length(&2, Rp.Was, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def rpx.wl.step(-s: String, +x: Rp.Was, +s3: String, -k: Nat, ex: {s == E.rp_w_was(x, s3) : String}, d: Wr.Dec<List<&2, Rp.Was>>, ih: rpx.wl.PL(s3, k, d)) -> rpx.wl.PL(s, 1n+k, Wr.get_list.cons(Rp.Was, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, E.rp_w_was(x, s3), E.rp_w_was(x, E.rp_w_wl.items(ys, r)), ex, Equal.cong(String, String, z => E.rp_w_was(x, z), s3, E.rp_w_wl.items(ys, r), e1)), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Rp.Was, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

def rpx.wl.loop(m: Nat, cur: Wr.Dec<Rp.Was>, +s: String, pc: rpx.was.P(s, cur)) -> rpx.wl.PL(s, m, Wr.get_list.go(~Rp.Was, ~FRp.get_was, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (pc, {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      rpx.wl.step(s, x, s3, k, pc, Wr.get_list.go(~Rp.Was, ~FRp.get_was, k, FRp.get_was(s3)), rpx.wl.loop(k, FRp.get_was(s3), s3, rpx.was(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def rpx.wl.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Rp.Was>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == E.rp_w_wl.items(xs, r) : String}, e2: {List.length(&2, Rp.Was, xs) == 1n+m : Nat}) -> {s == E.rp_w_wl(xs, r) : String}:
  %Equal.sym(Nat, List.length(&2, Rp.Was, xs), 1n+m, e2) : {s == Wr.put_nat(_, E.rp_w_wl.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def rpx.wl.conv_n(-m: Nat, -xs: List<&2, Rp.Was>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Rp.Was, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Rp.Was, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Rp.Was, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def rpx.wl.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Rp.Was>>, pl: rpx.wl.PL(s2, m, d)) -> rpx.wl.P(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, +e2) = pl
      (rpx.wl.conv_s(s, s2, m, xs, r, en, e1, e2), rpx.wl.conv_n(m, xs, fn, e2))
    case Wr.Bad{}:
      Unit{}

def rpx.wl.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> rpx.wl.P(s, Wr.get_list.start(~Rp.Was, ~FRp.get_was, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, fn)
    case 1n++m:
      rpx.wl.conv(s, s2, m, en, fn, Wr.get_list.go(~Rp.Was, ~FRp.get_was, m, FRp.get_was(s2)), rpx.wl.loop(m, FRp.get_was(s2), s2, rpx.was(s2)))

def rpx.wl.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rpx.wl.P(s, Wr.get_list.start(~Rp.Was, ~FRp.get_was, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      rpx.wl.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

def rpx.wl(+s: String) -> rpx.wl.P(s, FRp.get_wl(s)):
  rpx.wl.top(s, Wr.get_nat(s), {==})

def rpx.win.P(s: String, d: Wr.Dec<Rp.Win>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_win(x, r) : String} & {E.rp_fit_win(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rpx.win.f4(-s: String, +v1: Nat, +v2: Nat, +v3: Nat, -s4: String, pre: {s == Wr.put_nat(v1, Wr.put_nat(v2, Wr.put_nat(v3, s4))) : String}, +h1: {LawsBase.wire_fits(v1) == True{} : Bool}, +h2: {LawsBase.wire_fits(v2) == True{} : Bool}, +h3: {LawsBase.wire_fits(v3) == True{} : Bool}, d: Wr.Dec<Nat>, dp: LX1.rpx.nat.P(s4, d)) -> rpx.win.P(s, FRp.get_win.f4(v1, v2, v3, d)):
  match d:
    case Wr.Got{+v4, +r}:
      (e1, +h4) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(v1, Wr.put_nat(v2, Wr.put_nat(v3, s4))), Wr.put_nat(v1, Wr.put_nat(v2, Wr.put_nat(v3, Wr.put_nat(v4, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(v1, Wr.put_nat(v2, Wr.put_nat(v3, z))), s4, Wr.put_nat(v4, r), e1))
      (pre2, LBool.cb_and_intro(LawsBase.wire_fits(v1), Bool.and(LawsBase.wire_fits(v2), Bool.and(LawsBase.wire_fits(v3), LawsBase.wire_fits(v4))), h1, LBool.cb_and_intro(LawsBase.wire_fits(v2), Bool.and(LawsBase.wire_fits(v3), LawsBase.wire_fits(v4)), h2, LBool.cb_and_intro(LawsBase.wire_fits(v3), LawsBase.wire_fits(v4), h3, h4))))
    case Wr.Bad{}:
      Unit{}

def rpx.win.f3(-s: String, +v1: Nat, +v2: Nat, -s3: String, pre: {s == Wr.put_nat(v1, Wr.put_nat(v2, s3)) : String}, +h1: {LawsBase.wire_fits(v1) == True{} : Bool}, +h2: {LawsBase.wire_fits(v2) == True{} : Bool}, d: Wr.Dec<Nat>, dp: LX1.rpx.nat.P(s3, d)) -> rpx.win.P(s, FRp.get_win.f3(v1, v2, d)):
  match d:
    case Wr.Got{+v3, +r}:
      (e1, +h3) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(v1, Wr.put_nat(v2, s3)), Wr.put_nat(v1, Wr.put_nat(v2, Wr.put_nat(v3, r))), pre, Equal.cong(String, String, z => Wr.put_nat(v1, Wr.put_nat(v2, z)), s3, Wr.put_nat(v3, r), e1))
      rpx.win.f4(s, v1, v2, v3, r, pre2, h1, h2, h3, Wr.get_nat(r), LX1.rpx.nat(r))
    case Wr.Bad{}:
      Unit{}

def rpx.win.f2(-s: String, +v1: Nat, -s2: String, pre: {s == Wr.put_nat(v1, s2) : String}, +h1: {LawsBase.wire_fits(v1) == True{} : Bool}, d: Wr.Dec<Nat>, dp: LX1.rpx.nat.P(s2, d)) -> rpx.win.P(s, FRp.get_win.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      (e1, +h2) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(v1, s2), Wr.put_nat(v1, Wr.put_nat(v2, r)), pre, Equal.cong(String, String, z => Wr.put_nat(v1, z), s2, Wr.put_nat(v2, r), e1))
      rpx.win.f3(s, v1, v2, r, pre2, h1, h2, Wr.get_nat(r), LX1.rpx.nat(r))
    case Wr.Bad{}:
      Unit{}

def rpx.win.f1(-s: String, -s1: String, pre: {s == s1 : String}, d: Wr.Dec<Nat>, dp: LX1.rpx.nat.P(s1, d)) -> rpx.win.P(s, FRp.get_win.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      (e1, +h1) = dp
      +pre2 = Equal.trans(String, s, s1, Wr.put_nat(v1, r), pre, Equal.cong(String, String, z => z, s1, Wr.put_nat(v1, r), e1))
      rpx.win.f2(s, v1, r, pre2, h1, Wr.get_nat(r), LX1.rpx.nat(r))
    case Wr.Bad{}:
      Unit{}

def rpx.win(+s: String) -> rpx.win.P(s, FRp.get_win(s)):
  rpx.win.f1(s, s, {==}, Wr.get_nat(s), LX1.rpx.nat(s))

def rpx.search.P(s: String, d: Wr.Dec<Rp.Search>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_search(x, r) : String} & {E.rp_fit_search(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rpx.search.sprobe.f3(-s: String, +v1: Nat, +v2: Nat, -s3: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(v1, Wr.put_nat(v2, s3))) : String}, +h1: {LawsBase.wire_fits(v1) == True{} : Bool}, +h2: {LawsBase.wire_fits(v2) == True{} : Bool}, d: Wr.Dec<Nat>, dp: LX1.rpx.nat.P(s3, d)) -> rpx.search.P(s, FRp.get_search.sprobe.f3(v1, v2, d)):
  match d:
    case Wr.Got{+v3, +r}:
      (e1, +h3) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(v1, Wr.put_nat(v2, s3))), Wr.put_nat(1n, Wr.put_nat(v1, Wr.put_nat(v2, Wr.put_nat(v3, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(v1, Wr.put_nat(v2, z))), s3, Wr.put_nat(v3, r), e1))
      (pre2, LBool.cb_and_intro(LawsBase.wire_fits(v1), Bool.and(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3)), h1, LBool.cb_and_intro(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3), h2, h3)))
    case Wr.Bad{}:
      Unit{}

def rpx.search.sprobe.f2(-s: String, +v1: Nat, -s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(v1, s2)) : String}, +h1: {LawsBase.wire_fits(v1) == True{} : Bool}, d: Wr.Dec<Nat>, dp: LX1.rpx.nat.P(s2, d)) -> rpx.search.P(s, FRp.get_search.sprobe.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      (e1, +h2) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(v1, s2)), Wr.put_nat(1n, Wr.put_nat(v1, Wr.put_nat(v2, r))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(v1, z)), s2, Wr.put_nat(v2, r), e1))
      rpx.search.sprobe.f3(s, v1, v2, r, pre2, h1, h2, Wr.get_nat(r), LX1.rpx.nat(r))
    case Wr.Bad{}:
      Unit{}

def rpx.search.sprobe.f1(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, dp: LX1.rpx.nat.P(s1, d)) -> rpx.search.P(s, FRp.get_search.sprobe.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      (e1, +h1) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(v1, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(v1, r), e1))
      rpx.search.sprobe.f2(s, v1, r, pre2, h1, Wr.get_nat(r), LX1.rpx.nat(r))
    case Wr.Bad{}:
      Unit{}

def rpx.search.at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rpx.search.P(s, FRp.get_search.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (np, {==})
        case 1n:
          rpx.search.sprobe.f1(s, s1, np, Wr.get_nat(s1), LX1.rpx.nat(s1))
        case 2n:
          (np, {==})
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rpx.search(+s: String) -> rpx.search.P(s, FRp.get_search(s)):
  rpx.search.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rpx.req.P(s: String, d: Wr.Dec<FRp.Req>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == E.rp_w_req(x, r) : String} & {E.rp_fit_req(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rpx.req.qids.f1(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<List<&2, Rp.Ed>>, dp: LX1.rpx.eds.P(s1, d)) -> rpx.req.P(s, FRp.get_req.qids.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      (e1, +h1) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, E.rp_w_eds(v1, r)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, E.rp_w_eds(v1, r), e1))
      (pre2, h1)
    case Wr.Bad{}:
      Unit{}

def rpx.req.qplan.f2(-s: String, +v1: Rp.Opts, -s2: String, pre: {s == Wr.put_nat(1n, E.rp_w_opts(v1, s2)) : String}, d: Wr.Dec<List<&2, Rp.Ed>>, dp: LX1.rpx.eds.P(s2, d)) -> rpx.req.P(s, FRp.get_req.qplan.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      (e1, +h2) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, E.rp_w_opts(v1, s2)), Wr.put_nat(1n, E.rp_w_opts(v1, E.rp_w_eds(v2, r))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, E.rp_w_opts(v1, z)), s2, E.rp_w_eds(v2, r), e1))
      (pre2, h2)
    case Wr.Bad{}:
      Unit{}

def rpx.req.qplan.f1(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Rp.Opts>, dp: rpx.opts.P(s1, d)) -> rpx.req.P(s, FRp.get_req.qplan.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, E.rp_w_opts(v1, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, E.rp_w_opts(v1, r), dp))
      rpx.req.qplan.f2(s, v1, r, pre2, FRp.get_eds(r), LX1.rpx.eds(r))
    case Wr.Bad{}:
      Unit{}

def rpx.req.qback.f2(-s: String, +v1: String, -s2: String, pre: {s == Wr.put_nat(2n, Wr.put_str(v1, s2)) : String}, +h1: {LawsBase.wire_fits(String.length(v1)) == True{} : Bool}, d: Wr.Dec<List<&2, Rp.Was>>, dp: rpx.wl.P(s2, d)) -> rpx.req.P(s, FRp.get_req.qback.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      (e1, +h2) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(v1, s2)), Wr.put_nat(2n, Wr.put_str(v1, E.rp_w_wl(v2, r))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(v1, z)), s2, E.rp_w_wl(v2, r), e1))
      (pre2, LBool.cb_and_intro(LawsBase.wire_fits(String.length(v1)), E.rp_fit_wl(v2), h1, h2))
    case Wr.Bad{}:
      Unit{}

def rpx.req.qback.f1(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, dp: LE.dcw.SP(s1, d)) -> rpx.req.P(s, FRp.get_req.qback.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      (e1, +h1) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_str(v1, r)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_str(v1, r), e1))
      rpx.req.qback.f2(s, v1, r, pre2, h1, FRp.get_wl(r), rpx.wl(r))
    case Wr.Bad{}:
      Unit{}

def rpx.req.qnorm.f3(-s: String, +v1: Maybe<&2, String>, +v2: Maybe<&2, String>, -s3: String, pre: {s == Wr.put_nat(3n, E.rp_w_ms(v1, E.rp_w_ms(v2, s3))) : String}, +h1: {E.rp_fit_ms(v1) == True{} : Bool}, +h2: {E.rp_fit_ms(v2) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, dp: LX1.rpx.ms.P(s3, d)) -> rpx.req.P(s, FRp.get_req.qnorm.f3(v1, v2, d)):
  match d:
    case Wr.Got{+v3, +r}:
      (e1, +h3) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(3n, E.rp_w_ms(v1, E.rp_w_ms(v2, s3))), Wr.put_nat(3n, E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(3n, E.rp_w_ms(v1, E.rp_w_ms(v2, z))), s3, E.rp_w_ms(v3, r), e1))
      (pre2, LBool.cb_and_intro(E.rp_fit_ms(v1), Bool.and(E.rp_fit_ms(v2), E.rp_fit_ms(v3)), h1, LBool.cb_and_intro(E.rp_fit_ms(v2), E.rp_fit_ms(v3), h2, h3)))
    case Wr.Bad{}:
      Unit{}

def rpx.req.qnorm.f2(-s: String, +v1: Maybe<&2, String>, -s2: String, pre: {s == Wr.put_nat(3n, E.rp_w_ms(v1, s2)) : String}, +h1: {E.rp_fit_ms(v1) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, dp: LX1.rpx.ms.P(s2, d)) -> rpx.req.P(s, FRp.get_req.qnorm.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      (e1, +h2) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(3n, E.rp_w_ms(v1, s2)), Wr.put_nat(3n, E.rp_w_ms(v1, E.rp_w_ms(v2, r))), pre, Equal.cong(String, String, z => Wr.put_nat(3n, E.rp_w_ms(v1, z)), s2, E.rp_w_ms(v2, r), e1))
      rpx.req.qnorm.f3(s, v1, v2, r, pre2, h1, h2, FRp.get_ms(r), LX1.rpx.ms(r))
    case Wr.Bad{}:
      Unit{}

def rpx.req.qnorm.f1(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Maybe<&2, String>>, dp: LX1.rpx.ms.P(s1, d)) -> rpx.req.P(s, FRp.get_req.qnorm.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      (e1, +h1) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(3n, s1), Wr.put_nat(3n, E.rp_w_ms(v1, r)), pre, Equal.cong(String, String, z => Wr.put_nat(3n, z), s1, E.rp_w_ms(v1, r), e1))
      rpx.req.qnorm.f2(s, v1, r, pre2, h1, FRp.get_ms(r), LX1.rpx.ms(r))
    case Wr.Bad{}:
      Unit{}

def rpx.req.qscan.f1(-s: String, -s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<String>, dp: LE.dcw.SP(s1, d)) -> rpx.req.P(s, FRp.get_req.qscan.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      (e1, +h1) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(4n, s1), Wr.put_nat(4n, Wr.put_str(v1, r)), pre, Equal.cong(String, String, z => Wr.put_nat(4n, z), s1, Wr.put_str(v1, r), e1))
      (pre2, h1)
    case Wr.Bad{}:
      Unit{}

def rpx.req.qfit.f4(-s: String, +v1: Rp.Win, +v2: Nat, +v3: Rp.Search, -s4: String, pre: {s == Wr.put_nat(5n, E.rp_w_win(v1, Wr.put_nat(v2, E.rp_w_search(v3, s4)))) : String}, +h1: {E.rp_fit_win(v1) == True{} : Bool}, +h2: {LawsBase.wire_fits(v2) == True{} : Bool}, +h3: {E.rp_fit_search(v3) == True{} : Bool}, d: Wr.Dec<Nat>, dp: LX1.rpx.nat.P(s4, d)) -> rpx.req.P(s, FRp.get_req.qfit.f4(v1, v2, v3, d)):
  match d:
    case Wr.Got{+v4, +r}:
      (e1, +h4) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(5n, E.rp_w_win(v1, Wr.put_nat(v2, E.rp_w_search(v3, s4)))), Wr.put_nat(5n, E.rp_w_win(v1, Wr.put_nat(v2, E.rp_w_search(v3, Wr.put_nat(v4, r))))), pre, Equal.cong(String, String, z => Wr.put_nat(5n, E.rp_w_win(v1, Wr.put_nat(v2, E.rp_w_search(v3, z)))), s4, Wr.put_nat(v4, r), e1))
      (pre2, LBool.cb_and_intro(E.rp_fit_win(v1), Bool.and(LawsBase.wire_fits(v2), Bool.and(E.rp_fit_search(v3), LawsBase.wire_fits(v4))), h1, LBool.cb_and_intro(LawsBase.wire_fits(v2), Bool.and(E.rp_fit_search(v3), LawsBase.wire_fits(v4)), h2, LBool.cb_and_intro(E.rp_fit_search(v3), LawsBase.wire_fits(v4), h3, h4))))
    case Wr.Bad{}:
      Unit{}

def rpx.req.qfit.f3(-s: String, +v1: Rp.Win, +v2: Nat, -s3: String, pre: {s == Wr.put_nat(5n, E.rp_w_win(v1, Wr.put_nat(v2, s3))) : String}, +h1: {E.rp_fit_win(v1) == True{} : Bool}, +h2: {LawsBase.wire_fits(v2) == True{} : Bool}, d: Wr.Dec<Rp.Search>, dp: rpx.search.P(s3, d)) -> rpx.req.P(s, FRp.get_req.qfit.f3(v1, v2, d)):
  match d:
    case Wr.Got{+v3, +r}:
      (e1, +h3) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(5n, E.rp_w_win(v1, Wr.put_nat(v2, s3))), Wr.put_nat(5n, E.rp_w_win(v1, Wr.put_nat(v2, E.rp_w_search(v3, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(5n, E.rp_w_win(v1, Wr.put_nat(v2, z))), s3, E.rp_w_search(v3, r), e1))
      rpx.req.qfit.f4(s, v1, v2, v3, r, pre2, h1, h2, h3, Wr.get_nat(r), LX1.rpx.nat(r))
    case Wr.Bad{}:
      Unit{}

def rpx.req.qfit.f2(-s: String, +v1: Rp.Win, -s2: String, pre: {s == Wr.put_nat(5n, E.rp_w_win(v1, s2)) : String}, +h1: {E.rp_fit_win(v1) == True{} : Bool}, d: Wr.Dec<Nat>, dp: LX1.rpx.nat.P(s2, d)) -> rpx.req.P(s, FRp.get_req.qfit.f2(v1, d)):
  match d:
    case Wr.Got{+v2, +r}:
      (e1, +h2) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(5n, E.rp_w_win(v1, s2)), Wr.put_nat(5n, E.rp_w_win(v1, Wr.put_nat(v2, r))), pre, Equal.cong(String, String, z => Wr.put_nat(5n, E.rp_w_win(v1, z)), s2, Wr.put_nat(v2, r), e1))
      rpx.req.qfit.f3(s, v1, v2, r, pre2, h1, h2, FRp.get_search(r), rpx.search(r))
    case Wr.Bad{}:
      Unit{}

def rpx.req.qfit.f1(-s: String, -s1: String, pre: {s == Wr.put_nat(5n, s1) : String}, d: Wr.Dec<Rp.Win>, dp: rpx.win.P(s1, d)) -> rpx.req.P(s, FRp.get_req.qfit.f1(d)):
  match d:
    case Wr.Got{+v1, +r}:
      (e1, +h1) = dp
      +pre2 = Equal.trans(String, s, Wr.put_nat(5n, s1), Wr.put_nat(5n, E.rp_w_win(v1, r)), pre, Equal.cong(String, String, z => Wr.put_nat(5n, z), s1, E.rp_w_win(v1, r), e1))
      rpx.req.qfit.f2(s, v1, r, pre2, h1, Wr.get_nat(r), LX1.rpx.nat(r))
    case Wr.Bad{}:
      Unit{}

def rpx.req.at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rpx.req.P(s, FRp.get_req.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          rpx.req.qids.f1(s, s1, np, FRp.get_eds(s1), LX1.rpx.eds(s1))
        case 1n:
          rpx.req.qplan.f1(s, s1, np, FRp.get_opts(s1), rpx.opts(s1))
        case 2n:
          rpx.req.qback.f1(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 3n:
          rpx.req.qnorm.f1(s, s1, np, FRp.get_ms(s1), LX1.rpx.ms(s1))
        case 4n:
          rpx.req.qscan.f1(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 5n:
          rpx.req.qfit.f1(s, s1, np, FRp.get_win(s1), rpx.win(s1))
        case 6n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rpx.req(+s: String) -> rpx.req.P(s, FRp.get_req(s)):
  rpx.req.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rpx.T(s: String) -> Type:
  Sigma<&1, &1, FRp.Req, q => {s == E.rp_w_req(q, "") : String} & {E.rp_fit_req(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def rpx.top(-s: String, d: Wr.Dec<FRp.Req>, rp: rpx.req.P(s, d), ok: {LawsBase.wire_opens_err(FRp.ffi.got(d)) == False{} : Bool}) -> rpx.T(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(rpx.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(rpx.T(s), ok)
