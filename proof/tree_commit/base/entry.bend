# eukhe: lemmas of the entry proofs of area tree_commit
#
# The change codec of bend/ffi_tree_commit.bend against the spec's
# spelling (laws/tree_commit.bend spell_ch, spell_req), both directions:
# a spelled change or request whose keys fit reads back (tce.ch_rt,
# tce.go_rt), and a decoder answers Got only for a spelled input whose
# keys fit (tce.ch, tce.req). The reply's encoder is the spec's
# (tce.reply).

import Base
import ../../../bend/tree_commit.bend as Tc
import ../../../bend/ffi_tree_commit.bend as FTc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../../base/wire.bend as LWire
import ../../../laws/tree_commit.bend as TreeCommit

# ---- logic ----

def tce.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def tce.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : tce.BT(_, G)
  Unit{}

def tce.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def tce.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      tce.tf({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def tce.and_tt(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      ha

# ---- the reply ----

def tce.put_step(x: Tc.Res, -n: Nat, -r: String) -> {Wr.put_list.step(~Tc.Res, ~FTc.put_res, x, (n, r)) == (1n+n, TreeCommit.spell_res(x, r)) : Nat & String}:
  match x:
    case Tc.Apply{i}:
      {==}
    case Tc.Orphan{i}:
      {==}
    case Tc.Retire{i}:
      {==}

def tce.put_go(xs: List<&2, Tc.Res>, -rest: String) -> {Wr.put_list.go(~Tc.Res, ~FTc.put_res, xs, rest) == (List.length(&2, Tc.Res, xs), TreeCommit.spell_ress(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Tc.Res, ~FTc.put_res, t, rest), (List.length(&2, Tc.Res, t), TreeCommit.spell_ress(t, rest)), tce.put_go(t, rest)) : {Wr.put_list.step(~Tc.Res, ~FTc.put_res, x, _) == (1n+List.length(&2, Tc.Res, t), TreeCommit.spell_res(x, TreeCommit.spell_ress(t, rest))) : Nat & String}
      tce.put_step(x, List.length(&2, Tc.Res, t), TreeCommit.spell_ress(t, rest))

# the entry's reply encoder is the spec's speller
def tce.reply(+xs: List<&2, Tc.Res>) -> {Wr.put_list(~Tc.Res, ~FTc.put_res, xs, "") == TreeCommit.spell_reply(xs) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Tc.Res, ~FTc.put_res, xs, ""), (List.length(&2, Tc.Res, xs), TreeCommit.spell_ress(xs, "")), tce.put_go(xs, "")) : {Wr.put_list.fin(_) == TreeCommit.spell_reply(xs) : String}
  {==}

# the entry's reply is a count, then the results: never the error form
def tce.reply_not_err(+xs: List<&2, Tc.Res>) -> {LawsBase.wire_opens_err(Wr.put_list(~Tc.Res, ~FTc.put_res, xs, "")) == False{} : Bool}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Tc.Res, ~FTc.put_res, xs, ""), (List.length(&2, Tc.Res, xs), TreeCommit.spell_ress(xs, "")), tce.put_go(xs, "")) : {LawsBase.wire_opens_err(Wr.put_list.fin(_)) == False{} : Bool}
  Wire.wire_nat_not_err(List.length(&2, Tc.Res, xs), TreeCommit.spell_ress(xs, ""))

# ---- spelled requests read back ----

# a spelled change whose keys fit reads back
def tce.ch_rt(x: Tc.Ch, +rest: String, +h: {TreeCommit.ch_fits(x) == True{} : Bool}) -> {FTc.get_ch(TreeCommit.spell_ch(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Tc.Ch>}:
  match x:
    case Tc.Here{+k}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, Wr.put_nat(k, rest))), Wr.Got{0n, Wr.put_nat(k, rest)}, Wire.wire_nat_round_trip(0n, Wr.put_nat(k, rest), {==})) : {FTc.get_ch.start(_) == Wr.Got{Tc.Here{k}, rest} : Wr.Dec<Tc.Ch>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(k, rest)), Wr.Got{k, rest}, Wire.wire_nat_round_trip(k, rest, h)) : {FTc.get_ch.here(_) == Wr.Got{Tc.Here{k}, rest} : Wr.Dec<Tc.Ch>}
      {==}
    case Tc.Under{+k, +u}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(u, rest)))), Wr.Got{1n, Wr.put_nat(k, Wr.put_nat(u, rest))}, Wire.wire_nat_round_trip(1n, Wr.put_nat(k, Wr.put_nat(u, rest)), {==})) : {FTc.get_ch.start(_) == Wr.Got{Tc.Under{k, u}, rest} : Wr.Dec<Tc.Ch>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(k, Wr.put_nat(u, rest))), Wr.Got{k, Wr.put_nat(u, rest)}, Wire.wire_nat_round_trip(k, Wr.put_nat(u, rest), tce.and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(u), h))) : {FTc.get_ch.wait(_) == Wr.Got{Tc.Under{k, u}, rest} : Wr.Dec<Tc.Ch>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(u, rest)), Wr.Got{u, rest}, Wire.wire_nat_round_trip(u, rest, tce.and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(u), h))) : {FTc.get_ch.up(k, _) == Wr.Got{Tc.Under{k, u}, rest} : Wr.Dec<Tc.Ch>}
      {==}
    case Tc.Gone{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, rest)), Wr.Got{2n, rest}, Wire.wire_nat_round_trip(2n, rest, {==})) : {FTc.get_ch.start(_) == Wr.Got{Tc.Gone{}, rest} : Wr.Dec<Tc.Ch>}
      {==}

# the item loop reads back x then t
def tce.go_rt(+t: List<&2, Tc.Ch>, +x: Tc.Ch, +rest: String, +h: {TreeCommit.chs_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Tc.Ch, ~FTc.get_ch, List.length(&2, Tc.Ch, t), FTc.get_ch(TreeCommit.spell_ch(x, TreeCommit.spell_chs(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Tc.Ch>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Tc.Ch>, FTc.get_ch(TreeCommit.spell_ch(x, rest)), Wr.Got{x, rest}, tce.ch_rt(x, rest, tce.and_l(TreeCommit.ch_fits(x), TreeCommit.chs_fit([]), h))) : {Wr.get_list.go(~Tc.Ch, ~FTc.get_ch, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Tc.Ch>>}
      {==}
    case Con{+y, +u}:
      +r2 = TreeCommit.spell_ch(y, TreeCommit.spell_chs(u, rest))
      %Equal.sym(Wr.Dec<Tc.Ch>, FTc.get_ch(TreeCommit.spell_ch(x, r2)), Wr.Got{x, r2}, tce.ch_rt(x, r2, tce.and_l(TreeCommit.ch_fits(x), TreeCommit.chs_fit(y <> u), h))) : {Wr.get_list.go(~Tc.Ch, ~FTc.get_ch, 1n+List.length(&2, Tc.Ch, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Tc.Ch>>}
      %Equal.sym(Wr.Dec<List<&2, Tc.Ch>>, Wr.get_list.go(~Tc.Ch, ~FTc.get_ch, List.length(&2, Tc.Ch, u), FTc.get_ch(r2)), Wr.Got{y <> u, rest}, tce.go_rt(u, y, rest, tce.and_r(TreeCommit.ch_fits(x), TreeCommit.chs_fit(y <> u), h))) : {Wr.get_list.cons(Tc.Ch, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Tc.Ch>>}
      {==}

# ---- only spelled requests decode ----

# what the Nat decoder's answer says about its input s
def tce.PNF(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tce.pnf_go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tce.PNF(s, d):
  match d:
    case Wr.Got{+n, +r}:
      (Wire.wire_nat_exact(s, n, r, ed), Wire.wire_nat_decoded_fits(s, n, r, ed))
    case Wr.Bad{}:
      Unit{}

def tce.pnf(+s: String) -> tce.PNF(s, Wr.get_nat(s)):
  tce.pnf_go(s, Wr.get_nat(s), {==})

# what a change decoder's answer says about its input s
def tce.CH(s: String, d: Wr.Dec<Tc.Ch>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == TreeCommit.spell_ch(x, r) : String} & {TreeCommit.ch_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tce.ch_up(-s: String, -s2: String, +k: Nat, e0: {s == Wr.put_nat(1n, Wr.put_nat(k, s2)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, p: tce.PNF(s2, d)) -> tce.CH(s, FTc.get_ch.up(k, d)):
  match d:
    case Wr.Got{+u, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(k, s2)), Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(u, r))), e0, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(k, z)), s2, Wr.put_nat(u, r), e1)), tce.and_tt(LawsBase.wire_fits(k), LawsBase.wire_fits(u), fk, f1))
    case Wr.Bad{}:
      Unit{}

def tce.ch_wait(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, p: tce.PNF(s1, d)) -> tce.CH(s, FTc.get_ch.wait(d)):
  match d:
    case Wr.Got{+k, +s2}:
      (e1, f1) = p
      tce.ch_up(s, s2, k, Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(k, s2)), e0, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(k, s2), e1)), f1, Wr.get_nat(s2), tce.pnf(s2))
    case Wr.Bad{}:
      Unit{}

def tce.ch_here(-s: String, -s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, p: tce.PNF(s1, d)) -> tce.CH(s, FTc.get_ch.here(d)):
  match d:
    case Wr.Got{+k, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_nat(k, r)), e0, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_nat(k, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def tce.ch_top(-s: String, d: Wr.Dec<Nat>, p: tce.PNF(s, d)) -> tce.CH(s, FTc.get_ch.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          tce.ch_here(s, s1, e0, Wr.get_nat(s1), tce.pnf(s1))
        case 1n:
          (e0, f0) = p
          tce.ch_wait(s, s1, e0, Wr.get_nat(s1), tce.pnf(s1))
        case 2n:
          (e0, f0) = p
          (e0, {==})
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a change decoded is spelled, and its keys fit
def tce.ch(+s: String) -> tce.CH(s, FTc.get_ch(s)):
  tce.ch_top(s, Wr.get_nat(s), tce.pnf(s))

# what the item loop's answer says about its input s (m + 1 items)
def tce.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Tc.Ch>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == TreeCommit.spell_chs(xs, r) : String} & ({List.length(&2, Tc.Ch, xs) == 1n+m : Nat} & {TreeCommit.chs_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def tce.step(-s: String, +x: Tc.Ch, +s3: String, -k: Nat, ex: {s == TreeCommit.spell_ch(x, s3) : String}, fx: {TreeCommit.ch_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Tc.Ch>>, ih: tce.PL(s3, k, d)) -> tce.PL(s, 1n+k, Wr.get_list.cons(Tc.Ch, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, rest) = ih
      (e2, e3) = rest
      (Equal.trans(String, s, TreeCommit.spell_ch(x, s3), TreeCommit.spell_ch(x, TreeCommit.spell_chs(ys, r)), ex, Equal.cong(String, String, z => TreeCommit.spell_ch(x, z), s3, TreeCommit.spell_chs(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Tc.Ch, ys), 1n+k, e2), tce.and_tt(TreeCommit.ch_fits(x), TreeCommit.chs_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items whose keys fit
def tce.loop(m: Nat, cur: Wr.Dec<Tc.Ch>, +s: String, pc: tce.CH(s, cur)) -> tce.PL(s, m, Wr.get_list.go(~Tc.Ch, ~FTc.get_ch, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, tce.and_tt(TreeCommit.ch_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      tce.step(s, x, s3, k, e, f, Wr.get_list.go(~Tc.Ch, ~FTc.get_ch, k, FTc.get_ch(s3)), tce.loop(k, FTc.get_ch(s3), s3, tce.ch(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a request decoder's answer says about its input s
def tce.LS(s: String, d: Wr.Dec<List<&2, Tc.Ch>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == TreeCommit.spell_req(xs, r) : String} & {TreeCommit.req_fits(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tce.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Tc.Ch>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == TreeCommit.spell_chs(xs, r) : String}, e2: {List.length(&2, Tc.Ch, xs) == 1n+m : Nat}) -> {s == TreeCommit.spell_req(xs, r) : String}:
  %Equal.sym(Nat, List.length(&2, Tc.Ch, xs), 1n+m, e2) : {s == Wr.put_nat(_, TreeCommit.spell_chs(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def tce.conv_f(+m: Nat, +xs: List<&2, Tc.Ch>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Tc.Ch, xs) == 1n+m : Nat}, e3: {TreeCommit.chs_fit(xs) == True{} : Bool}) -> {TreeCommit.req_fits(xs) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Tc.Ch, xs), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), TreeCommit.chs_fit(xs)) == True{} : Bool}
  tce.and_tt(LawsBase.wire_fits(1n+m), TreeCommit.chs_fit(xs), fn, e3)

def tce.conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Tc.Ch>>, pl: tce.PL(s2, m, d)) -> tce.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, rest) = pl
      (+e2, e3) = rest
      (tce.conv_s(s, s2, m, xs, r, en, e1, e2), tce.conv_f(m, xs, fn, e2, e3))
    case Wr.Bad{}:
      Unit{}

def tce.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> tce.LS(s, Wr.get_list.start(~Tc.Ch, ~FTc.get_ch, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      tce.conv(s, s2, m, en, fn, Wr.get_list.go(~Tc.Ch, ~FTc.get_ch, m, FTc.get_ch(s2)), tce.loop(m, FTc.get_ch(s2), s2, tce.ch(s2)))

def tce.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tce.LS(s, Wr.get_list.start(~Tc.Ch, ~FTc.get_ch, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      tce.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and its count and keys fit
def tce.req(+s: String) -> tce.LS(s, FTc.get_req(s)):
  tce.top(s, Wr.get_nat(s), {==})
