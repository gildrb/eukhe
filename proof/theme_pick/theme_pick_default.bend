# eukhe: the proof of LAW theme_pick_default: the empty name resolves to
# the default before any search, quietly; a name no file offers and no
# builtin has passes every candidate (LA.pk.skip, LA.pk.bn) and ends at the
# default, with a warning

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick
import ./base.bend as LA

def pd.empty_res(+ls: List<&2, TChoice.Ld>, +n: String, u: {String.is_empty(n) == True{} : Bool}) -> {TChoice.pick.res(ls, n) == TName.Res{0, False{}} : TName.Res}:
  %Equal.sym(Bool, String.is_empty(n), True{}, u) : {TName.resolve.name.pick(_, TName.sources(TChoice.cands(ls, False{}, 0n), TChoice.cands(ls, True{}, 0n)), n) == TName.Res{0, False{}} : TName.Res}
  {==}

def pd.empty(+ls: List<&2, TChoice.Ld>, +n: String, u: {String.is_empty(n) == True{} : Bool})
  -> {ThemePick.th.res(TChoice.pick(ls, n)) == TName.Res{0, False{}} : TName.Res} & {ThemePick.th.cause(TChoice.pick(ls, n)) == None{} : Maybe<&2, TChoice.Cause>}:
  +e = pd.empty_res(ls, n, u)
  +c = Equal.cong(TName.Res, Maybe<&2, TChoice.Cause>, r => ThemePick.th.cause(TChoice.pick.go(r, ls, n)), TChoice.pick.res(ls, n), TName.Res{0, False{}}, e)
  (Equal.trans(TName.Res, ThemePick.th.res(TChoice.pick(ls, n)), TChoice.pick.res(ls, n), TName.Res{0, False{}}, LA.pk.res_pick(ls, n), e), c)

def pd.missing(+ls: List<&2, TChoice.Ld>, +n: String, ne: {String.is_empty(n) == False{} : Bool}, no: {ThemePick.th.none.reg(ls, n) == True{} : Bool}, nb: {ThemePick.th.builtin(n) == None{} : Maybe<&2, Nat>}, noc: {ThemePick.th.none.custom(ls, n) == True{} : Bool})
  -> {ThemePick.th.res(TChoice.pick(ls, n)) == TName.Res{0, True{}} : TName.Res}:
  +cc = TChoice.cands(ls, True{}, 0n)
  +r = List.append(&2, TName.Cand, TName.builtins(), cc)
  +src = List.append(&2, TName.Cand, TChoice.cands(ls, False{}, 0n), r)
  +want = {TName.Res{0, True{}} : TName.Res}
  +no2 = Equal.trans(Bool, LA.pk.none(ls, n, False{}), ThemePick.th.none.reg(ls, n), True{}, Equal.sym(Bool, ThemePick.th.none.reg(ls, n), LA.pk.none(ls, n, False{}), LA.pk.none_reg(ls, n)), no)
  +noc2 = Equal.trans(Bool, LA.pk.none(ls, n, True{}), ThemePick.th.none.custom(ls, n), True{}, Equal.sym(Bool, ThemePick.th.none.custom(ls, n), LA.pk.none(ls, n, True{}), LA.pk.none_custom(ls, n)), noc)
  +h0 = LA.pk.nonempty(src, n, ne)
  +h1 = LA.pk.skip(ls, False{}, 0n, r, n, no2)
  +h2 = LA.pk.bn(String.eq("eukhe", n), String.eq("dark", n), String.eq("light", n), cc, n, nb)
  +h3 = Equal.cong(List<&2, TName.Cand>, TName.Res, xs => TName.find(xs, n), cc, List.append(&2, TName.Cand, cc, Nil{}), LA.pk.app_nil(cc))
  +h4 = LA.pk.skip(ls, True{}, 0n, Nil{}, n, noc2)
  +c4 = Equal.trans(TName.Res, TName.find(cc, n), TName.find(List.append(&2, TName.Cand, cc, Nil{}), n), want, h3, h4)
  +c2 = Equal.trans(TName.Res, TName.find(r, n), TName.find(cc, n), want, h2, c4)
  +c1 = Equal.trans(TName.Res, TName.find(src, n), TName.find(r, n), want, h1, c2)
  Equal.trans(TName.Res, ThemePick.th.res(TChoice.pick(ls, n)), TChoice.pick.res(ls, n), want, LA.pk.res_pick(ls, n), Equal.trans(TName.Res, TChoice.pick.res(ls, n), TName.find(src, n), want, h0, c1))

def ThemePick.theme_pick_default(ls, n):
  (u => pd.empty(ls, n, u), ne => no => nb => noc => pd.missing(ls, n, ne, no, nb, noc))
