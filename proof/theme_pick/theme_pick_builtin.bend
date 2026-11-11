# eukhe: the proof of LAW theme_pick_builtin: no registered file offers
# the name, so the search passes them (LA.pk.skip) and reaches the
# builtins, which answer by their names (LA.pk.bi); the empty name names
# no builtin

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick
import ./base.bend as LA
import ../theme/base.bend as LT

def pb.res(+ls: List<&2, TChoice.Ld>, n: String, +k: Nat, no: {ThemePick.th.none.reg(ls, n) == True{} : Bool}, b: {ThemePick.th.builtin(n) == Some{k} : Maybe<&2, Nat>})
  -> {ThemePick.th.res(TChoice.pick(ls, n)) == TName.Res{U32.from_nat(k), False{}} : TName.Res}:
  match n:
    case SNil{}:
      LT.pt.none_some(Nat, k, {ThemePick.th.res(TChoice.pick(ls, SNil{})) == TName.Res{U32.from_nat(k), False{}} : TName.Res}, b)
    case SCon{+c, +t}:
      +s = {SCon{c, t} : String}
      +cc = TChoice.cands(ls, True{}, 0n)
      +r = List.append(&2, TName.Cand, TName.builtins(), cc)
      +src = List.append(&2, TName.Cand, TChoice.cands(ls, False{}, 0n), r)
      +want = {TName.Res{U32.from_nat(k), False{}} : TName.Res}
      +no2 = Equal.trans(Bool, LA.pk.none(ls, s, False{}), ThemePick.th.none.reg(ls, s), True{}, Equal.sym(Bool, ThemePick.th.none.reg(ls, s), LA.pk.none(ls, s, False{}), LA.pk.none_reg(ls, s)), no)
      +h0 = LA.pk.nonempty(src, s, {==})
      +h1 = LA.pk.skip(ls, False{}, 0n, r, s, no2)
      +h2 = LA.pk.bi(String.eq("eukhe", s), String.eq("dark", s), String.eq("light", s), cc, s, k, b)
      Equal.trans(TName.Res, ThemePick.th.res(TChoice.pick(ls, s)), TChoice.pick.res(ls, s), want, LA.pk.res_pick(ls, s), Equal.trans(TName.Res, TChoice.pick.res(ls, s), TName.find(src, s), want, h0, Equal.trans(TName.Res, TName.find(src, s), TName.find(r, s), want, h1, h2)))

def ThemePick.theme_pick_builtin(ls, n, k, no, b):
  pb.res(ls, n, k, no, b)
