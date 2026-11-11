# eukhe: the proof of LAW theme_pick_registered: the registered files come
# first; none before the file offers the name, so the search finds it
# (LA.pk.found), with the id of its index

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick
import ./base.bend as LA

def pg.reg(+pre: List<&2, TChoice.Ld>, +nm: String, +post: List<&2, TChoice.Ld>, +n: String, ne: {String.is_empty(n) == False{} : Bool}, no: {ThemePick.th.none.reg(pre, n) == True{} : Bool}, same: {String.eq(nm, n) == True{} : Bool})
  -> {ThemePick.th.res(TChoice.pick(List.append(&2, TChoice.Ld, pre, TChoice.Fine{nm, False{}} <> post), n)) == TName.Res{U32.from_nat(Nat.add(3n, List.length(&2, TChoice.Ld, pre))), False{}} : TName.Res}:
  +l = List.append(&2, TChoice.Ld, pre, TChoice.Fine{nm, False{}} <> post)
  +r = List.append(&2, TName.Cand, TName.builtins(), TChoice.cands(l, True{}, 0n))
  +src = List.append(&2, TName.Cand, TChoice.cands(l, False{}, 0n), r)
  +len = List.length(&2, TChoice.Ld, pre)
  +x = {TName.Res{TChoice.file.id(Nat.add(len, 0n)), False{}} : TName.Res}
  +want = {TName.Res{U32.from_nat(Nat.add(3n, len)), False{}} : TName.Res}
  +no2 = Equal.trans(Bool, LA.pk.none(pre, n, False{}), ThemePick.th.none.reg(pre, n), True{}, Equal.sym(Bool, ThemePick.th.none.reg(pre, n), LA.pk.none(pre, n, False{}), LA.pk.none_reg(pre, n)), no)
  +h1 = Equal.trans(TName.Res, TChoice.pick.res(l, n), TName.find(src, n), x, LA.pk.nonempty(src, n, ne), LA.pk.found(pre, nm, post, False{}, 0n, r, n, no2, same))
  +h2 = Equal.cong(Nat, TName.Res, k => TName.Res{U32.from_nat(Nat.add(3n, k)), False{}}, Nat.add(len, 0n), len, Equal.sym(Nat, len, Nat.add(len, 0n), LA.pk.add0(len)))
  Equal.trans(TName.Res, ThemePick.th.res(TChoice.pick(l, n)), TChoice.pick.res(l, n), want, LA.pk.res_pick(l, n), Equal.trans(TName.Res, TChoice.pick.res(l, n), x, want, h1, h2))

def ThemePick.theme_pick_registered(pre, nm, post, n, ne, no, same):
  pg.reg(pre, nm, post, n, ne, no, same)
