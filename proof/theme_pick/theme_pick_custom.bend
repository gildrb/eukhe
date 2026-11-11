# eukhe: the proof of LAW theme_pick_custom: the search passes the
# registered files (none offers the name) and the builtins (none has it),
# then finds the first custom file that offers it (LA.pk.found)

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick
import ./base.bend as LA

def pc.res(+pre: List<&2, TChoice.Ld>, +nm: String, +post: List<&2, TChoice.Ld>, +n: String, ne: {String.is_empty(n) == False{} : Bool}, no: {ThemePick.th.none.reg(List.append(&2, TChoice.Ld, pre, TChoice.Fine{nm, True{}} <> post), n) == True{} : Bool}, nb: {ThemePick.th.builtin(n) == None{} : Maybe<&2, Nat>}, noc: {ThemePick.th.none.custom(pre, n) == True{} : Bool}, same: {String.eq(nm, n) == True{} : Bool})
  -> {ThemePick.th.res(TChoice.pick(List.append(&2, TChoice.Ld, pre, TChoice.Fine{nm, True{}} <> post), n)) == TName.Res{U32.from_nat(Nat.add(3n, List.length(&2, TChoice.Ld, pre))), False{}} : TName.Res}:
  +l = List.append(&2, TChoice.Ld, pre, TChoice.Fine{nm, True{}} <> post)
  +cc = TChoice.cands(l, True{}, 0n)
  +r = List.append(&2, TName.Cand, TName.builtins(), cc)
  +src = List.append(&2, TName.Cand, TChoice.cands(l, False{}, 0n), r)
  +len = List.length(&2, TChoice.Ld, pre)
  +x = {TName.Res{TChoice.file.id(Nat.add(len, 0n)), False{}} : TName.Res}
  +want = {TName.Res{U32.from_nat(Nat.add(3n, len)), False{}} : TName.Res}
  +no2 = Equal.trans(Bool, LA.pk.none(l, n, False{}), ThemePick.th.none.reg(l, n), True{}, Equal.sym(Bool, ThemePick.th.none.reg(l, n), LA.pk.none(l, n, False{}), LA.pk.none_reg(l, n)), no)
  +noc2 = Equal.trans(Bool, LA.pk.none(pre, n, True{}), ThemePick.th.none.custom(pre, n), True{}, Equal.sym(Bool, ThemePick.th.none.custom(pre, n), LA.pk.none(pre, n, True{}), LA.pk.none_custom(pre, n)), noc)
  +h0 = LA.pk.nonempty(src, n, ne)
  +h1 = LA.pk.skip(l, False{}, 0n, r, n, no2)
  +h2 = LA.pk.bn(String.eq("eukhe", n), String.eq("dark", n), String.eq("light", n), cc, n, nb)
  +h3 = Equal.cong(List<&2, TName.Cand>, TName.Res, xs => TName.find(xs, n), cc, List.append(&2, TName.Cand, cc, Nil{}), LA.pk.app_nil(cc))
  +h4 = LA.pk.found(pre, nm, post, True{}, 0n, Nil{}, n, noc2, same)
  +h5 = Equal.cong(Nat, TName.Res, k => TName.Res{U32.from_nat(Nat.add(3n, k)), False{}}, Nat.add(len, 0n), len, Equal.sym(Nat, len, Nat.add(len, 0n), LA.pk.add0(len)))
  +c4 = Equal.trans(TName.Res, TName.find(cc, n), x, want, Equal.trans(TName.Res, TName.find(cc, n), TName.find(List.append(&2, TName.Cand, cc, Nil{}), n), x, h3, h4), h5)
  +c2 = Equal.trans(TName.Res, TName.find(r, n), TName.find(cc, n), want, h2, c4)
  +c1 = Equal.trans(TName.Res, TName.find(src, n), TName.find(r, n), want, h1, c2)
  Equal.trans(TName.Res, ThemePick.th.res(TChoice.pick(l, n)), TChoice.pick.res(l, n), want, LA.pk.res_pick(l, n), Equal.trans(TName.Res, TChoice.pick.res(l, n), TName.find(src, n), want, h0, c1))

def ThemePick.theme_pick_custom(pre, nm, post, n, ne, no, nb, noc, same):
  pc.res(pre, nm, post, n, ne, no, nb, noc, same)
