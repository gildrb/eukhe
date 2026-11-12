# eukhe: the proof of LAW rebase_disjoint_lands
#
# PROOF: the rule is the spec's (rr.refines). The edit is valid
# (dl.valid) and the head differs, so the replacement tries context 0
# first (dl.first), whose window is its own lines, unanchored (dl.win0);
# the base and the head each hold one copy, so it lands at the head's
# copy, as long as it was (dl.win); a nonempty copy ends within the head
# (dl.bnd, from rb.cp.one and rb.st.bound), so the landed edit passes the
# crossing check (dl.fits).

import Base
import ../../bend/rebase.bend as R
import ../../spec/harness/rebase.bend as RbSpec
import ../../laws/rebase.bend as Rebase
import ./base.bend as LR
import ./base/refines.bend as LRR

# at context 0 the window of a replacement within b is its own lines
def dl.win0(+b: List<&2, Nat>, +s: Nat, +t: Nat, +inside: {Nat.is_le(t, List.length(&2, Nat, b)) == True{} : Bool}) -> {RbSpec.window(b, s, t, 0n) == R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, Nat.sub(t, s)} : R.Win}:
  %Equal.sym(Nat, Nat.sub(s, 0n), s, LR.rb.sub_zero(s)) : {R.Win{Nat.is_lt(s, 0n), List.append(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, _), Nat.sub(s, _)), List.append(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), List.take(&2, Nat, List.drop(&2, Nat, b, t), 0n))), Nat.is_lt(List.length(&2, Nat, b), Nat.add(t, 0n)), List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, _), Nat.sub(s, _))), List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)))} == R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, Nat.sub(t, s)} : R.Win}
  %Equal.sym(Nat, Nat.sub(s, s), 0n, LR.rb.sub_self(s)) : {R.Win{Nat.is_lt(s, 0n), List.append(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), _), List.append(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), List.take(&2, Nat, List.drop(&2, Nat, b, t), 0n))), Nat.is_lt(List.length(&2, Nat, b), Nat.add(t, 0n)), List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), _)), List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)))} == R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, Nat.sub(t, s)} : R.Win}
  %Equal.sym(List<&2, Nat>, List.take(&2, Nat, List.drop(&2, Nat, b, s), 0n), Nil{}, LR.rb.take_zero(List.drop(&2, Nat, b, s))) : {R.Win{Nat.is_lt(s, 0n), List.append(&2, Nat, _, List.append(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), List.take(&2, Nat, List.drop(&2, Nat, b, t), 0n))), Nat.is_lt(List.length(&2, Nat, b), Nat.add(t, 0n)), List.length(&2, Nat, _), List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)))} == R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, Nat.sub(t, s)} : R.Win}
  %Equal.sym(List<&2, Nat>, List.take(&2, Nat, List.drop(&2, Nat, b, t), 0n), Nil{}, LR.rb.take_zero(List.drop(&2, Nat, b, t))) : {R.Win{Nat.is_lt(s, 0n), List.append(&2, Nat, Nil{}, List.append(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), _)), Nat.is_lt(List.length(&2, Nat, b), Nat.add(t, 0n)), List.length(&2, Nat, Nil{}), List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)))} == R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, Nat.sub(t, s)} : R.Win}
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), Nil{}), List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), LR.rb.app_nil(List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)))) : {R.Win{Nat.is_lt(s, 0n), List.append(&2, Nat, Nil{}, _), Nat.is_lt(List.length(&2, Nat, b), Nat.add(t, 0n)), List.length(&2, Nat, Nil{}), List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)))} == R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, Nat.sub(t, s)} : R.Win}
  %Equal.sym(Bool, Nat.is_lt(s, 0n), False{}, LR.rb.lt_zero(s)) : {R.Win{_, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), Nat.is_lt(List.length(&2, Nat, b), Nat.add(t, 0n)), 0n, List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)))} == R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, Nat.sub(t, s)} : R.Win}
  %Equal.sym(Nat, Nat.add(t, 0n), t, LR.rb.add_zero(t)) : {R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), Nat.is_lt(List.length(&2, Nat, b), _), 0n, List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)))} == R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, Nat.sub(t, s)} : R.Win}
  %Equal.sym(Bool, Nat.is_lt(List.length(&2, Nat, b), t), False{}, LR.rb.le_not_lt(List.length(&2, Nat, b), t, inside)) : {R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), _, 0n, List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)))} == R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, Nat.sub(t, s)} : R.Win}
  %Equal.sym(Nat, List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s))), Nat.sub(t, s), LR.rb.len_region(b, s, t, inside)) : {R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, _} == R.Win{False{}, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s)), False{}, 0n, Nat.sub(t, s)} : R.Win}
  {==}

def dl.first(+s: Nat, +t: Nat, apart: {Nat.is_lt(s, t) == True{} : Bool}) -> {RbSpec.first(s, t) == 0n : Nat}:
  %Equal.sym(Bool, Nat.is_eq(s, t), False{}, LR.rb.lt_ne(s, t, apart)) : {RbSpec.first.of(_) == 0n : Nat}
  {==}

# the edit is sorted and apart within b
def dl.valid(+b: List<&2, Nat>, +s: Nat, +t: Nat, +p: List<&2, Nat>, apart: {Nat.is_lt(s, t) == True{} : Bool}, inside: {Nat.is_le(t, List.length(&2, Nat, b)) == True{} : Bool}) -> {RbSpec.bad([R.Edit{s, t, p}], List.length(&2, Nat, b)) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Nat.is_le(s, t), True{}, LR.rb.lt_le(s, t, apart)) : {RbSpec.bad.of(Bool.and(Bool.and(_, Nat.is_le(t, List.length(&2, Nat, b))), True{}), 0n, None{}) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Nat.is_le(t, List.length(&2, Nat, b)), True{}, inside) : {RbSpec.bad.of(Bool.and(Bool.and(True{}, _), True{}), 0n, None{}) == None{} : Maybe<&2, Nat>}
  {==}

# the landed edit is sorted and apart within h
def dl.fits(+h: List<&2, Nat>, +j: Nat, +d: Nat, +p: List<&2, Nat>, bnd: {Nat.is_le(Nat.add(j, d), List.length(&2, Nat, h)) == True{} : Bool}) -> {RbSpec.bad([R.Edit{j, Nat.add(j, d), p}], List.length(&2, Nat, h)) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Nat.is_le(j, Nat.add(j, d)), True{}, LR.rb.le_add(j, d)) : {RbSpec.bad.of(Bool.and(Bool.and(_, Nat.is_le(Nat.add(j, d), List.length(&2, Nat, h))), True{}), 0n, None{}) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Nat.is_le(Nat.add(j, d), List.length(&2, Nat, h)), True{}, bnd) : {RbSpec.bad.of(Bool.and(Bool.and(True{}, _), True{}), 0n, None{}) == None{} : Maybe<&2, Nat>}
  {==}

# the one copy in each lands the edit at the head's
def dl.win(w: R.Win, +b: List<&2, Nat>, +h: List<&2, Nat>, +p: List<&2, Nat>, +j: Nat, +s: Nat, +d: Nat, +rg: List<&2, Nat>, -next: Unit -> R.Land,
  ew: {w == R.Win{False{}, rg, False{}, 0n, d} : R.Win},
  oh: {RbSpec.copies(h, rg) == [j] : List<&2, Nat>},
  ob: {RbSpec.copies(b, rg) == [s] : List<&2, Nat>})
  -> {RbSpec.step.win(w, b, h, p, 0n, next) == R.Lands{R.Edit{j, Nat.add(j, d), p}} : R.Land}:
  %Equal.sym(R.Win, w, R.Win{False{}, rg, False{}, 0n, d}, ew) : {RbSpec.step.win(_, b, h, p, 0n, next) == R.Lands{R.Edit{j, Nat.add(j, d), p}} : R.Land}
  %Equal.sym(List<&2, Nat>, RbSpec.copies(h, rg), [j], oh) : {RbSpec.step(_, RbSpec.copies(b, rg), False{}, False{}, List.length(&2, Nat, rg), List.length(&2, Nat, h), List.length(&2, Nat, b), 0n, d, p, 0n, next) == R.Lands{R.Edit{j, Nat.add(j, d), p}} : R.Land}
  %Equal.sym(List<&2, Nat>, RbSpec.copies(b, rg), [s], ob) : {RbSpec.step([j], _, False{}, False{}, List.length(&2, Nat, rg), List.length(&2, Nat, h), List.length(&2, Nat, b), 0n, d, p, 0n, next) == R.Lands{R.Edit{j, Nat.add(j, d), p}} : R.Land}
  %Equal.sym(Nat, Nat.add(j, 0n), j, LR.rb.add_zero(j)) : {R.Lands{R.Edit{_, Nat.add(_, d), p}} == R.Lands{R.Edit{j, Nat.add(j, d), p}} : R.Land}
  {==}

def dl.land(+b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +p: List<&2, Nat>, +j: Nat, apart: {Nat.is_lt(s, t) == True{} : Bool}, inside: {Nat.is_le(t, List.length(&2, Nat, b)) == True{} : Bool},
  ob: {RbSpec.copies(b, RbSpec.region(b, R.Edit{s, t, p})) == [s] : List<&2, Nat>},
  oh: {RbSpec.copies(h, RbSpec.region(b, R.Edit{s, t, p})) == [j] : List<&2, Nat>})
  -> {RbSpec.land(b, h, R.Edit{s, t, p}, 0n) == R.Lands{R.Edit{j, Nat.add(j, Nat.sub(t, s)), p}} : R.Land}:
  %Equal.sym(Nat, RbSpec.first(s, t), 0n, dl.first(s, t, apart)) : {RbSpec.land.go(Nat.sub(1n+RbSpec.ctx(), _), b, h, s, t, p, _, 0n) == R.Lands{R.Edit{j, Nat.add(j, Nat.sub(t, s)), p}} : R.Land}
  dl.win(RbSpec.window(b, s, t, 0n), b, h, p, j, s, Nat.sub(t, s), RbSpec.region(b, R.Edit{s, t, p}), u => RbSpec.land.go(8n, b, h, s, t, p, 1n, 0n), dl.win0(b, s, t, inside), oh, ob)

def dl.bnd(rg: List<&2, Nat>, +j: Nat, +h: List<&2, Nat>, -q: Nat, e: {RbSpec.starts(rg, List.drop(&2, Nat, h, j)) == True{} : Bool}, ne: {List.length(&2, Nat, rg) == 1n+q : Nat}) -> {Nat.is_le(Nat.add(j, List.length(&2, Nat, rg)), List.length(&2, Nat, h)) == True{} : Bool}:
  match rg:
    case Nil{}:
      LR.rb.zero_succ({Nat.is_le(Nat.add(j, 0n), List.length(&2, Nat, h)) == True{} : Bool}, q, ne)
    case Con{+x, +wt}:
      LR.rb.st.bound(j, h, x, wt, e)

# the landed edit ends within the head
def dl.within(+b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +p: List<&2, Nat>, +j: Nat, apart: {Nat.is_lt(s, t) == True{} : Bool}, inside: {Nat.is_le(t, List.length(&2, Nat, b)) == True{} : Bool},
  oh: {RbSpec.copies(h, RbSpec.region(b, R.Edit{s, t, p})) == [j] : List<&2, Nat>})
  -> {Nat.is_le(Nat.add(j, Nat.sub(t, s)), List.length(&2, Nat, h)) == True{} : Bool}:
  +rg = RbSpec.region(b, R.Edit{s, t, p})
  +el = LR.rb.len_region(b, s, t, inside)
  +le1 = Equal.trans(Bool, Nat.is_le(1n+s, t), Nat.is_lt(s, t), True{}, LR.rb.le_succ(s, t), apart)
  +ne = Equal.trans(Nat, List.length(&2, Nat, rg), Nat.sub(t, s), 1n+Nat.sub(t, 1n+s), el, LR.rb.sub_succ(s, t, le1))
  +bd = dl.bnd(rg, j, h, Nat.sub(t, 1n+s), LR.rb.cp.one(h, rg, j, oh), ne)
  %el : {Nat.is_le(Nat.add(j, _), List.length(&2, Nat, h)) == True{} : Bool}
  bd

def Rebase.rebase_disjoint_lands(b, h, s, t, p, j, apart, inside, stale, once_b, once_h):
  +l = {[R.Edit{s, t, p}] : List<&2, R.Edit>}
  +f = {R.Edit{j, Nat.add(j, Nat.sub(t, s)), p} : R.Edit}
  +a = apart
  +ins = inside
  +oh = once_h
  %Equal.sym(R.Outcome, R.rebase(b, h, l), RbSpec.rebase(b, h, l), LRR.rr.refines(b, h, l)) : {_ == R.Rebased{[f]} : R.Outcome}
  %Equal.sym(Maybe<&2, Nat>, RbSpec.bad(l, List.length(&2, Nat, b)), None{}, dl.valid(b, s, t, p, a, ins)) : {RbSpec.rebase.of(_, RbSpec.same(b, h), b, h, l) == R.Rebased{[f]} : R.Outcome}
  %Equal.sym(Bool, RbSpec.same(b, h), False{}, stale) : {RbSpec.rebase.of(None{}, _, b, h, l) == R.Rebased{[f]} : R.Outcome}
  %Equal.sym(R.Land, RbSpec.land(b, h, R.Edit{s, t, p}, 0n), R.Lands{f}, dl.land(b, h, s, t, p, j, a, ins, once_b, oh)) : {RbSpec.crossed(RbSpec.land_all.of(_, R.Rebased{Nil{}}), List.length(&2, Nat, h)) == R.Rebased{[f]} : R.Outcome}
  %Equal.sym(Maybe<&2, Nat>, RbSpec.bad([f], List.length(&2, Nat, h)), None{}, dl.fits(h, j, Nat.sub(t, s), p, dl.within(b, h, s, t, p, j, a, ins, oh))) : {RbSpec.crossed.of(_, [f]) == R.Rebased{[f]} : R.Outcome}
  {==}
