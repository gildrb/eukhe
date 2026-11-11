# eukhe: the proof of LAW cvar_toggle_values
# A toggle adds at most one set, of x, after the agent's own sets. For
# another cvar y that set is not a hit (LS.sv.miss_other): the value stays
# (tv.at_miss). For x: no Bool value, nothing is added; a Bool b adds the
# set of not b, a hit exactly when it counts for an agent (tv.hit_eq): then
# it is the value (tv.at_hit), else the value stays.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ../../laws/cvar/whole.bend as CvarWhole
import ./base.bend as LA
import ./base/resolve.bend as LR
import ./base/save.bend as LS

def tv.over_miss(+p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +t: Cv.Bind, +ds: List<&2, Cv.Decl>, +y: Nat, +base: Cv.Val, h: {Cv.hit.at([t], ds, Cv.Agent{}, y) == False{} : Bool}) -> {Cv.over(ds, Cv.Ag{p, List.append(&2, Cv.Bind, ss, [t])}, y, base) == Cv.over(ds, Cv.Ag{p, ss}, y, base) : Cv.Val}:
  +lp = Cv.layer(p, ds, Cv.Agent{}, y, None{})
  Equal.cong(Maybe<&2, Cv.Val>, Cv.Val, z => Maybe.default(&2, Cv.Val, z, base), Cv.layer(List.append(&2, Cv.Bind, ss, [t]), ds, Cv.Agent{}, y, lp), Cv.layer(ss, ds, Cv.Agent{}, y, lp),
    Equal.trans(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, ss, [t]), ds, Cv.Agent{}, y, lp), Cv.layer([t], ds, Cv.Agent{}, y, Cv.layer(ss, ds, Cv.Agent{}, y, lp)), Cv.layer(ss, ds, Cv.Agent{}, y, lp),
      LA.pv.layer_snoc(ss, t, ds, Cv.Agent{}, y, lp), LA.pv.layer_miss(t, ds, Cv.Agent{}, y, Cv.layer(ss, ds, Cv.Agent{}, y, lp), h)))

def tv.over_hit(+p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +t: Cv.Bind, +ds: List<&2, Cv.Decl>, +y: Nat, +base: Cv.Val, h: {Cv.hit.at([t], ds, Cv.Agent{}, y) == True{} : Bool}) -> {Cv.over(ds, Cv.Ag{p, List.append(&2, Cv.Bind, ss, [t])}, y, base) == Cv.Bind.val(t) : Cv.Val}:
  +lp = Cv.layer(p, ds, Cv.Agent{}, y, None{})
  Equal.cong(Maybe<&2, Cv.Val>, Cv.Val, z => Maybe.default(&2, Cv.Val, z, base), Cv.layer(List.append(&2, Cv.Bind, ss, [t]), ds, Cv.Agent{}, y, lp), Some{Cv.Bind.val(t)},
    Equal.trans(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, ss, [t]), ds, Cv.Agent{}, y, lp), Cv.layer([t], ds, Cv.Agent{}, y, Cv.layer(ss, ds, Cv.Agent{}, y, lp)), Some{Cv.Bind.val(t)},
      LA.pv.layer_snoc(ss, t, ds, Cv.Agent{}, y, lp), LA.pv.layer_hit(t, ds, Cv.Agent{}, y, Cv.layer(ss, ds, Cv.Agent{}, y, lp), h)))

def tv.at_miss(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +t: Cv.Bind, +y: Nat, h: {Cv.hit.at([t], ds, Cv.Agent{}, y) == False{} : Bool}) -> {Cv.value.at(m, ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, List.append(&2, Cv.Bind, ss, [t])}]), y) == Cv.value.at(m, ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), y) : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      +b = Cv.root.val(ds, cfg, y, d)
      +c = Cv.chain(fam, ds, y, b)
      +a1 = {Cv.Ag{p, List.append(&2, Cv.Bind, ss, [t])} : Cv.Ag}
      +a0 = {Cv.Ag{p, ss} : Cv.Ag}
      Equal.cong(Cv.Val, Maybe<&2, Cv.Val>, z => Some{z}, Cv.chain(List.append(&2, Cv.Ag, fam, [a1]), ds, y, b), Cv.chain(List.append(&2, Cv.Ag, fam, [a0]), ds, y, b),
        Equal.trans(Cv.Val, Cv.chain(List.append(&2, Cv.Ag, fam, [a1]), ds, y, b), Cv.over(ds, a1, y, c), Cv.chain(List.append(&2, Cv.Ag, fam, [a0]), ds, y, b), LA.pv.chain_snoc(fam, a1, ds, y, b),
          Equal.trans(Cv.Val, Cv.over(ds, a1, y, c), Cv.over(ds, a0, y, c), Cv.chain(List.append(&2, Cv.Ag, fam, [a0]), ds, y, b), tv.over_miss(p, ss, t, ds, y, c, h),
            Equal.sym(Cv.Val, Cv.chain(List.append(&2, Cv.Ag, fam, [a0]), ds, y, b), Cv.over(ds, a0, y, c), LA.pv.chain_snoc(fam, a0, ds, y, b)))))

def tv.at_hit(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +t: Cv.Bind, +y: Nat, +w: Cv.Val, h: {Cv.hit.at([t], ds, Cv.Agent{}, y) == True{} : Bool}, hc: {Cvar.spec_counts.at(m, Cv.Agent{}, w) == True{} : Bool}) -> {Cv.value.at(m, ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, List.append(&2, Cv.Bind, ss, [t])}]), y) == Some{Cv.Bind.val(t)} : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      LA.pv.absurdF({None{} == Some{Cv.Bind.val(t)} : Maybe<&2, Cv.Val>}, hc)
    case Some{d}:
      +b = Cv.root.val(ds, cfg, y, d)
      +c = Cv.chain(fam, ds, y, b)
      +a1 = {Cv.Ag{p, List.append(&2, Cv.Bind, ss, [t])} : Cv.Ag}
      Equal.cong(Cv.Val, Maybe<&2, Cv.Val>, z => Some{z}, Cv.chain(List.append(&2, Cv.Ag, fam, [a1]), ds, y, b), Cv.Bind.val(t),
        Equal.trans(Cv.Val, Cv.chain(List.append(&2, Cv.Ag, fam, [a1]), ds, y, b), Cv.over(ds, a1, y, c), Cv.Bind.val(t), LA.pv.chain_snoc(fam, a1, ds, y, b), tv.over_hit(p, ss, t, ds, y, c, h)))

# the toggled set of x is a hit for x exactly when it counts
def tv.hit_eq(+ds: List<&2, Cv.Decl>, +x: Nat, +w: Cv.Val) -> {Cv.hit.at([Cv.Bind{x, w}], ds, Cv.Agent{}, x) == Cvar.spec_counts.at(Cv.find(ds, x), Cv.Agent{}, w) : Bool}:
  +t = {Cv.Bind{x, w} : Cv.Bind}
  +vv = Cv.valid(ds, Cv.Agent{}, t)
  Equal.trans(Bool, Cv.hit.when(Nat.is_eq(x, x), ds, Cv.Agent{}, t), Bool.and(Nat.is_eq(x, x), vv), Cvar.spec_counts.at(Cv.find(ds, x), Cv.Agent{}, w), LA.pv.hit_and(Nat.is_eq(x, x), ds, Cv.Agent{}, t),
    Equal.trans(Bool, Bool.and(Nat.is_eq(x, x), vv), vv, Cvar.spec_counts.at(Cv.find(ds, x), Cv.Agent{}, w),
      Equal.cong(Bool, Bool, z => Bool.and(z, vv), Nat.is_eq(x, x), True{}, Equal.sym(Bool, True{}, Nat.is_eq(x, x), LA.cvar.pv.eq_refl(x))),
      LR.rs.valid(ds, Cv.Agent{}, t)))

def tv.false(m: Maybe<&2, Cv.Decl>, v: Maybe<&2, Cv.Val>) -> {v == CvarWhole.spec_toggled(False{}, m, v) : Maybe<&2, Cv.Val>}:
  match v:
    case None{}:
      {==}
    case Some{w}:
      match w:
        case Cv.VNat{n}:
          {==}
        case Cv.VBool{b}:
          {==}

# another cvar y: the toggle's set, if any, is of x
def tv.neq(mv: Maybe<&2, Cv.Val>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, +y: Nat, ne: {Nat.is_eq(x, y) == False{} : Bool}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.add(Cv.Ag{p, ss}, Cv.flip(x, mv))]), y) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), y) : Maybe<&2, Cv.Val>}:
  match mv:
    case None{}:
      {==}
    case Some{w}:
      match w:
        case Cv.VNat{n}:
          {==}
        case Cv.VBool{+b}:
          tv.at_miss(Cv.find(ds, y), ds, cfg, fam, p, ss, Cv.Bind{x, Cv.VBool{Bool.not(b)}}, y, LS.sv.miss_other(ds, Cv.Agent{}, x, Cv.VBool{Bool.not(b)}, y, ne))

def tv.pick(cb: Bool, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, +b: Bool, +ec: {Cvar.spec_counts.at(Cv.find(ds, x), Cv.Agent{}, Cv.VBool{Bool.not(b)}) == cb : Bool}, ev: {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), x) == Some{Cv.VBool{b}} : Maybe<&2, Cv.Val>}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, Cv.VBool{Bool.not(b)}}])}]), x) == CvarWhole.spec_toggled.pick(cb, b, Some{Cv.VBool{b}}) : Maybe<&2, Cv.Val>}:
  match cb:
    case True{}:
      +t = {Cv.Bind{x, Cv.VBool{Bool.not(b)}} : Cv.Bind}
      +he = Equal.trans(Bool, Cv.hit.at([t], ds, Cv.Agent{}, x), Cvar.spec_counts.at(Cv.find(ds, x), Cv.Agent{}, Cv.VBool{Bool.not(b)}), True{}, tv.hit_eq(ds, x, Cv.VBool{Bool.not(b)}), ec)
      tv.at_hit(Cv.find(ds, x), ds, cfg, fam, p, ss, t, x, Cv.VBool{Bool.not(b)}, he, ec)
    case False{}:
      +t = {Cv.Bind{x, Cv.VBool{Bool.not(b)}} : Cv.Bind}
      +he = Equal.trans(Bool, Cv.hit.at([t], ds, Cv.Agent{}, x), Cvar.spec_counts.at(Cv.find(ds, x), Cv.Agent{}, Cv.VBool{Bool.not(b)}), False{}, tv.hit_eq(ds, x, Cv.VBool{Bool.not(b)}), ec)
      Equal.trans(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, List.append(&2, Cv.Bind, ss, [t])}]), x), Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), x), Some{Cv.VBool{b}},
        tv.at_miss(Cv.find(ds, x), ds, cfg, fam, p, ss, t, x, he), ev)

# x itself, its value mv
def tv.same(mv: Maybe<&2, Cv.Val>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, ev: {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), x) == mv : Maybe<&2, Cv.Val>}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.add(Cv.Ag{p, ss}, Cv.flip(x, mv))]), x) == CvarWhole.spec_toggled(True{}, Cv.find(ds, x), mv) : Maybe<&2, Cv.Val>}:
  match mv:
    case None{}:
      ev
    case Some{w}:
      match w:
        case Cv.VNat{n}:
          ev
        case Cv.VBool{+b}:
          tv.pick(Cvar.spec_counts.at(Cv.find(ds, x), Cv.Agent{}, Cv.VBool{Bool.not(b)}), ds, cfg, fam, p, ss, x, b, {==}, ev)

def tv.main(eb: Bool, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, +y: Nat, +eh: {Nat.is_eq(x, y) == eb : Bool}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.Ag{p, ss}, x)]), y) == CvarWhole.spec_toggled(Nat.is_eq(x, y), Cv.find(ds, x), Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), y)) : Maybe<&2, Cv.Val>}:
  match eb:
    case True{}:
      +mv = Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), x)
      +exy = LA.pv.eq_true(x, y, eh)
      %exy : {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.Ag{p, ss}, x)]), _) == CvarWhole.spec_toggled(Nat.is_eq(x, _), Cv.find(ds, x), Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), _)) : Maybe<&2, Cv.Val>}
      %LA.cvar.pv.eq_refl(x) : {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.Ag{p, ss}, x)]), x) == CvarWhole.spec_toggled(_, Cv.find(ds, x), mv) : Maybe<&2, Cv.Val>}
      tv.same(mv, ds, cfg, fam, p, ss, x, {==})
    case False{}:
      +mv = Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), x)
      %Equal.sym(Bool, Nat.is_eq(x, y), False{}, eh) : {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.Ag{p, ss}, x)]), y) == CvarWhole.spec_toggled(_, Cv.find(ds, x), Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), y)) : Maybe<&2, Cv.Val>}
      Equal.trans(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.add(Cv.Ag{p, ss}, Cv.flip(x, mv))]), y), Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), y), CvarWhole.spec_toggled(False{}, Cv.find(ds, x), Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), y)),
        tv.neq(mv, ds, cfg, fam, p, ss, x, y, eh), tv.false(Cv.find(ds, x), Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), y)))

def CvarWhole.cvar_toggle_values(ds, cfg, fam, a, x, y):
  match a:
    case Cv.Ag{+p, +ss}:
      tv.main(Nat.is_eq(x, y), ds, cfg, fam, p, ss, x, y, {==})
