# eukhe: the proof of LAW rebase_result_applies
#
# PROOF: the rule is the spec's (rebase_refines), so it is enough that
# every answer of the spec is good (ap.Good): a head that is the base
# (rb.same_eq) takes valid edits that replay themselves (rb.pairs_refl);
# else each landed edit sits at the head's one copy of its window, so the
# head holds the window's lines there (rb.cp.one) and, past the context
# before the edit (rb.st.app, rb.drop_drop), the edit's own lines
# (rb.st.take): the landed edit replaces the base lines the edit replaced
# (ap.land_ok, carried through the contexts and the edits: ap.go, ap.all),
# and the crossing check leaves only edits sorted and apart (ap.crossed).

import Base
import ../../bend/rebase.bend as R
import ../../spec/harness/rebase.bend as RbSpec
import ../../laws/rebase.bend as Rebase
import ./base.bend as LR
import ./rebase_refines.bend as PRebaseRefines

# what a landing of e says
def ap.LG(+b: List<&2, Nat>, +h: List<&2, Nat>, +e: R.Edit, l: R.Land) -> Type:
  match l:
    case R.Lands{+f}:
      {Bool.and(RbSpec.same(RbSpec.edit_lines(f), RbSpec.edit_lines(e)), RbSpec.same(RbSpec.region(h, f), RbSpec.region(b, e))) == True{} : Bool}
    case R.Fails{w}:
      Unit

# what the landings of es say
def ap.Pairs(+b: List<&2, Nat>, +h: List<&2, Nat>, es: List<&2, R.Edit>, o: R.Outcome) -> Type:
  match o:
    case R.Rebased{fs}:
      {RbSpec.pairs(b, h, es, fs) == True{} : Bool}
    case R.Conflict{w}:
      Unit

# what an answer says
def ap.Good(+b: List<&2, Nat>, +h: List<&2, Nat>, es: List<&2, R.Edit>, o: R.Outcome) -> Type:
  match o:
    case R.Rebased{fs}:
      {RbSpec.replays(b, h, es, fs) == True{} : Bool}
    case R.Conflict{w}:
      Unit

# the edit landed at the head's one copy of its window replaces the base
# lines it replaced
def ap.land_ok(+lc: List<&2, Nat>, +rg: List<&2, Nat>, +rc: List<&2, Nat>, +h: List<&2, Nat>, +j: Nat, +ls: List<&2, Nat>, -b: List<&2, Nat>, -s: Nat, -t: Nat,
  ech: {RbSpec.copies(h, List.append(&2, Nat, lc, List.append(&2, Nat, rg, rc))) == [j] : List<&2, Nat>},
  erg: {rg == RbSpec.region(b, R.Edit{s, t, ls}) : List<&2, Nat>})
  -> {Bool.and(RbSpec.same(ls, ls), RbSpec.same(RbSpec.region(h, R.Edit{Nat.add(j, List.length(&2, Nat, lc)), Nat.add(Nat.add(j, List.length(&2, Nat, lc)), List.length(&2, Nat, rg)), ls}), RbSpec.region(b, R.Edit{s, t, ls}))) == True{} : Bool}:
  +w = List.append(&2, Nat, rg, rc)
  +a = Nat.add(j, List.length(&2, Nat, lc))
  +st1 = LR.rb.st.app(lc, w, List.drop(&2, Nat, h, j), LR.rb.cp.one(h, List.append(&2, Nat, lc, w), j, ech))
  +st2 = Equal.trans(Bool, RbSpec.starts(w, List.drop(&2, Nat, h, a)), RbSpec.starts(w, List.drop(&2, Nat, List.drop(&2, Nat, h, j), List.length(&2, Nat, lc))), True{}, Equal.cong(List<&2, Nat>, Bool, z => RbSpec.starts(w, z), List.drop(&2, Nat, h, a), List.drop(&2, Nat, List.drop(&2, Nat, h, j), List.length(&2, Nat, lc)), Equal.sym(List<&2, Nat>, List.drop(&2, Nat, List.drop(&2, Nat, h, j), List.length(&2, Nat, lc)), List.drop(&2, Nat, h, a), LR.rb.drop_drop(j, h, List.length(&2, Nat, lc)))), st1)
  %Equal.sym(Nat, Nat.sub(Nat.add(a, List.length(&2, Nat, rg)), a), List.length(&2, Nat, rg), LR.rb.add_sub(a, List.length(&2, Nat, rg))) : {Bool.and(RbSpec.same(ls, ls), RbSpec.same(List.take(&2, Nat, List.drop(&2, Nat, h, a), _), RbSpec.region(b, R.Edit{s, t, ls}))) == True{} : Bool}
  %erg : {Bool.and(RbSpec.same(ls, ls), RbSpec.same(List.take(&2, Nat, List.drop(&2, Nat, h, a), List.length(&2, Nat, rg)), _)) == True{} : Bool}
  %Equal.sym(Bool, RbSpec.same(ls, ls), True{}, LR.rb.same_refl(ls)) : {Bool.and(_, RbSpec.same(List.take(&2, Nat, List.drop(&2, Nat, h, a), List.length(&2, Nat, rg)), rg)) == True{} : Bool}
  LR.rb.st.take(rg, rc, List.drop(&2, Nat, h, a), st2)

def ap.pick(q: Bool, +b: List<&2, Nat>, +h: List<&2, Nat>, +e: R.Edit, f: R.Edit, -next: Unit -> R.Land, lp: ap.LG(b, h, e, R.Lands{f}), ih: ap.LG(b, h, e, next(Unit{}))) -> ap.LG(b, h, e, RbSpec.step.pick(q, f, next)):
  match q:
    case True{}:
      lp
    case False{}:
      ih

def ap.base(cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +bl: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +e: R.Edit, f: R.Edit, -next: Unit -> R.Land, lp: ap.LG(b, h, e, R.Lands{f}), ih: ap.LG(b, h, e, next(Unit{}))) -> ap.LG(b, h, e, RbSpec.step.base(cb, la, ha, wl, bl, f, next)):
  match cb:
    case Nil{}:
      ih
    case Con{+x, more}:
      match more:
        case Nil{}:
          ap.pick(RbSpec.sits(la, ha, x, wl, bl), b, h, e, f, next, lp, ih)
        case Con{y, rest}:
          ih

def ap.one(q: Bool, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +bl: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +e: R.Edit, f: R.Edit, +i: Nat, -next: Unit -> R.Land, lp: ap.LG(b, h, e, R.Lands{f}), ih: ap.LG(b, h, e, next(Unit{}))) -> ap.LG(b, h, e, RbSpec.step.one(q, cb, la, ha, wl, bl, f, i, next)):
  match q:
    case True{}:
      ap.base(cb, la, ha, wl, bl, b, h, e, f, next, lp, ih)
    case False{}:
      Unit{}

# one context's verdict says what a landing says
def ap.step(ch: List<&2, Nat>, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +hl: Nat, +bl: Nat, +lc: List<&2, Nat>, +rg: List<&2, Nat>, +rc: List<&2, Nat>, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +ls: List<&2, Nat>, +i: Nat, -next: Unit -> R.Land,
  ech: {RbSpec.copies(h, List.append(&2, Nat, lc, List.append(&2, Nat, rg, rc))) == ch : List<&2, Nat>},
  erg: {rg == RbSpec.region(b, R.Edit{s, t, ls}) : List<&2, Nat>},
  ih: ap.LG(b, h, R.Edit{s, t, ls}, next(Unit{})))
  -> ap.LG(b, h, R.Edit{s, t, ls}, RbSpec.step(ch, cb, la, ha, wl, hl, bl, List.length(&2, Nat, lc), List.length(&2, Nat, rg), ls, i, next)):
  match ch:
    case Nil{}:
      Unit{}
    case Con{+j, more}:
      match more:
        case Nil{}:
          +f = {R.Edit{Nat.add(j, List.length(&2, Nat, lc)), Nat.add(Nat.add(j, List.length(&2, Nat, lc)), List.length(&2, Nat, rg)), ls} : R.Edit}
          ap.one(RbSpec.sits(la, ha, j, wl, hl), cb, la, ha, wl, bl, b, h, R.Edit{s, t, ls}, f, i, next, ap.land_ok(lc, rg, rc, h, j, ls, b, s, t, ech, erg), ih)
        case Con{y, rest}:
          ih

def ap.go(fuel: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +ls: List<&2, Nat>, +k: Nat, +i: Nat) -> ap.LG(b, h, R.Edit{s, t, ls}, RbSpec.land.go(fuel, b, h, s, t, ls, k, i)):
  match fuel:
    case 0n:
      Unit{}
    case 1n++p:
      +lo = Nat.sub(s, k)
      +lc = List.take(&2, Nat, List.drop(&2, Nat, b, lo), Nat.sub(s, lo))
      +rg = List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s))
      +rc = List.take(&2, Nat, List.drop(&2, Nat, b, t), k)
      +w = List.append(&2, Nat, lc, List.append(&2, Nat, rg, rc))
      ap.step(RbSpec.copies(h, w), RbSpec.copies(b, w), Nat.is_lt(s, k), Nat.is_lt(List.length(&2, Nat, b), Nat.add(t, k)), List.length(&2, Nat, w), List.length(&2, Nat, h), List.length(&2, Nat, b), lc, rg, rc, b, h, s, t, ls, i, u => RbSpec.land.go(p, b, h, s, t, ls, 1n+k, i), {==}, {==}, ap.go(p, b, h, s, t, ls, 1n+k, i))

def ap.land(+b: List<&2, Nat>, +h: List<&2, Nat>, e: R.Edit, +i: Nat) -> ap.LG(b, h, e, RbSpec.land(b, h, e, i)):
  match e:
    case R.Edit{+s, +t, +ls}:
      ap.go(Nat.sub(1n+RbSpec.ctx(), RbSpec.first(s, t)), b, h, s, t, ls, RbSpec.first(s, t), i)

def ap.all.of(+b: List<&2, Nat>, +h: List<&2, Nat>, +e: R.Edit, -rest: List<&2, R.Edit>, l: R.Land, r: R.Outcome, lg: ap.LG(b, h, e, l), ih: ap.Pairs(b, h, rest, r)) -> ap.Pairs(b, h, e <> rest, RbSpec.land_all.of(l, r)):
  match l:
    case R.Lands{+f}:
      match r:
        case R.Rebased{+fs}:
          LR.rb.and_t(Bool.and(RbSpec.same(RbSpec.edit_lines(f), RbSpec.edit_lines(e)), RbSpec.same(RbSpec.region(h, f), RbSpec.region(b, e))), RbSpec.pairs(b, h, rest, fs), lg, ih)
        case R.Conflict{w}:
          Unit{}
    case R.Fails{w}:
      Unit{}

def ap.all(es: List<&2, R.Edit>, +b: List<&2, Nat>, +h: List<&2, Nat>, +i: Nat) -> ap.Pairs(b, h, es, RbSpec.land_all(es, b, h, i)):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      ap.all.of(b, h, e, rest, RbSpec.land(b, h, e, i), RbSpec.land_all(rest, b, h, 1n+i), ap.land(b, h, e, i), ap.all(rest, b, h, 1n+i))

def ap.cr.of(+b: List<&2, Nat>, +h: List<&2, Nat>, -es: List<&2, R.Edit>, +fs: List<&2, R.Edit>, c: Maybe<&2, Nat>, ec: {RbSpec.bad(fs, List.length(&2, Nat, h)) == c : Maybe<&2, Nat>}, p: {RbSpec.pairs(b, h, es, fs) == True{} : Bool}) -> ap.Good(b, h, es, RbSpec.crossed.of(c, fs)):
  match c:
    case None{}:
      %Equal.sym(Maybe<&2, Nat>, RbSpec.bad(fs, List.length(&2, Nat, h)), None{}, ec) : {Bool.and(RbSpec.none(_), RbSpec.pairs(b, h, es, fs)) == True{} : Bool}
      p
    case Some{i}:
      Unit{}

def ap.crossed(+b: List<&2, Nat>, +h: List<&2, Nat>, -es: List<&2, R.Edit>, o: R.Outcome, p: ap.Pairs(b, h, es, o)) -> ap.Good(b, h, es, RbSpec.crossed(o, List.length(&2, Nat, h))):
  match o:
    case R.Rebased{+fs}:
      ap.cr.of(b, h, es, fs, RbSpec.bad(fs, List.length(&2, Nat, h)), {==}, p)
    case R.Conflict{w}:
      Unit{}

# every answer of the spec is good
def ap.of(+b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>, c: Maybe<&2, Nat>, ec: {RbSpec.bad(es, List.length(&2, Nat, b)) == c : Maybe<&2, Nat>}, q: Bool, eq: {RbSpec.same(b, h) == q : Bool}) -> ap.Good(b, h, es, RbSpec.rebase.of(c, q, b, h, es)):
  match c:
    case Some{i}:
      Unit{}
    case None{}:
      match q:
        case True{}:
          %LR.rb.same_eq(b, h, eq) : {Bool.and(RbSpec.none(RbSpec.bad(es, List.length(&2, Nat, _))), RbSpec.pairs(b, _, es, es)) == True{} : Bool}
          %Equal.sym(Maybe<&2, Nat>, RbSpec.bad(es, List.length(&2, Nat, b)), None{}, ec) : {Bool.and(RbSpec.none(_), RbSpec.pairs(b, b, es, es)) == True{} : Bool}
          LR.rb.pairs_refl(b, es)
        case False{}:
          ap.crossed(b, h, es, RbSpec.land_all(es, b, h, 0n), ap.all(es, b, h, 0n))

def Rebase.rebase_result_applies(b, h, es, fs, got):
  +eq = Equal.trans(R.Outcome, RbSpec.rebase(b, h, es), R.rebase(b, h, es), R.Rebased{fs}, Equal.sym(R.Outcome, R.rebase(b, h, es), RbSpec.rebase(b, h, es), Rebase.rebase_refines(b, h, es)), got)
  %eq : ap.Good(b, h, es, _)
  ap.of(b, h, es, RbSpec.bad(es, List.length(&2, Nat, b)), {==}, RbSpec.same(b, h), {==})
