# eukhe: a lemma of the proofs of area rebase: the rule (bend/rebase.bend)
# computes what the spec (spec/harness/rebase.bend) computes, rr.refines.
# No law states it: the spec restates the rule's steps (S4's step order
# and landing offset are the rule's), so the laws state requirements
# instead, and their proofs reason on the spec through this lemma.
#
# PROOF: step by step. The model's lazy prefix test is the spec's
# (rr.fits); its scan, stopping at the second copy, classifies the spec's
# list of copies (rr.scan, rr.hits); one context's verdict on those classes
# is the spec's step on the lists (rr.at), so the contexts agree by
# induction on the fuel (rr.go) and so do the edits (rr.land, rr.all). Rule
# 1: the model's floor test is the spec's comparison with the previous edit
# once that edit passed (rr.fl, rr.ck_some, rr.ck_none). The rest follows
# the same branches (rr.crossed, rr.rebase).

import Base
import ../../../bend/rebase.bend as R
import ../../../spec/harness/rebase.bend as RbSpec
import ../base.bend as LR

# Windows: copies
# ---------------

def rr.fits.at(q: Bool, -wt: List<&2, Nat>, -yt: List<&2, Nat>, ih: {R.fits(wt, yt) == RbSpec.starts(wt, yt) : Bool}) -> {R.when(Bool, q, u => R.fits(wt, yt), u => False{}) == Bool.and(q, RbSpec.starts(wt, yt)) : Bool}:
  match q:
    case True{}:
      ih
    case False{}:
      {==}

# the model's prefix test is the spec's
def rr.fits(w: List<&2, Nat>, y: List<&2, Nat>) -> {R.fits(w, y) == RbSpec.starts(w, y) : Bool}:
  match w y:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{a, wt} Nil{}:
      {==}
    case Con{+a, +wt} Con{+c, +yt}:
      rr.fits.at(Nat.is_eq(a, c), wt, yt, rr.fits(wt, yt))

# the class of a list of copies: none, one, two or more
def rr.cls(l: List<&2, Nat>) -> R.Hits:
  match l:
    case Nil{}:
      R.HNone{}
    case Con{j, r}:
      match r:
        case Nil{}:
          R.HOne{j}
        case Con{k, rest}:
          R.HMany{}

# the copies after the one already found
def rr.acc(m: Maybe<&2, Nat>, l: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case None{}:
      l
    case Some{a}:
      a <> l

def rr.scan.nil(q: Bool, acc: Maybe<&2, Nat>, +j: Nat) -> {R.when(R.Hits, q, u => R.seen(acc, v => R.HOne{j}), u => R.found(acc)) == rr.cls(rr.acc(acc, RbSpec.put(q, j, Nil{}))) : R.Hits}:
  match q:
    case True{}:
      match acc:
        case None{}:
          {==}
        case Some{a}:
          {==}
    case False{}:
      match acc:
        case None{}:
          {==}
        case Some{a}:
          {==}

def rr.scan.con(q: Bool, acc: Maybe<&2, Nat>, +j: Nat, -t: List<&2, Nat>, -w: List<&2, Nat>,
  ih1: {R.scan(t, w, 1n+j, Some{j}) == rr.cls(rr.acc(Some{j}, RbSpec.copies.go(t, w, 1n+j))) : R.Hits},
  ih2: {R.scan(t, w, 1n+j, acc) == rr.cls(rr.acc(acc, RbSpec.copies.go(t, w, 1n+j))) : R.Hits})
  -> {R.when(R.Hits, q, u => R.seen(acc, v => R.scan(t, w, 1n+j, Some{j})), u => R.scan(t, w, 1n+j, acc)) == rr.cls(rr.acc(acc, RbSpec.put(q, j, RbSpec.copies.go(t, w, 1n+j)))) : R.Hits}:
  match q:
    case True{}:
      match acc:
        case None{}:
          ih1
        case Some{a}:
          {==}
    case False{}:
      ih2

# the scan from the copy at acc classifies the spec's copies after it
def rr.scan(x: List<&2, Nat>, +w: List<&2, Nat>, +j: Nat, +acc: Maybe<&2, Nat>) -> {R.scan(x, w, j, acc) == rr.cls(rr.acc(acc, RbSpec.copies.go(x, w, j))) : R.Hits}:
  match x:
    case Nil{}:
      %Equal.sym(Bool, R.fits(w, Nil{}), RbSpec.starts(w, Nil{}), rr.fits(w, Nil{})) : {R.when(R.Hits, _, u => R.seen(acc, v => R.HOne{j}), u => R.found(acc)) == rr.cls(rr.acc(acc, RbSpec.put(RbSpec.starts(w, Nil{}), j, Nil{}))) : R.Hits}
      rr.scan.nil(RbSpec.starts(w, Nil{}), acc, j)
    case Con{+c, +t}:
      %Equal.sym(Bool, R.fits(w, Con{c, t}), RbSpec.starts(w, Con{c, t}), rr.fits(w, Con{c, t})) : {R.when(R.Hits, _, u => R.seen(acc, v => R.scan(t, w, 1n+j, Some{j})), u => R.scan(t, w, 1n+j, acc)) == rr.cls(rr.acc(acc, RbSpec.put(RbSpec.starts(w, Con{c, t}), j, RbSpec.copies.go(t, w, 1n+j)))) : R.Hits}
      rr.scan.con(RbSpec.starts(w, Con{c, t}), acc, j, t, w, rr.scan(t, w, 1n+j, Some{j}), rr.scan(t, w, 1n+j, acc))

# the model's copies of a window are the class of the spec's, anchored
def rr.hits(+x: List<&2, Nat>, la: Bool, +w: List<&2, Nat>, ha: Bool) -> {R.hits(x, la, w, ha) == R.anchor(rr.cls(RbSpec.copies(x, w)), la, ha, List.length(&2, Nat, w), List.length(&2, Nat, x)) : R.Hits}:
  %Equal.sym(R.Hits, R.scan(x, w, 0n, None{}), rr.cls(RbSpec.copies(x, w)), rr.scan(x, w, 0n, None{})) : {R.anchor(_, la, ha, List.length(&2, Nat, w), List.length(&2, Nat, x)) == R.anchor(rr.cls(RbSpec.copies(x, w)), la, ha, List.length(&2, Nat, w), List.length(&2, Nat, x)) : R.Hits}
  {==}

# the anchors are the spec's
def rr.placed(la: Bool, ha: Bool, +j: Nat, +wl: Nat, +xl: Nat) -> {R.placed(la, ha, j, wl, xl) == RbSpec.sits(la, ha, j, wl, xl) : Bool}:
  match la ha:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# One context
# -----------

def rr.at.pick(q: Bool, +j: Nat, +x: Nat, +off: Nat, +len: Nat, ls: List<&2, Nat>, +i: Nat, -nm: Unit -> R.Land, -ns: Unit -> R.Land, e: {nm(Unit{}) == ns(Unit{}) : R.Land})
  -> {R.land.at(R.HOne{j}, R.keep(q, x), off, len, ls, i, nm) == RbSpec.step.pick(q, R.Edit{Nat.add(j, off), Nat.add(Nat.add(j, off), len), ls}, ns) : R.Land}:
  match q:
    case True{}:
      {==}
    case False{}:
      e

def rr.at.base(cb: List<&2, Nat>, +la: Bool, +ha: Bool, +j: Nat, +wl: Nat, +bl: Nat, +off: Nat, +len: Nat, ls: List<&2, Nat>, +i: Nat, -nm: Unit -> R.Land, -ns: Unit -> R.Land, e: {nm(Unit{}) == ns(Unit{}) : R.Land})
  -> {R.land.at(R.HOne{j}, R.anchor(rr.cls(cb), la, ha, wl, bl), off, len, ls, i, nm) == RbSpec.step.base(cb, la, ha, wl, bl, R.Edit{Nat.add(j, off), Nat.add(Nat.add(j, off), len), ls}, ns) : R.Land}:
  match cb:
    case Nil{}:
      e
    case Con{+x, more}:
      match more:
        case Nil{}:
          %Equal.sym(Bool, R.placed(la, ha, x, wl, bl), RbSpec.sits(la, ha, x, wl, bl), rr.placed(la, ha, x, wl, bl)) : {R.land.at(R.HOne{j}, R.keep(_, x), off, len, ls, i, nm) == RbSpec.step.pick(RbSpec.sits(la, ha, x, wl, bl), R.Edit{Nat.add(j, off), Nat.add(Nat.add(j, off), len), ls}, ns) : R.Land}
          rr.at.pick(RbSpec.sits(la, ha, x, wl, bl), j, x, off, len, ls, i, nm, ns, e)
        case Con{y, rest}:
          e

def rr.at.one(q: Bool, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +j: Nat, +wl: Nat, +bl: Nat, +off: Nat, +len: Nat, ls: List<&2, Nat>, +i: Nat, -nm: Unit -> R.Land, -ns: Unit -> R.Land, e: {nm(Unit{}) == ns(Unit{}) : R.Land})
  -> {R.land.at(R.keep(q, j), R.anchor(rr.cls(cb), la, ha, wl, bl), off, len, ls, i, nm) == RbSpec.step.one(q, cb, la, ha, wl, bl, R.Edit{Nat.add(j, off), Nat.add(Nat.add(j, off), len), ls}, i, ns) : R.Land}:
  match q:
    case True{}:
      rr.at.base(cb, la, ha, j, wl, bl, off, len, ls, i, nm, ns, e)
    case False{}:
      {==}

# one context's verdict on the classes is the spec's step on the lists
def rr.at(ch: List<&2, Nat>, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +hl: Nat, +bl: Nat, +off: Nat, +len: Nat, ls: List<&2, Nat>, +i: Nat, -nm: Unit -> R.Land, -ns: Unit -> R.Land, e: {nm(Unit{}) == ns(Unit{}) : R.Land})
  -> {R.land.at(R.anchor(rr.cls(ch), la, ha, wl, hl), R.anchor(rr.cls(cb), la, ha, wl, bl), off, len, ls, i, nm) == RbSpec.step(ch, cb, la, ha, wl, hl, bl, off, len, ls, i, ns) : R.Land}:
  match ch:
    case Nil{}:
      {==}
    case Con{+j, more}:
      match more:
        case Nil{}:
          %Equal.sym(Bool, R.placed(la, ha, j, wl, hl), RbSpec.sits(la, ha, j, wl, hl), rr.placed(la, ha, j, wl, hl)) : {R.land.at(R.keep(_, j), R.anchor(rr.cls(cb), la, ha, wl, bl), off, len, ls, i, nm) == RbSpec.step.one(RbSpec.sits(la, ha, j, wl, hl), cb, la, ha, wl, bl, R.Edit{Nat.add(j, off), Nat.add(Nat.add(j, off), len), ls}, i, ns) : R.Land}
          rr.at.one(RbSpec.sits(la, ha, j, wl, hl), cb, la, ha, j, wl, bl, off, len, ls, i, nm, ns, e)
        case Con{k, rest}:
          e

def rr.win(w: R.Win, +b: List<&2, Nat>, +h: List<&2, Nat>, ls: List<&2, Nat>, +i: Nat, -nm: Unit -> R.Land, -ns: Unit -> R.Land, e: {nm(Unit{}) == ns(Unit{}) : R.Land})
  -> {R.land.win(w, b, h, ls, i, nm) == RbSpec.step.win(w, b, h, ls, i, ns) : R.Land}:
  match w:
    case R.Win{+la, +lw, +ha, +off, +len}:
      %Equal.sym(R.Hits, R.hits(h, la, lw, ha), R.anchor(rr.cls(RbSpec.copies(h, lw)), la, ha, List.length(&2, Nat, lw), List.length(&2, Nat, h)), rr.hits(h, la, lw, ha)) : {R.land.at(_, R.hits(b, la, lw, ha), off, len, ls, i, nm) == RbSpec.step.win(R.Win{la, lw, ha, off, len}, b, h, ls, i, ns) : R.Land}
      %Equal.sym(R.Hits, R.hits(b, la, lw, ha), R.anchor(rr.cls(RbSpec.copies(b, lw)), la, ha, List.length(&2, Nat, lw), List.length(&2, Nat, b)), rr.hits(b, la, lw, ha)) : {R.land.at(R.anchor(rr.cls(RbSpec.copies(h, lw)), la, ha, List.length(&2, Nat, lw), List.length(&2, Nat, h)), _, off, len, ls, i, nm) == RbSpec.step.win(R.Win{la, lw, ha, off, len}, b, h, ls, i, ns) : R.Land}
      rr.at(RbSpec.copies(h, lw), RbSpec.copies(b, lw), la, ha, List.length(&2, Nat, lw), List.length(&2, Nat, h), List.length(&2, Nat, b), off, len, ls, i, nm, ns, e)

# the contexts agree, by induction on the fuel
def rr.go(fuel: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +ls: List<&2, Nat>, +k: Nat, +i: Nat) -> {R.land.go(fuel, b, h, s, t, ls, k, i) == RbSpec.land.go(fuel, b, h, s, t, ls, k, i) : R.Land}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      rr.win(R.window(b, s, t, k), b, h, ls, i, u => R.land.go(p, b, h, s, t, ls, 1n+k, i), u => RbSpec.land.go(p, b, h, s, t, ls, 1n+k, i), rr.go(p, b, h, s, t, ls, 1n+k, i))

def rr.first.of(q: Bool) -> {R.first.of(q) == RbSpec.first.of(q) : Nat}:
  match q:
    case True{}:
      {==}
    case False{}:
      {==}

def rr.first(+s: Nat, +t: Nat) -> {R.first(s, t) == RbSpec.first(s, t) : Nat}:
  rr.first.of(Nat.is_eq(s, t))

def rr.land(+b: List<&2, Nat>, +h: List<&2, Nat>, e: R.Edit, +i: Nat) -> {R.land(b, h, e, i) == RbSpec.land(b, h, e, i) : R.Land}:
  match e:
    case R.Edit{+s, +t, +ls}:
      %Equal.sym(Nat, R.first(s, t), RbSpec.first(s, t), rr.first(s, t)) : {R.land.go(Nat.sub(1n+R.ctx(), _), b, h, s, t, ls, _, i) == RbSpec.land(b, h, R.Edit{s, t, ls}, i) : R.Land}
      rr.go(Nat.sub(1n+RbSpec.ctx(), RbSpec.first(s, t)), b, h, s, t, ls, RbSpec.first(s, t), i)

def rr.all.at(l: R.Land, r: R.Outcome) -> {R.land_all.at(l, r) == RbSpec.land_all.of(l, r) : R.Outcome}:
  match l:
    case R.Lands{f}:
      match r:
        case R.Rebased{fs}:
          {==}
        case R.Conflict{w}:
          {==}
    case R.Fails{w}:
      {==}

def rr.all(es: List<&2, R.Edit>, +b: List<&2, Nat>, +h: List<&2, Nat>, +i: Nat) -> {R.land_all(es, b, h, i) == RbSpec.land_all(es, b, h, i) : R.Outcome}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      %Equal.sym(R.Land, R.land(b, h, e, i), RbSpec.land(b, h, e, i), rr.land(b, h, e, i)) : {R.land_all.at(_, R.land_all(rest, b, h, 1n+i)) == RbSpec.land_all.of(RbSpec.land(b, h, e, i), RbSpec.land_all(rest, b, h, 1n+i)) : R.Outcome}
      %Equal.sym(R.Outcome, R.land_all(rest, b, h, 1n+i), RbSpec.land_all(rest, b, h, 1n+i), rr.all(rest, b, h, 1n+i)) : {R.land_all.at(RbSpec.land(b, h, e, i), _) == RbSpec.land_all.of(RbSpec.land(b, h, e, i), RbSpec.land_all(rest, b, h, 1n+i)) : R.Outcome}
      rr.all.at(RbSpec.land(b, h, e, i), RbSpec.land_all(rest, b, h, 1n+i))

# Rule 1
# ------

def rr.lt_and.of(+a: Nat, +b: Nat, q: Bool, eq: {Nat.is_lt(a, b) == q : Bool}) -> {q == Bool.and(q, Nat.is_le(a, b)) : Bool}:
  match q:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(a, b), True{}, LR.rb.lt_le(a, b, eq)) : {True{} == Bool.and(True{}, _) : Bool}
      {==}
    case False{}:
      {==}

def rr.lt_and(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == Bool.and(Nat.is_lt(a, b), Nat.is_le(a, b)) : Bool}:
  rr.lt_and.of(a, b, Nat.is_lt(a, b), {==})

def rr.fl.past(+ps: Nat, +pe: Nat, +s: Nat, lt: {Nat.is_lt(ps, pe) == True{} : Bool}, q: Bool, eq: {Nat.is_le(pe, s) == q : Bool}) -> {q == Bool.and(Nat.is_lt(ps, s), q) : Bool}:
  match q:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(ps, s), True{}, LR.rb.lt_le_trans(ps, pe, s, lt, eq)) : {True{} == Bool.and(_, True{}) : Bool}
      {==}
    case False{}:
      Equal.sym(Bool, Bool.and(Nat.is_lt(ps, s), False{}), False{}, LR.rb.and_false_r(Nat.is_lt(ps, s)))

def rr.fl.of(+ps: Nat, +pe: Nat, +s: Nat, le: {Nat.is_le(ps, pe) == True{} : Bool}, q: Bool, eq: {Nat.is_eq(ps, pe) == q : Bool}) -> {Nat.is_le(R.floor.of(q, pe), s) == Bool.and(Nat.is_lt(ps, s), Nat.is_le(pe, s)) : Bool}:
  match q:
    case True{}:
      %Equal.sym(Nat, ps, pe, LR.rb.eq_true(ps, pe, eq)) : {Nat.is_le(1n+pe, s) == Bool.and(Nat.is_lt(_, s), Nat.is_le(pe, s)) : Bool}
      %Equal.sym(Bool, Nat.is_le(1n+pe, s), Nat.is_lt(pe, s), LR.rb.le_succ(pe, s)) : {_ == Bool.and(Nat.is_lt(pe, s), Nat.is_le(pe, s)) : Bool}
      rr.lt_and(pe, s)
    case False{}:
      rr.fl.past(ps, pe, s, LR.rb.le_ne_lt(ps, pe, le, eq), Nat.is_le(pe, s), {==})

# past an edit (ps, pe) with ps <= pe, the floor test is the spec's
def rr.fl(+ps: Nat, +pe: Nat, +s: Nat, le: {Nat.is_le(ps, pe) == True{} : Bool}) -> {Nat.is_le(R.floor(ps, pe), s) == Bool.and(Nat.is_lt(ps, s), Nat.is_le(pe, s)) : Bool}:
  rr.fl.of(ps, pe, s, le, Nat.is_eq(ps, pe), {==})

def rr.ck.at(q: Bool, +i: Nat, -rm: Maybe<&2, Nat>, -rs: Maybe<&2, Nat>, h: {q == True{} : Bool} -> {rm == rs : Maybe<&2, Nat>}) -> {R.check.at(q, i, rm) == RbSpec.bad.of(q, i, rs) : Maybe<&2, Nat>}:
  match q:
    case True{}:
      h({==})
    case False{}:
      {==}

# after an edit (ps, pe) that passed, the floor's check is the spec's
def rr.ck_some(es: List<&2, R.Edit>, +n: Nat, +i: Nat, +ps: Nat, +pe: Nat, +pl: List<&2, Nat>, le: {Nat.is_le(ps, pe) == True{} : Bool}) -> {R.check.go(es, n, R.floor(ps, pe), i) == RbSpec.bad.go(es, Some{R.Edit{ps, pe, pl}}, n, i) : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case Con{e, rest}:
      match e:
        case R.Edit{+s, +t, +ls}:
          +x = Bool.and(Nat.is_le(s, t), Nat.is_le(t, n))
          +p = Bool.and(Nat.is_lt(ps, s), Nat.is_le(pe, s))
          %Equal.sym(Bool, Nat.is_le(R.floor(ps, pe), s), p, rr.fl(ps, pe, s, le)) : {R.check.at(Bool.and(_, x), i, R.check.go(rest, n, R.floor(s, t), 1n+i)) == RbSpec.bad.of(Bool.and(x, p), i, RbSpec.bad.go(rest, Some{R.Edit{s, t, ls}}, n, 1n+i)) : Maybe<&2, Nat>}
          %Equal.sym(Bool, Bool.and(p, x), Bool.and(x, p), LR.rb.and_comm(p, x)) : {R.check.at(_, i, R.check.go(rest, n, R.floor(s, t), 1n+i)) == RbSpec.bad.of(Bool.and(x, p), i, RbSpec.bad.go(rest, Some{R.Edit{s, t, ls}}, n, 1n+i)) : Maybe<&2, Nat>}
          rr.ck.at(Bool.and(x, p), i, R.check.go(rest, n, R.floor(s, t), 1n+i), RbSpec.bad.go(rest, Some{R.Edit{s, t, ls}}, n, 1n+i), qt => rr.ck_some(rest, n, 1n+i, s, t, ls, LR.rb.and_l(Nat.is_le(s, t), Nat.is_le(t, n), LR.rb.and_l(x, p, qt))))

# from the start, the check is the spec's
def rr.ck_none(es: List<&2, R.Edit>, +n: Nat, +i: Nat) -> {R.check.go(es, n, 0n, i) == RbSpec.bad.go(es, None{}, n, i) : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case Con{e, rest}:
      match e:
        case R.Edit{+s, +t, +ls}:
          +x = Bool.and(Nat.is_le(s, t), Nat.is_le(t, n))
          %Equal.sym(Bool, Nat.is_le(0n, s), True{}, LR.rb.le_zero(s)) : {R.check.at(Bool.and(_, x), i, R.check.go(rest, n, R.floor(s, t), 1n+i)) == RbSpec.bad.of(Bool.and(x, True{}), i, RbSpec.bad.go(rest, Some{R.Edit{s, t, ls}}, n, 1n+i)) : Maybe<&2, Nat>}
          %Equal.sym(Bool, Bool.and(x, True{}), x, LR.rb.and_true_r(x)) : {R.check.at(x, i, R.check.go(rest, n, R.floor(s, t), 1n+i)) == RbSpec.bad.of(_, i, RbSpec.bad.go(rest, Some{R.Edit{s, t, ls}}, n, 1n+i)) : Maybe<&2, Nat>}
          rr.ck.at(x, i, R.check.go(rest, n, R.floor(s, t), 1n+i), RbSpec.bad.go(rest, Some{R.Edit{s, t, ls}}, n, 1n+i), qt => rr.ck_some(rest, n, 1n+i, s, t, ls, LR.rb.and_l(Nat.is_le(s, t), Nat.is_le(t, n), qt)))

def rr.check(es: List<&2, R.Edit>, +n: Nat) -> {R.check(es, n) == RbSpec.bad(es, n) : Maybe<&2, Nat>}:
  rr.ck_none(es, n, 0n)

# The rest
# --------

def rr.same(a: List<&2, Nat>, b: List<&2, Nat>) -> {R.same(a, b) == RbSpec.same(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      {==}
    case Con{x, xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(x, y), z), R.same(xs, ys), RbSpec.same(xs, ys), rr.same(xs, ys))

def rr.crossed.at(c: Maybe<&2, Nat>, fs: List<&2, R.Edit>) -> {R.crossed.at(c, fs) == RbSpec.crossed.of(c, fs) : R.Outcome}:
  match c:
    case None{}:
      {==}
    case Some{i}:
      {==}

def rr.crossed(o: R.Outcome, +m: Nat) -> {R.crossed(o, m) == RbSpec.crossed(o, m) : R.Outcome}:
  match o:
    case R.Rebased{+fs}:
      %Equal.sym(Maybe<&2, Nat>, R.check(fs, m), RbSpec.bad(fs, m), rr.check(fs, m)) : {R.crossed.at(_, fs) == RbSpec.crossed.of(RbSpec.bad(fs, m), fs) : R.Outcome}
      rr.crossed.at(RbSpec.bad(fs, m), fs)
    case R.Conflict{w}:
      {==}

def rr.rebase.at(c: Maybe<&2, Nat>, eq: Bool, +b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> {R.rebase.at(c, eq, b, h, es) == RbSpec.rebase.of(c, eq, b, h, es) : R.Outcome}:
  match c:
    case Some{i}:
      {==}
    case None{}:
      match eq:
        case True{}:
          {==}
        case False{}:
          %Equal.sym(R.Outcome, R.land_all(es, b, h, 0n), RbSpec.land_all(es, b, h, 0n), rr.all(es, b, h, 0n)) : {R.crossed(_, List.length(&2, Nat, h)) == RbSpec.crossed(RbSpec.land_all(es, b, h, 0n), List.length(&2, Nat, h)) : R.Outcome}
          rr.crossed(RbSpec.land_all(es, b, h, 0n), List.length(&2, Nat, h))

def rr.refines(+b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> {R.rebase(b, h, es) == RbSpec.rebase(b, h, es) : R.Outcome}:
  %Equal.sym(Maybe<&2, Nat>, R.check(es, List.length(&2, Nat, b)), RbSpec.bad(es, List.length(&2, Nat, b)), rr.check(es, List.length(&2, Nat, b))) : {R.rebase.at(_, R.same(b, h), b, h, es) == RbSpec.rebase(b, h, es) : R.Outcome}
  %Equal.sym(Bool, R.same(b, h), RbSpec.same(b, h), rr.same(b, h)) : {R.rebase.at(RbSpec.bad(es, List.length(&2, Nat, b)), _, b, h, es) == RbSpec.rebase(b, h, es) : R.Outcome}
  rr.rebase.at(RbSpec.bad(es, List.length(&2, Nat, b)), RbSpec.same(b, h), b, h, es)
