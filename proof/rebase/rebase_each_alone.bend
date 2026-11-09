# eukhe: the proof of LAW rebase_each_alone
#
# PROOF: the rule is the spec's (rr.refines); the edits are valid and the
# head differs, so the answer is the crossing check of the edits landed one
# by one (RbSpec.land_all). Each edit of valid edits is valid alone
# (ea.split, ea.ok_alone), so its own rebase is its landing at index 0
# (ea.single): a landed edit lies within the head (ea.lw.*: the window's
# one copy in the head starts at most at its end, ea.cp_le, and its lines
# fit there, ea.fit), so the crossing check of that one edit keeps it. A
# landing names its edit's index only in a refusal (ea.rl.*), so landing
# the i-th edit is landing it alone with the refusal renamed (ea.at); by
# induction on the edits (ea.go) both sides land the same edits.

import Base
import ../../bend/rebase.bend as R
import ../../spec/harness/rebase.bend as RbSpec
import ../../laws/rebase.bend as Rebase
import ./base.bend as LR
import ./base/refines.bend as LRR

# One edit alone
# --------------

# a landing as the rebase of its edit alone answers it
def ea.one(l: R.Land) -> R.Outcome:
  match l:
    case R.Lands{f}:
      R.Rebased{[f]}
    case R.Fails{w}:
      R.Conflict{w}

# a landing of the 0-th edit as that of the i-th
def ea.rel(l: R.Land, +i: Nat) -> R.Land:
  match l:
    case R.Lands{f}:
      R.Lands{f}
    case R.Fails{w}:
      R.Fails{Rebase.rb_at(w, i)}

# the edit landed lies within the head: sorted and apart there alone
def ea.LW(+h: List<&2, Nat>, l: R.Land) -> Type:
  match l:
    case R.Lands{f}:
      {RbSpec.bad([f], List.length(&2, Nat, h)) == None{} : Maybe<&2, Nat>}
    case R.Fails{w}:
      Unit

# Lines
# -----

def ea.MI(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def ea.some_none(-G: Type, -i: Nat, e: {Some{i} == None{} : Maybe<&2, Nat>}) -> G:
  %e : ea.MI(_, G)
  Unit{}

def ea.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), ea.add_succ(p, b))

# a prefix of a prefix of y is a prefix of y
def ea.pre(u: List<&2, Nat>, +v: List<&2, Nat>, y: List<&2, Nat>, e: {RbSpec.starts(List.append(&2, Nat, u, v), y) == True{} : Bool}) -> {RbSpec.starts(u, y) == True{} : Bool}:
  match u:
    case Nil{}:
      {==}
    case Con{+x, +ut}:
      match y:
        case Nil{}:
          LR.rb.absurdF({RbSpec.starts(x <> ut, Nil{}) == True{} : Bool}, e)
        case Con{+d, +yt}:
          +e0 = e
          LR.rb.and_t(Nat.is_eq(x, d), RbSpec.starts(ut, yt), LR.rb.and_l(Nat.is_eq(x, d), RbSpec.starts(List.append(&2, Nat, ut, v), yt), e0), ea.pre(ut, v, yt, LR.rb.and_r(Nat.is_eq(x, d), RbSpec.starts(List.append(&2, Nat, ut, v), yt), e0)))

# lines u that start h at j, j within h, end within h
def ea.fit(+u: List<&2, Nat>, j: Nat, h: List<&2, Nat>, e: {RbSpec.starts(u, List.drop(&2, Nat, h, j)) == True{} : Bool}, le: {Nat.is_le(j, List.length(&2, Nat, h)) == True{} : Bool}) -> {Nat.is_le(Nat.add(j, List.length(&2, Nat, u)), List.length(&2, Nat, h)) == True{} : Bool}:
  match j:
    case 0n:
      match h:
        case Nil{}:
          LR.rb.st.len(u, Nil{}, e)
        case Con{+d, +ht}:
          LR.rb.st.len(u, d <> ht, e)
    case 1n+q:
      match h:
        case Nil{}:
          LR.rb.absurdF({Nat.is_le(Nat.add(1n+q, List.length(&2, Nat, u)), 0n) == True{} : Bool}, le)
        case Con{d, ht}:
          ea.fit(u, q, ht, e, le)

def ea.cp_le.nil(q: Bool, +j0: Nat, +j: Nat, -l: List<&2, Nat>, e: {RbSpec.put(q, j0, Nil{}) == j <> l : List<&2, Nat>}) -> {Nat.is_le(j, Nat.add(j0, 0n)) == True{} : Bool}:
  match q:
    case True{}:
      %Equal.cong(List<&2, Nat>, Nat, LR.rb.hd, j0 <> Nil{}, j <> l, e) : {Nat.is_le(_, Nat.add(j0, 0n)) == True{} : Bool}
      LR.rb.le_add(j0, 0n)
    case False{}:
      LR.rb.nil_con({Nat.is_le(j, Nat.add(j0, 0n)) == True{} : Bool}, j, l, e)

def ea.cp_le.con(q: Bool, +j0: Nat, +j: Nat, -l: List<&2, Nat>, +t: List<&2, Nat>, -w: List<&2, Nat>,
  e: {RbSpec.put(q, j0, RbSpec.copies.go(t, w, 1n+j0)) == j <> l : List<&2, Nat>},
  ih: {RbSpec.copies.go(t, w, 1n+j0) == j <> l : List<&2, Nat>} -> {Nat.is_le(j, Nat.add(1n+j0, List.length(&2, Nat, t))) == True{} : Bool})
  -> {Nat.is_le(j, Nat.add(j0, 1n+List.length(&2, Nat, t))) == True{} : Bool}:
  match q:
    case True{}:
      %Equal.cong(List<&2, Nat>, Nat, LR.rb.hd, j0 <> RbSpec.copies.go(t, w, 1n+j0), j <> l, e) : {Nat.is_le(_, Nat.add(j0, 1n+List.length(&2, Nat, t))) == True{} : Bool}
      LR.rb.le_add(j0, 1n+List.length(&2, Nat, t))
    case False{}:
      %Equal.sym(Nat, Nat.add(j0, 1n+List.length(&2, Nat, t)), 1n+Nat.add(j0, List.length(&2, Nat, t)), ea.add_succ(j0, List.length(&2, Nat, t))) : {Nat.is_le(j, _) == True{} : Bool}
      ih(e)

# a copy found in x (x being the lines from j0 on) is at most at x's end
def ea.cp_le(x: List<&2, Nat>, +w: List<&2, Nat>, +j0: Nat, +j: Nat, +l: List<&2, Nat>, e: {RbSpec.copies.go(x, w, j0) == j <> l : List<&2, Nat>}) -> {Nat.is_le(j, Nat.add(j0, List.length(&2, Nat, x))) == True{} : Bool}:
  match x:
    case Nil{}:
      ea.cp_le.nil(RbSpec.starts(w, Nil{}), j0, j, l, e)
    case Con{+c, +t}:
      ea.cp_le.con(RbSpec.starts(w, c <> t), j0, j, l, t, w, e, e2 => ea.cp_le(t, w, 1n+j0, j, l, e2))

# the edit landed at the head's one copy of its window lies within the head
def ea.lw.land(+lc: List<&2, Nat>, +rg: List<&2, Nat>, +rc: List<&2, Nat>, +h: List<&2, Nat>, +j: Nat, +ls: List<&2, Nat>,
  ech: {RbSpec.copies(h, List.append(&2, Nat, lc, List.append(&2, Nat, rg, rc))) == [j] : List<&2, Nat>})
  -> {RbSpec.bad([R.Edit{Nat.add(j, List.length(&2, Nat, lc)), Nat.add(Nat.add(j, List.length(&2, Nat, lc)), List.length(&2, Nat, rg)), ls}], List.length(&2, Nat, h)) == None{} : Maybe<&2, Nat>}:
  +w = List.append(&2, Nat, rg, rc)
  +a = Nat.add(j, List.length(&2, Nat, lc))
  +e0 = ech
  +st0 = LR.rb.cp.one(h, List.append(&2, Nat, lc, w), j, e0)
  +jle = ea.cp_le(h, List.append(&2, Nat, lc, w), 0n, j, Nil{}, e0)
  +a1 = ea.fit(lc, j, h, ea.pre(lc, w, List.drop(&2, Nat, h, j), st0), jle)
  +st1 = LR.rb.st.app(lc, w, List.drop(&2, Nat, h, j), st0)
  +st2 = Equal.trans(Bool, RbSpec.starts(w, List.drop(&2, Nat, h, a)), RbSpec.starts(w, List.drop(&2, Nat, List.drop(&2, Nat, h, j), List.length(&2, Nat, lc))), True{}, Equal.cong(List<&2, Nat>, Bool, z => RbSpec.starts(w, z), List.drop(&2, Nat, h, a), List.drop(&2, Nat, List.drop(&2, Nat, h, j), List.length(&2, Nat, lc)), Equal.sym(List<&2, Nat>, List.drop(&2, Nat, List.drop(&2, Nat, h, j), List.length(&2, Nat, lc)), List.drop(&2, Nat, h, a), LR.rb.drop_drop(j, h, List.length(&2, Nat, lc)))), st1)
  +a2 = ea.fit(rg, a, h, ea.pre(rg, rc, List.drop(&2, Nat, h, a), st2), a1)
  %Equal.sym(Bool, Nat.is_le(a, Nat.add(a, List.length(&2, Nat, rg))), True{}, LR.rb.le_add(a, List.length(&2, Nat, rg))) : {RbSpec.bad.of(Bool.and(Bool.and(_, Nat.is_le(Nat.add(a, List.length(&2, Nat, rg)), List.length(&2, Nat, h))), True{}), 0n, None{}) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Nat.is_le(Nat.add(a, List.length(&2, Nat, rg)), List.length(&2, Nat, h)), True{}, a2) : {RbSpec.bad.of(Bool.and(Bool.and(True{}, _), True{}), 0n, None{}) == None{} : Maybe<&2, Nat>}
  {==}

def ea.lw.pick(q: Bool, +h: List<&2, Nat>, f: R.Edit, -next: Unit -> R.Land, lp: ea.LW(h, R.Lands{f}), ih: ea.LW(h, next(Unit{}))) -> ea.LW(h, RbSpec.step.pick(q, f, next)):
  match q:
    case True{}:
      lp
    case False{}:
      ih

def ea.lw.base(cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +bl: Nat, +h: List<&2, Nat>, f: R.Edit, -next: Unit -> R.Land, lp: ea.LW(h, R.Lands{f}), ih: ea.LW(h, next(Unit{}))) -> ea.LW(h, RbSpec.step.base(cb, la, ha, wl, bl, f, next)):
  match cb:
    case Nil{}:
      ih
    case Con{+x, more}:
      match more:
        case Nil{}:
          ea.lw.pick(RbSpec.sits(la, ha, x, wl, bl), h, f, next, lp, ih)
        case Con{y, rest}:
          ih

def ea.lw.one(q: Bool, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +bl: Nat, +h: List<&2, Nat>, f: R.Edit, +i: Nat, -next: Unit -> R.Land, lp: ea.LW(h, R.Lands{f}), ih: ea.LW(h, next(Unit{}))) -> ea.LW(h, RbSpec.step.one(q, cb, la, ha, wl, bl, f, i, next)):
  match q:
    case True{}:
      ea.lw.base(cb, la, ha, wl, bl, h, f, next, lp, ih)
    case False{}:
      Unit{}

def ea.lw.step(ch: List<&2, Nat>, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +hl: Nat, +bl: Nat, +lc: List<&2, Nat>, +rg: List<&2, Nat>, +rc: List<&2, Nat>, +h: List<&2, Nat>, +ls: List<&2, Nat>, +i: Nat, -next: Unit -> R.Land,
  ech: {RbSpec.copies(h, List.append(&2, Nat, lc, List.append(&2, Nat, rg, rc))) == ch : List<&2, Nat>},
  ih: ea.LW(h, next(Unit{})))
  -> ea.LW(h, RbSpec.step(ch, cb, la, ha, wl, hl, bl, List.length(&2, Nat, lc), List.length(&2, Nat, rg), ls, i, next)):
  match ch:
    case Nil{}:
      Unit{}
    case Con{+j, more}:
      match more:
        case Nil{}:
          +f = {R.Edit{Nat.add(j, List.length(&2, Nat, lc)), Nat.add(Nat.add(j, List.length(&2, Nat, lc)), List.length(&2, Nat, rg)), ls} : R.Edit}
          ea.lw.one(RbSpec.sits(la, ha, j, wl, hl), cb, la, ha, wl, bl, h, f, i, next, ea.lw.land(lc, rg, rc, h, j, ls, ech), ih)
        case Con{y, rest}:
          ih

def ea.lw.go(fuel: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +ls: List<&2, Nat>, +k: Nat, +i: Nat) -> ea.LW(h, RbSpec.land.go(fuel, b, h, s, t, ls, k, i)):
  match fuel:
    case 0n:
      Unit{}
    case 1n++p:
      +lo = Nat.sub(s, k)
      +lc = List.take(&2, Nat, List.drop(&2, Nat, b, lo), Nat.sub(s, lo))
      +rg = List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s))
      +rc = List.take(&2, Nat, List.drop(&2, Nat, b, t), k)
      +w = List.append(&2, Nat, lc, List.append(&2, Nat, rg, rc))
      ea.lw.step(RbSpec.copies(h, w), RbSpec.copies(b, w), Nat.is_lt(s, k), Nat.is_lt(List.length(&2, Nat, b), Nat.add(t, k)), List.length(&2, Nat, w), List.length(&2, Nat, h), List.length(&2, Nat, b), lc, rg, rc, h, ls, i, u => RbSpec.land.go(p, b, h, s, t, ls, 1n+k, i), {==}, ea.lw.go(p, b, h, s, t, ls, 1n+k, i))

def ea.lw(+b: List<&2, Nat>, +h: List<&2, Nat>, e: R.Edit, +i: Nat) -> ea.LW(h, RbSpec.land(b, h, e, i)):
  match e:
    case R.Edit{+s, +t, +ls}:
      ea.lw.go(Nat.sub(1n+RbSpec.ctx(), RbSpec.first(s, t)), b, h, s, t, ls, RbSpec.first(s, t), i)

# The index
# ---------

def ea.rl.pick(q: Bool, f: R.Edit, +i: Nat, -n0: Unit -> R.Land, -ni: Unit -> R.Land, e: {ni(Unit{}) == ea.rel(n0(Unit{}), i) : R.Land}) -> {RbSpec.step.pick(q, f, ni) == ea.rel(RbSpec.step.pick(q, f, n0), i) : R.Land}:
  match q:
    case True{}:
      {==}
    case False{}:
      e

def ea.rl.base(cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +bl: Nat, f: R.Edit, +i: Nat, -n0: Unit -> R.Land, -ni: Unit -> R.Land, e: {ni(Unit{}) == ea.rel(n0(Unit{}), i) : R.Land}) -> {RbSpec.step.base(cb, la, ha, wl, bl, f, ni) == ea.rel(RbSpec.step.base(cb, la, ha, wl, bl, f, n0), i) : R.Land}:
  match cb:
    case Nil{}:
      e
    case Con{+x, more}:
      match more:
        case Nil{}:
          ea.rl.pick(RbSpec.sits(la, ha, x, wl, bl), f, i, n0, ni, e)
        case Con{y, rest}:
          e

def ea.rl.one(q: Bool, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +bl: Nat, f: R.Edit, +i: Nat, -n0: Unit -> R.Land, -ni: Unit -> R.Land, e: {ni(Unit{}) == ea.rel(n0(Unit{}), i) : R.Land}) -> {RbSpec.step.one(q, cb, la, ha, wl, bl, f, i, ni) == ea.rel(RbSpec.step.one(q, cb, la, ha, wl, bl, f, 0n, n0), i) : R.Land}:
  match q:
    case True{}:
      ea.rl.base(cb, la, ha, wl, bl, f, i, n0, ni, e)
    case False{}:
      {==}

def ea.rl.step(ch: List<&2, Nat>, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +hl: Nat, +bl: Nat, +off: Nat, +len: Nat, ls: List<&2, Nat>, +i: Nat, -n0: Unit -> R.Land, -ni: Unit -> R.Land, e: {ni(Unit{}) == ea.rel(n0(Unit{}), i) : R.Land}) -> {RbSpec.step(ch, cb, la, ha, wl, hl, bl, off, len, ls, i, ni) == ea.rel(RbSpec.step(ch, cb, la, ha, wl, hl, bl, off, len, ls, 0n, n0), i) : R.Land}:
  match ch:
    case Nil{}:
      {==}
    case Con{+j, more}:
      match more:
        case Nil{}:
          ea.rl.one(RbSpec.sits(la, ha, j, wl, hl), cb, la, ha, wl, bl, R.Edit{Nat.add(j, off), Nat.add(Nat.add(j, off), len), ls}, i, n0, ni, e)
        case Con{y, rest}:
          e

def ea.rl.win(w: R.Win, +b: List<&2, Nat>, +h: List<&2, Nat>, ls: List<&2, Nat>, +i: Nat, -n0: Unit -> R.Land, -ni: Unit -> R.Land, e: {ni(Unit{}) == ea.rel(n0(Unit{}), i) : R.Land}) -> {RbSpec.step.win(w, b, h, ls, i, ni) == ea.rel(RbSpec.step.win(w, b, h, ls, 0n, n0), i) : R.Land}:
  match w:
    case R.Win{+la, +lw, +ha, +off, +len}:
      ea.rl.step(RbSpec.copies(h, lw), RbSpec.copies(b, lw), la, ha, List.length(&2, Nat, lw), List.length(&2, Nat, h), List.length(&2, Nat, b), off, len, ls, i, n0, ni, e)

def ea.rl.go(fuel: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +ls: List<&2, Nat>, +k: Nat, +i: Nat) -> {RbSpec.land.go(fuel, b, h, s, t, ls, k, i) == ea.rel(RbSpec.land.go(fuel, b, h, s, t, ls, k, 0n), i) : R.Land}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      ea.rl.win(RbSpec.window(b, s, t, k), b, h, ls, i, u => RbSpec.land.go(p, b, h, s, t, ls, 1n+k, 0n), u => RbSpec.land.go(p, b, h, s, t, ls, 1n+k, i), ea.rl.go(p, b, h, s, t, ls, 1n+k, i))

# landing the i-th edit is landing it alone, a refusal naming i
def ea.rl(+b: List<&2, Nat>, +h: List<&2, Nat>, e: R.Edit, +i: Nat) -> {RbSpec.land(b, h, e, i) == ea.rel(RbSpec.land(b, h, e, 0n), i) : R.Land}:
  match e:
    case R.Edit{+s, +t, +ls}:
      ea.rl.go(Nat.sub(1n+RbSpec.ctx(), RbSpec.first(s, t)), b, h, s, t, ls, RbSpec.first(s, t), i)

# Valid edits
# -----------

def ea.split.of_l(q: Bool, +i: Nat, -r: Maybe<&2, Nat>, h: {RbSpec.bad.of(q, i, r) == None{} : Maybe<&2, Nat>}) -> {q == True{} : Bool}:
  match q:
    case True{}:
      {==}
    case False{}:
      ea.some_none({False{} == True{} : Bool}, i, h)

def ea.split.of_r(q: Bool, +i: Nat, -r: Maybe<&2, Nat>, h: {RbSpec.bad.of(q, i, r) == None{} : Maybe<&2, Nat>}) -> {r == None{} : Maybe<&2, Nat>}:
  match q:
    case True{}:
      h
    case False{}:
      ea.some_none({r == None{} : Maybe<&2, Nat>}, i, h)

# the first of valid edits passes S1
def ea.split_l(+e: R.Edit, -rest: List<&2, R.Edit>, p: Maybe<&2, R.Edit>, +n: Nat, +i: Nat, h: {RbSpec.bad.go(e <> rest, p, n, i) == None{} : Maybe<&2, Nat>}) -> {RbSpec.ok(e, p, n) == True{} : Bool}:
  ea.split.of_l(RbSpec.ok(e, p, n), i, RbSpec.bad.go(rest, Some{e}, n, 1n+i), h)

# and so do the rest after it
def ea.split_r(+e: R.Edit, -rest: List<&2, R.Edit>, p: Maybe<&2, R.Edit>, +n: Nat, +i: Nat, h: {RbSpec.bad.go(e <> rest, p, n, i) == None{} : Maybe<&2, Nat>}) -> {RbSpec.bad.go(rest, Some{e}, n, 1n+i) == None{} : Maybe<&2, Nat>}:
  ea.split.of_r(RbSpec.ok(e, p, n), i, RbSpec.bad.go(rest, Some{e}, n, 1n+i), h)

# an edit that passes S1 after another is valid alone
def ea.ok_alone(e: R.Edit, -p: Maybe<&2, R.Edit>, +n: Nat, okp: {RbSpec.ok(e, p, n) == True{} : Bool}) -> {RbSpec.bad([e], n) == None{} : Maybe<&2, Nat>}:
  match e:
    case R.Edit{+s, +t, ls}:
      +x = Bool.and(Nat.is_le(s, t), Nat.is_le(t, n))
      %Equal.sym(Bool, x, True{}, LR.rb.and_l(x, RbSpec.after(p, s), okp)) : {RbSpec.bad.of(Bool.and(_, True{}), 0n, None{}) == None{} : Maybe<&2, Nat>}
      {==}

# Each edit
# ---------

def ea.single.of(l: R.Land, +h: List<&2, Nat>, wl: ea.LW(h, l)) -> {RbSpec.crossed(RbSpec.land_all.of(l, R.Rebased{Nil{}}), List.length(&2, Nat, h)) == ea.one(l) : R.Outcome}:
  match l:
    case R.Lands{f}:
      %Equal.sym(Maybe<&2, Nat>, RbSpec.bad([f], List.length(&2, Nat, h)), None{}, wl) : {RbSpec.crossed.of(_, [f]) == R.Rebased{[f]} : R.Outcome}
      {==}
    case R.Fails{w}:
      {==}

# a valid edit's own rebase is its landing alone
def ea.single(+b: List<&2, Nat>, +h: List<&2, Nat>, +e: R.Edit, ok1: {RbSpec.bad([e], List.length(&2, Nat, b)) == None{} : Maybe<&2, Nat>}, stale: {RbSpec.same(b, h) == False{} : Bool}) -> {R.rebase(b, h, [e]) == ea.one(RbSpec.land(b, h, e, 0n)) : R.Outcome}:
  %Equal.sym(R.Outcome, R.rebase(b, h, [e]), RbSpec.rebase(b, h, [e]), LRR.rr.refines(b, h, [e])) : {_ == ea.one(RbSpec.land(b, h, e, 0n)) : R.Outcome}
  %Equal.sym(Maybe<&2, Nat>, RbSpec.bad([e], List.length(&2, Nat, b)), None{}, ok1) : {RbSpec.rebase.of(_, RbSpec.same(b, h), b, h, [e]) == ea.one(RbSpec.land(b, h, e, 0n)) : R.Outcome}
  %Equal.sym(Bool, RbSpec.same(b, h), False{}, stale) : {RbSpec.rebase.of(None{}, _, b, h, [e]) == ea.one(RbSpec.land(b, h, e, 0n)) : R.Outcome}
  ea.single.of(RbSpec.land(b, h, e, 0n), h, ea.lw(b, h, e, 0n))

def ea.at(l: R.Land, +i: Nat, r: R.Outcome) -> {Rebase.rb_alone.at(ea.one(l), i, r) == RbSpec.land_all.of(ea.rel(l, i), r) : R.Outcome}:
  match l:
    case R.Lands{f}:
      match r:
        case R.Rebased{gs}:
          {==}
        case R.Conflict{w}:
          {==}
    case R.Fails{w}:
      {==}

# the edits each alone are the edits landed one by one
def ea.go(+b: List<&2, Nat>, +h: List<&2, Nat>, es: List<&2, R.Edit>, +p: Maybe<&2, R.Edit>, +i: Nat, okv: {RbSpec.bad.go(es, p, List.length(&2, Nat, b), i) == None{} : Maybe<&2, Nat>}, +stale: {RbSpec.same(b, h) == False{} : Bool}) -> {Rebase.rb_alone.go(b, h, es, i) == RbSpec.land_all(es, b, h, i) : R.Outcome}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      +ov = okv
      +ok1 = ea.split_l(e, rest, p, List.length(&2, Nat, b), i, ov)
      +okr = ea.split_r(e, rest, p, List.length(&2, Nat, b), i, ov)
      %Equal.sym(R.Outcome, Rebase.rb_alone.go(b, h, rest, 1n+i), RbSpec.land_all(rest, b, h, 1n+i), ea.go(b, h, rest, Some{e}, 1n+i, okr, stale)) : {Rebase.rb_alone.at(R.rebase(b, h, [e]), i, _) == RbSpec.land_all.of(RbSpec.land(b, h, e, i), RbSpec.land_all(rest, b, h, 1n+i)) : R.Outcome}
      %Equal.sym(R.Outcome, R.rebase(b, h, [e]), ea.one(RbSpec.land(b, h, e, 0n)), ea.single(b, h, e, ea.ok_alone(e, p, List.length(&2, Nat, b), ok1), stale)) : {Rebase.rb_alone.at(_, i, RbSpec.land_all(rest, b, h, 1n+i)) == RbSpec.land_all.of(RbSpec.land(b, h, e, i), RbSpec.land_all(rest, b, h, 1n+i)) : R.Outcome}
      %Equal.sym(R.Land, RbSpec.land(b, h, e, i), ea.rel(RbSpec.land(b, h, e, 0n), i), ea.rl(b, h, e, i)) : {Rebase.rb_alone.at(ea.one(RbSpec.land(b, h, e, 0n)), i, RbSpec.land_all(rest, b, h, 1n+i)) == RbSpec.land_all.of(_, RbSpec.land_all(rest, b, h, 1n+i)) : R.Outcome}
      ea.at(RbSpec.land(b, h, e, 0n), i, RbSpec.land_all(rest, b, h, 1n+i))

def Rebase.rebase_each_alone(b, h, es, ok, stale):
  +nb = LR.rb.none_true(RbSpec.bad(es, List.length(&2, Nat, b)), ok)
  +st = stale
  %Equal.sym(R.Outcome, R.rebase(b, h, es), RbSpec.rebase(b, h, es), LRR.rr.refines(b, h, es)) : {_ == Rebase.rb_alone(b, h, es) : R.Outcome}
  %Equal.sym(Maybe<&2, Nat>, RbSpec.bad(es, List.length(&2, Nat, b)), None{}, nb) : {RbSpec.rebase.of(_, RbSpec.same(b, h), b, h, es) == Rebase.rb_alone(b, h, es) : R.Outcome}
  %Equal.sym(Bool, RbSpec.same(b, h), False{}, st) : {RbSpec.rebase.of(None{}, _, b, h, es) == Rebase.rb_alone(b, h, es) : R.Outcome}
  %Equal.sym(R.Outcome, Rebase.rb_alone.go(b, h, es, 0n), RbSpec.land_all(es, b, h, 0n), ea.go(b, h, es, None{}, 0n, nb, st)) : {RbSpec.crossed(RbSpec.land_all(es, b, h, 0n), List.length(&2, Nat, h)) == RbSpec.crossed(_, List.length(&2, Nat, h)) : R.Outcome}
  {==}
