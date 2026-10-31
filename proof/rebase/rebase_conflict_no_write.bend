# eukhe: the proof of LAW rebase_conflict_no_write
#
# PROOF: the rule is the spec's (rebase_refines). Invalid edits are a
# conflict; else the head differs, and the edit e fails at its first
# context, its window having no copy in the head (rc.win, rc.land); a
# failure anywhere in the list makes the whole list a conflict (rc.all,
# rc.all.of), which the crossing check keeps (rc.crossed).

import Base
import ../../bend/rebase.bend as R
import ../../spec/harness/rebase.bend as RbSpec
import ../../laws/rebase.bend as Rebase
import ./base.bend as LR
import ./rebase_refines.bend as PRebaseRefines

def rc.win(w: R.Win, +b: List<&2, Nat>, +h: List<&2, Nat>, ls: List<&2, Nat>, +i: Nat, -next: Unit -> R.Land, gone: {RbSpec.copies(h, RbSpec.lines(w)) == Nil{} : List<&2, Nat>}) -> {RbSpec.step.win(w, b, h, ls, i, next) == R.Fails{R.Moved{i}} : R.Land}:
  match w:
    case R.Win{+la, +lw, +ha, +off, +len}:
      %Equal.sym(List<&2, Nat>, RbSpec.copies(h, lw), Nil{}, gone) : {RbSpec.step(_, RbSpec.copies(b, lw), la, ha, List.length(&2, Nat, lw), List.length(&2, Nat, h), List.length(&2, Nat, b), off, len, ls, i, next) == R.Fails{R.Moved{i}} : R.Land}
      {==}

def rc.land(q: Bool, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +ls: List<&2, Nat>, +i: Nat, gone: {RbSpec.copies(h, RbSpec.lines(RbSpec.window(b, s, t, RbSpec.first.of(q)))) == Nil{} : List<&2, Nat>}) -> {RbSpec.land.go(Nat.sub(1n+RbSpec.ctx(), RbSpec.first.of(q)), b, h, s, t, ls, RbSpec.first.of(q), i) == R.Fails{R.Moved{i}} : R.Land}:
  match q:
    case True{}:
      rc.win(RbSpec.window(b, s, t, 1n), b, h, ls, i, u => RbSpec.land.go(7n, b, h, s, t, ls, 2n, i), gone)
    case False{}:
      rc.win(RbSpec.window(b, s, t, 0n), b, h, ls, i, u => RbSpec.land.go(8n, b, h, s, t, ls, 1n, i), gone)

def rc.all.of(l: R.Land, r: R.Outcome, ih: {RbSpec.is_conflict(r) == True{} : Bool}) -> {RbSpec.is_conflict(RbSpec.land_all.of(l, r)) == True{} : Bool}:
  match l:
    case R.Lands{f}:
      match r:
        case R.Rebased{fs}:
          LR.rb.absurdF({RbSpec.is_conflict(R.Rebased{f <> fs}) == True{} : Bool}, ih)
        case R.Conflict{w}:
          {==}
    case R.Fails{w}:
      {==}

def rc.all(xs: List<&2, R.Edit>, +e: R.Edit, +ys: List<&2, R.Edit>, +b: List<&2, Nat>, +h: List<&2, Nat>, +i: Nat, gone: {RbSpec.held(b, h, e) == Nil{} : List<&2, Nat>}) -> {RbSpec.is_conflict(RbSpec.land_all(List.append(&2, R.Edit, xs, e <> ys), b, h, i)) == True{} : Bool}:
  match xs:
    case Nil{}:
      match e:
        case R.Edit{+s, +t, +ls}:
          %Equal.sym(R.Land, RbSpec.land(b, h, R.Edit{s, t, ls}, i), R.Fails{R.Moved{i}}, rc.land(Nat.is_eq(s, t), b, h, s, t, ls, i, gone)) : {RbSpec.is_conflict(RbSpec.land_all.of(_, RbSpec.land_all(ys, b, h, 1n+i))) == True{} : Bool}
          {==}
    case Con{+x, +xt}:
      rc.all.of(RbSpec.land(b, h, x, i), RbSpec.land_all(List.append(&2, R.Edit, xt, e <> ys), b, h, 1n+i), rc.all(xt, e, ys, b, h, 1n+i, gone))

def rc.crossed(o: R.Outcome, +m: Nat, ih: {RbSpec.is_conflict(o) == True{} : Bool}) -> {RbSpec.is_conflict(RbSpec.crossed(o, m)) == True{} : Bool}:
  match o:
    case R.Rebased{fs}:
      LR.rb.absurdF({RbSpec.is_conflict(RbSpec.crossed(R.Rebased{fs}, m)) == True{} : Bool}, ih)
    case R.Conflict{w}:
      {==}

def rc.of(c: Maybe<&2, Nat>, +b: List<&2, Nat>, +h: List<&2, Nat>, +l: List<&2, R.Edit>, stale: {RbSpec.same(b, h) == False{} : Bool}, ih: {RbSpec.is_conflict(RbSpec.land_all(l, b, h, 0n)) == True{} : Bool}) -> {RbSpec.is_conflict(RbSpec.rebase.of(c, RbSpec.same(b, h), b, h, l)) == True{} : Bool}:
  match c:
    case Some{i}:
      {==}
    case None{}:
      %Equal.sym(Bool, RbSpec.same(b, h), False{}, stale) : {RbSpec.is_conflict(RbSpec.rebase.of(None{}, _, b, h, l)) == True{} : Bool}
      rc.crossed(RbSpec.land_all(l, b, h, 0n), List.length(&2, Nat, h), ih)

def Rebase.rebase_conflict_no_write(b, h, xs, e, ys, stale, gone):
  +l = List.append(&2, R.Edit, xs, e <> ys)
  %Equal.sym(R.Outcome, R.rebase(b, h, l), RbSpec.rebase(b, h, l), Rebase.rebase_refines(b, h, l)) : {RbSpec.is_conflict(_) == True{} : Bool}
  rc.of(RbSpec.bad(l, List.length(&2, Nat, b)), b, h, l, stale, rc.all(xs, e, ys, b, h, 0n, gone))
